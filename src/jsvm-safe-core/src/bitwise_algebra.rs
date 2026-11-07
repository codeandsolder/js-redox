//! Sound bounded bitwise-algebra recovery for proven primitive Int32 bindings.
//!
//! Arithmetic forms are integer linear combinations of bitwise expressions.
//! Each bitwise expression is a Boolean function *independently at each bit*.
//! Therefore comparing the zero vector and every single-bit assignment is a
//! complete equivalence proof for every possible combination of 32-bit inputs,
//! not a randomized equivalence test. The original JS arithmetic must also be
//! exact, and all identifier reads must be primitive and free of effects.
use crate::{fragment, numeric::exact_i64, statically_resolved_symbol};
use oxc_ast::ast::{AssignmentTarget, Expression, Statement};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::Scoping;
use oxc_span::{GetSpan, Span};
use oxc_syntax::{scope::ScopeId, symbol::SymbolId};
use std::collections::{BTreeMap, BTreeSet};

const MAX_VARIABLES: usize = 4;
const MAX_TERMS: usize = 48;
const MAX_COEFFICIENT: i64 = 64;
const MAX_CONSTANT: i64 = 1_000_000;
const MAX_ABS_VALUE: i64 = 1_i64 << 53;

#[derive(Clone)]
enum Bits {
    Variable(SymbolId),
    Constant(i32),
    Not(Box<Self>),
    And(Box<Self>, Box<Self>),
    Or(Box<Self>, Box<Self>),
    Xor(Box<Self>, Box<Self>),
}

impl Bits {
    fn evaluate(&self, values: &BTreeMap<SymbolId, i32>) -> Option<i32> {
        match self {
            Self::Variable(symbol) => values.get(symbol).copied(),
            Self::Constant(value) => Some(*value),
            Self::Not(v) => Some(!v.evaluate(values)?),
            Self::And(a, b) => Some(a.evaluate(values)? & b.evaluate(values)?),
            Self::Or(a, b) => Some(a.evaluate(values)? | b.evaluate(values)?),
            Self::Xor(a, b) => Some(a.evaluate(values)? ^ b.evaluate(values)?),
        }
    }
}

#[derive(Default)]
struct Form {
    constant: i64,
    terms: Vec<(i64, Bits)>,
    variables: BTreeSet<SymbolId>,
}

impl Form {
    fn literal(constant: i64) -> Self {
        Self {
            constant,
            ..Self::default()
        }
    }

    fn bitwise(bits: Bits, vars: BTreeSet<SymbolId>) -> Self {
        Self {
            terms: vec![(1, bits)],
            variables: vars,
            ..Self::default()
        }
    }

    fn scaled(mut self, scalar: i64) -> Option<Self> {
        self.constant = self.constant.checked_mul(scalar)?;
        for (coeff, _) in &mut self.terms {
            *coeff = coeff.checked_mul(scalar)?;
        }
        self.bounded().then_some(self)
    }

    fn combined(mut self, rhs: Self, sign: i64) -> Option<Self> {
        self.constant = self.constant.checked_add(rhs.constant.checked_mul(sign)?)?;
        self.terms
            .extend(rhs.terms.into_iter().map(|(c, b)| (c * sign, b)));
        self.variables.extend(rhs.variables);
        self.bounded().then_some(self)
    }

    fn bounded(&self) -> bool {
        self.terms.len() <= MAX_TERMS
            && self.variables.len() <= MAX_VARIABLES
            && self.constant.abs() <= MAX_CONSTANT
            && self.terms.iter().all(|(c, _)| c.abs() <= MAX_COEFFICIENT)
            && self
                .terms
                .iter()
                .map(|(c, _)| i128::from(c.abs()))
                .sum::<i128>()
                * i128::from(i32::MIN).abs()
                + i128::from(self.constant.abs())
                < i128::from(MAX_ABS_VALUE)
    }

    fn evaluate(&self, values: &BTreeMap<SymbolId, i32>) -> Option<i64> {
        let mut value = self.constant;
        for (coefficient, bits) in &self.terms {
            let term = coefficient.checked_mul(i64::from(bits.evaluate(values)?))?;
            value = value.checked_add(term)?;
        }
        Some(value)
    }
}

fn unparen<'e, 'a>(mut expr: &'e Expression<'a>) -> &'e Expression<'a> {
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    expr
}

fn integer_literal(expr: &Expression<'_>) -> Option<i64> {
    match unparen(expr) {
        Expression::NumericLiteral(number) => exact_i64(number.value),
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "-" => {
            integer_literal(&unary.argument)?.checked_neg()
        }
        _ => None,
    }
}

fn symbol_from_expression(expr: &Expression<'_>, scoping: &Scoping) -> Option<SymbolId> {
    let Expression::Identifier(id) = unparen(expr) else {
        return None;
    };
    statically_resolved_symbol(scoping, id.reference_id.get()?)
}

fn bits(
    expr: &Expression<'_>,
    scoping: &Scoping,
    primitive: &BTreeSet<SymbolId>,
    used: &mut BTreeSet<SymbolId>,
) -> Option<Bits> {
    let expr = unparen(expr);
    if let Some(symbol) = symbol_from_expression(expr, scoping) {
        if !primitive.contains(&symbol) {
            return None;
        }
        used.insert(symbol);
        return Some(Bits::Variable(symbol));
    }
    if let Some(number) = integer_literal(expr) {
        // ECMAScript ToInt32: modulo 2^32 followed by signed interpretation.
        let low = u32::try_from(number.rem_euclid(1_i64 << 32)).ok()?;
        return Some(Bits::Constant(i32::from_ne_bytes(low.to_ne_bytes())));
    }
    match expr {
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "~" => Some(Bits::Not(
            Box::new(bits(&unary.argument, scoping, primitive, used)?),
        )),
        Expression::BinaryExpression(binary) => {
            let left = bits(&binary.left, scoping, primitive, used)?;
            let right = bits(&binary.right, scoping, primitive, used)?;
            match binary.operator.as_str() {
                "&" => Some(Bits::And(Box::new(left), Box::new(right))),
                "|" => Some(Bits::Or(Box::new(left), Box::new(right))),
                "^" => Some(Bits::Xor(Box::new(left), Box::new(right))),
                _ => None,
            }
        }
        _ => None,
    }
}

fn form(expr: &Expression<'_>, scoping: &Scoping, primitive: &BTreeSet<SymbolId>) -> Option<Form> {
    let expr = unparen(expr);
    if let Expression::BinaryExpression(binary) = expr {
        match binary.operator.as_str() {
            "+" => {
                return form(&binary.left, scoping, primitive)?
                    .combined(form(&binary.right, scoping, primitive)?, 1)
            }
            "-" => {
                return form(&binary.left, scoping, primitive)?
                    .combined(form(&binary.right, scoping, primitive)?, -1)
            }
            "*" => {
                if let Some(scalar) = integer_literal(&binary.left) {
                    return form(&binary.right, scoping, primitive)?.scaled(scalar);
                }
                if let Some(scalar) = integer_literal(&binary.right) {
                    return form(&binary.left, scoping, primitive)?.scaled(scalar);
                }
                return None;
            }
            _ => {}
        }
    }
    if let Expression::UnaryExpression(unary) = expr {
        if unary.operator.as_str() == "-" {
            return form(&unary.argument, scoping, primitive)?.scaled(-1);
        }
    }
    if let Some(number) = integer_literal(expr) {
        return Form::literal(number)
            .bounded()
            .then(|| Form::literal(number));
    }
    let mut used = BTreeSet::new();
    let bitexpr = bits(expr, scoping, primitive, &mut used)?;
    let result = Form::bitwise(bitexpr, used);
    result.bounded().then_some(result)
}

// A linear combination of per-bit Boolean functions has no cross-bit terms.
// Hence the following is an *exhaustive proof*, even for 4 * 32 input bits:
// equality at all-zero and at all 2^k assignments of each individual bit
// implies equality at arbitrary simultaneous assignments on all 32 bits.
fn equivalent(form: &Form, candidate: &Bits, variables: &[SymbolId]) -> bool {
    let mut values = BTreeMap::new();
    for &symbol in variables {
        values.insert(symbol, 0);
    }
    if form.evaluate(&values) != candidate.evaluate(&values).map(i64::from) {
        return false;
    }
    for bit in 0..32 {
        for selector in 1..(1usize << variables.len()) {
            for (index, &symbol) in variables.iter().enumerate() {
                values.insert(
                    symbol,
                    if (selector & (1 << index)) != 0 {
                        i32::from_ne_bytes((1u32 << bit).to_ne_bytes())
                    } else {
                        0
                    },
                );
            }
            if form.evaluate(&values) != candidate.evaluate(&values).map(i64::from) {
                return false;
            }
        }
    }
    true
}

/// Bitwise operators always return a primitive Number with positive zero.
/// Arithmetic can create *negative* zero despite having the same mathematical
/// integer value; prove the entire expression cannot return -0 before replacing
/// it by a bitwise candidate. In particular, `-0`, `-x`, and `-2 * x` cannot
/// be discarded merely because integer algebra says they are zero.
fn cannot_be_negative_zero(
    expr: &Expression<'_>,
    primitive: &BTreeSet<SymbolId>,
    scoping: &Scoping,
) -> bool {
    match unparen(expr) {
        Expression::Identifier(_) => {
            symbol_from_expression(expr, scoping).is_some_and(|symbol| primitive.contains(&symbol))
        }
        Expression::NumericLiteral(number) => {
            number.value != 0.0 || !number.value.is_sign_negative()
        }
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "~" => true,
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "-" => {
            integer_literal(&unary.argument).is_some_and(|number| number != 0)
        }
        Expression::BinaryExpression(binary) => match binary.operator.as_str() {
            "&" | "|" | "^" | "<<" | ">>" | ">>>" => true,
            "+" => {
                cannot_be_negative_zero(&binary.left, primitive, scoping)
                    || cannot_be_negative_zero(&binary.right, primitive, scoping)
            }
            "-" => cannot_be_negative_zero(&binary.left, primitive, scoping),
            "*" => {
                if let Some(scalar) = integer_literal(&binary.left) {
                    scalar > 0 && cannot_be_negative_zero(&binary.right, primitive, scoping)
                } else if let Some(scalar) = integer_literal(&binary.right) {
                    scalar > 0 && cannot_be_negative_zero(&binary.left, primitive, scoping)
                } else {
                    false
                }
            }
            _ => false,
        },
        _ => false,
    }
}

fn simplify(
    expr: &Expression<'_>,
    source: &str,
    scoping: &Scoping,
    primitive: &BTreeSet<SymbolId>,
) -> Option<String> {
    if !cannot_be_negative_zero(expr, primitive, scoping) {
        return None;
    }
    let value = form(expr, scoping, primitive)?;
    if value.variables.is_empty() {
        return None;
    }
    let variables = value.variables.iter().copied().collect::<Vec<_>>();
    let names = variables
        .iter()
        .map(|&symbol| scoping.symbol_name(symbol).to_string())
        .collect::<Vec<_>>();
    let initial_size = fragment(source, expr.span()).len();
    let mut alternatives = Vec::<(String, Bits)>::new();
    for (index, &symbol) in variables.iter().enumerate() {
        alternatives.push((names[index].clone(), Bits::Variable(symbol)));
        alternatives.push((
            format!("~{}", names[index]),
            Bits::Not(Box::new(Bits::Variable(symbol))),
        ));
    }
    for i in 0..variables.len() {
        for j in i + 1..variables.len() {
            let a = Bits::Variable(variables[i]);
            let b = Bits::Variable(variables[j]);
            let na = &names[i];
            let nb = &names[j];
            for (op, bit_expr) in [
                ("|", Bits::Or(Box::new(a.clone()), Box::new(b.clone()))),
                ("&", Bits::And(Box::new(a.clone()), Box::new(b.clone()))),
                ("^", Bits::Xor(Box::new(a.clone()), Box::new(b.clone()))),
            ] {
                alternatives.push((format!("{na} {op} {nb}"), bit_expr));
            }
            for (op, inner) in [
                ("|", Bits::Or(Box::new(a.clone()), Box::new(b.clone()))),
                ("&", Bits::And(Box::new(a.clone()), Box::new(b.clone()))),
                ("^", Bits::Xor(Box::new(a.clone()), Box::new(b.clone()))),
            ] {
                alternatives.push((format!("~({na} {op} {nb})"), Bits::Not(Box::new(inner))));
            }
        }
    }
    alternatives.sort_unstable_by_key(|(text, _)| text.len());
    alternatives.into_iter().find_map(|(text, candidate)| {
        (text.len() < initial_size && equivalent(&value, &candidate, &variables)).then_some(text)
    })
}

fn symbol_safe(scoping: &Scoping, symbol: SymbolId) -> bool {
    let binding_scope = scoping.symbol_scope_id(symbol);
    scoping
        .get_resolved_reference_ids(symbol)
        .iter()
        .all(|reference_id| {
            let reference = scoping.get_reference(*reference_id);
            let mut scope: ScopeId = reference.scope_id();
            loop {
                if scope == binding_scope {
                    return true;
                }
                if scoping.scope_flags(scope).is_function() {
                    return false;
                }
                let Some(parent) = scoping.scope_parent_id(scope) else {
                    return false;
                };
                scope = parent;
            }
        })
}

fn root_assignment<'e, 'a>(
    expr: &'e Expression<'a>,
    scoping: &Scoping,
) -> Option<(SymbolId, &'e Expression<'a>)> {
    let Expression::AssignmentExpression(assign) = unparen(expr) else {
        return None;
    };
    if assign.operator.as_str() != "=" {
        return None;
    }
    let AssignmentTarget::AssignmentTargetIdentifier(id) = &assign.left else {
        return None;
    };
    let symbol = statically_resolved_symbol(scoping, id.reference_id.get()?)?;
    Some((symbol, &assign.right))
}

/// Bitwise operators can return BigInt when both operands are BigInt.
/// Only mark a result as primitive Int32 if at least one operand is proven
/// Number: on the successful path the other operand must have been coerced to
/// Number as well (otherwise JavaScript throws before the assignment).
fn proven_number(expr: &Expression<'_>, scoping: &Scoping, numeric: &BTreeSet<SymbolId>) -> bool {
    match unparen(expr) {
        Expression::NumericLiteral(_) => true,
        Expression::Identifier(_) => {
            symbol_from_expression(expr, scoping).is_some_and(|symbol| numeric.contains(&symbol))
        }
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "-" => {
            proven_number(&unary.argument, scoping, numeric)
        }
        Expression::BinaryExpression(binary)
            if matches!(
                binary.operator.as_str(),
                "&" | "|" | "^" | "<<" | ">>" | ">>>"
            ) =>
        {
            binary.operator.as_str() == ">>>"
                || proven_number(&binary.left, scoping, numeric)
                || proven_number(&binary.right, scoping, numeric)
        }
        _ => false,
    }
}

fn is_int32(expr: &Expression<'_>, scoping: &Scoping, numeric: &BTreeSet<SymbolId>) -> bool {
    match unparen(expr) {
        Expression::BinaryExpression(binary)
            if matches!(binary.operator.as_str(), "&" | "|" | "^" | "<<" | ">>") =>
        {
            proven_number(&binary.left, scoping, numeric)
                || proven_number(&binary.right, scoping, numeric)
        }
        Expression::UnaryExpression(unary) if unary.operator.as_str() == "~" => {
            proven_number(&unary.argument, scoping, numeric)
        }
        Expression::NumericLiteral(number) => {
            exact_i64(number.value).is_some_and(|i| i32::try_from(i).is_ok())
        }
        _ => false,
    }
}

#[derive(Default)]
struct NestedWrites(bool);

impl<'a> Visit<'a> for NestedWrites {
    fn visit_assignment_expression(&mut self, it: &oxc_ast::ast::AssignmentExpression<'a>) {
        self.0 = true;
        walk::walk_assignment_expression(self, it);
    }

    fn visit_update_expression(&mut self, it: &oxc_ast::ast::UpdateExpression<'a>) {
        self.0 = true;
        walk::walk_update_expression(self, it);
    }
}

fn has_nested_writes(expr: &Expression<'_>) -> bool {
    let mut visitor = NestedWrites::default();
    visitor.visit_expression(expr);
    visitor.0
}

/// Visit a straight-line statement list. Facts are invalidated at every
/// control-flow or unmodelled statement boundary. This deliberately does not
/// infer branch convergence, loop invariants, aliasing, or interprocedural state.
pub(super) fn scan(
    statements: &[Statement<'_>],
    source: &str,
    scoping: &Scoping,
) -> Vec<(Span, String)> {
    let mut numeric = BTreeSet::<SymbolId>::new();
    let mut replacements = Vec::new();
    for stmt in statements {
        let Statement::ExpressionStatement(expr_stmt) = stmt else {
            numeric.clear();
            continue;
        };
        let Some((target, rhs)) = root_assignment(&expr_stmt.expression, scoping) else {
            numeric.clear();
            continue;
        };
        if !symbol_safe(scoping, target) {
            numeric.clear();
            continue;
        }
        if has_nested_writes(rhs) {
            // A nested assignment or increment could invalidate *any*
            // previously established primitive binding before the next
            // statement. Never infer dependencies through such expressions.
            numeric.clear();
        }
        if let Some(rewrite) = simplify(rhs, source, scoping, &numeric) {
            replacements.push((rhs.span(), rewrite));
        }
        let proven_int32 = is_int32(rhs, scoping, &numeric);
        numeric.remove(&target);
        if proven_int32 {
            numeric.insert(target);
        }
    }
    replacements
}

#[cfg(test)]
mod tests {
    use crate::deobfuscate;
    use work_budget::{BudgetExceeded, WorkBudget};

    fn recover(source: &str) -> Result<(String, usize), BudgetExceeded> {
        let result = deobfuscate(source, 16, &WorkBudget::unlimited("bitwise-algebra"))?;
        assert!(result.is_some(), "valid source must be accepted");
        let Some(result) = result else {
            unreachable!("valid source");
        };
        let count = result
            .transforms
            .get("bitwise_algebra")
            .copied()
            .unwrap_or(0);
        Ok((result.source, count))
    }

    #[test]
    fn reconstructs_integer_byte_composition_without_matching_names_or_masks(
    ) -> Result<(), BudgetExceeded> {
        for (head, a, b) in [
            ("function f(x,y,A,B,C){", "A", "B"),
            ("function f(x,y,lower,upper,C){", "lower", "upper"),
        ] {
            let source = format!("{head} if(x) {{{a}=y&127; {b}=get() << 7; C=~{a}-2*~({a}|{b})+({a}|~{b});}} return C; }}");
            let (output, count) = recover(&source)?;
            assert!(count >= 1, "{output}");
            assert!(output.contains(&format!("{a} | {b}")), "{output}");
        }
        Ok(())
    }

    #[test]
    fn proves_general_or_xor_and_demorgan_bitwise_equivalences() -> Result<(), BudgetExceeded> {
        let source = "function f(x,y,a,b,c){a=x|0;b=y|0;c=(a+b)-(a&b);return c;}";
        let (output, count) = recover(source)?;
        assert!(count >= 1, "{output}");
        assert!(output.contains("a | b"), "{output}");
        let source = "function f(x,y,a,b,c){a=x|0;b=y|0;c=~(a&b);return c;}";
        let (output, _) = recover(source)?;
        assert!(
            output.contains("~(a&b)"),
            "no need to make already concise source longer: {output}"
        );
        Ok(())
    }

    #[test]
    fn does_not_replace_untyped_object_coercions_or_unsafe_cross_block_facts(
    ) -> Result<(), BudgetExceeded> {
        for source in [
            "function f(a,b,c){c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(a,b,c,x){a=x&127; mutate(); b=x<<7;c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(a,b,c,x){a=x&127; if(x){b=x<<7;} c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(a,b,c,x){a=x&127;b=(a={},x)<<7;c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(a,b,c,x){let change=()=>{a={};};a=x&127;b=(change(),x)<<7;c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(a,b,c,x){a=x&127; b=x<<7; eval('a=42');c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(x,y,a,b,c){a=x&y;b=y&x;c=~a-2*~(a|b)+(a|~b);return c;}",
            "function f(x,y,a,b,c){a=~x;b=~y;c=~a-2*~(a|b)+(a|~b);return c;}",
        ] {
            let (output, count) = recover(source)?;
            assert_eq!(count, 0, "unexpected rewrite: {source} => {output}");
        }
        Ok(())
    }
}
