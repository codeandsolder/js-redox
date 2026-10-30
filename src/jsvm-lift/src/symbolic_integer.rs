use crate::numeric::{eval_js_bitwise_i64, exact_i64, js_int32_from_i64};
use oxc_ast::ast::{AssignmentTarget, Expression};
use oxc_semantic::Scoping;
use oxc_span::GetSpan;
use oxc_syntax::symbol::SymbolId;
use std::collections::{BTreeMap, HashMap, HashSet};

const MAX_TERMS: usize = 256;
const MAX_DEGREE: usize = 8;

type Monomial = Vec<SymbolId>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegerPolynomial {
    terms: BTreeMap<Monomial, i128>,
}

impl IntegerPolynomial {
    #[must_use]
    pub fn constant(value: i128) -> Self {
        let mut terms = BTreeMap::new();
        if value != 0 {
            terms.insert(Vec::new(), value);
        }
        Self { terms }
    }

    #[must_use]
    pub fn variable(symbol: SymbolId) -> Self {
        Self {
            terms: BTreeMap::from([(vec![symbol], 1)]),
        }
    }

    #[must_use]
    pub fn constant_value(&self) -> Option<i128> {
        if self.terms.is_empty() {
            return Some(0);
        }
        if self.terms.len() == 1 {
            let (monomial, value) = self.terms.first_key_value()?;
            if monomial.is_empty() {
                return Some(*value);
            }
        }
        None
    }

    /// Return the distinct symbol-resolved variables participating in this
    /// polynomial, sorted by `SymbolId` for stable proof comparisons.
    #[must_use]
    pub fn variables(&self) -> Vec<SymbolId> {
        let mut variables = self
            .terms
            .keys()
            .flat_map(|monomial| monomial.iter().copied())
            .collect::<Vec<_>>();
        variables.sort_unstable();
        variables.dedup();
        variables
    }

    fn negated(&self) -> Option<Self> {
        let mut terms = BTreeMap::new();
        for (monomial, coefficient) in &self.terms {
            terms.insert(monomial.clone(), coefficient.checked_neg()?);
        }
        Some(Self { terms })
    }

    fn add(&self, rhs: &Self) -> Option<Self> {
        let mut terms = self.terms.clone();
        for (monomial, coefficient) in &rhs.terms {
            let next = terms
                .get(monomial)
                .copied()
                .unwrap_or(0)
                .checked_add(*coefficient)?;
            if next == 0 {
                terms.remove(monomial);
            } else {
                terms.insert(monomial.clone(), next);
            }
        }
        (terms.len() <= MAX_TERMS).then_some(Self { terms })
    }

    fn sub(&self, rhs: &Self) -> Option<Self> {
        self.add(&rhs.negated()?)
    }

    fn mul(&self, rhs: &Self) -> Option<Self> {
        let mut terms = BTreeMap::<Monomial, i128>::new();
        for (left_vars, left_coefficient) in &self.terms {
            for (right_vars, right_coefficient) in &rhs.terms {
                let mut monomial = left_vars.clone();
                monomial.extend(right_vars.iter().copied());
                monomial.sort_unstable();
                if monomial.len() > MAX_DEGREE {
                    return None;
                }
                let product = left_coefficient.checked_mul(*right_coefficient)?;
                let next = terms
                    .get(&monomial)
                    .copied()
                    .unwrap_or(0)
                    .checked_add(product)?;
                if next == 0 {
                    terms.remove(&monomial);
                } else {
                    terms.insert(monomial, next);
                }
                if terms.len() > MAX_TERMS {
                    return None;
                }
            }
        }
        Some(Self { terms })
    }
}

fn reference_symbol(scoping: &Scoping, expression: &Expression<'_>) -> Option<SymbolId> {
    let Expression::Identifier(identifier) = expression else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

fn assignment_symbol(scoping: &Scoping, target: &AssignmentTarget<'_>) -> Option<SymbolId> {
    let AssignmentTarget::AssignmentTargetIdentifier(identifier) = target else {
        return None;
    };
    scoping
        .get_reference(identifier.reference_id.get()?)
        .symbol_id()
}

struct Normalizer<'s, 'b, 'c, 'a> {
    scoping: &'s Scoping,
    bindings: HashMap<SymbolId, IntegerPolynomial>,
    opaque_constants: &'c HashMap<(u32, u32), i128>,
    arbitrary_assignments: &'a HashSet<SymbolId>,
    _marker: std::marker::PhantomData<&'b ()>,
}

impl Normalizer<'_, '_, '_, '_> {
    fn normalize(&mut self, expression: &Expression<'_>) -> Option<IntegerPolynomial> {
        let span = expression.span();
        if let Some(value) = self.opaque_constants.get(&(span.start, span.end)) {
            return Some(IntegerPolynomial::constant(*value));
        }
        match expression {
            Expression::NumericLiteral(number) => Some(IntegerPolynomial::constant(i128::from(
                exact_i64(number.value)?,
            ))),
            Expression::Identifier(_) => {
                let symbol = reference_symbol(self.scoping, expression)?;
                Some(
                    self.bindings
                        .get(&symbol)
                        .cloned()
                        .unwrap_or_else(|| IntegerPolynomial::variable(symbol)),
                )
            }
            Expression::ParenthesizedExpression(parenthesized) => {
                self.normalize(&parenthesized.expression)
            }
            Expression::UnaryExpression(unary) => {
                let argument = self.normalize(&unary.argument)?;
                match unary.operator.as_str() {
                    "+" => Some(argument),
                    "-" => argument.negated(),
                    "~" => {
                        let value = i64::try_from(argument.constant_value()?).ok()?;
                        Some(IntegerPolynomial::constant(i128::from(!js_int32_from_i64(
                            value,
                        ))))
                    }
                    _ => None,
                }
            }
            Expression::BinaryExpression(binary) => {
                let left = self.normalize(&binary.left)?;
                let right = self.normalize(&binary.right)?;
                match binary.operator.as_str() {
                    "+" => left.add(&right),
                    "-" => left.sub(&right),
                    "*" => left.mul(&right),
                    "&" | "|" | "^" | "<<" | ">>" | ">>>" => {
                        let left = i64::try_from(left.constant_value()?).ok()?;
                        let right = i64::try_from(right.constant_value()?).ok()?;
                        Some(IntegerPolynomial::constant(i128::from(
                            eval_js_bitwise_i64(binary.operator.as_str(), left, right)?,
                        )))
                    }
                    "%" => {
                        let left = left.constant_value()?;
                        let right = right.constant_value()?;
                        (right != 0).then(|| IntegerPolynomial::constant(left % right))
                    }
                    _ => None,
                }
            }
            Expression::SequenceExpression(sequence) => {
                let mut last = None;
                for expression in &sequence.expressions {
                    last = Some(self.normalize(expression)?);
                }
                last
            }
            Expression::AssignmentExpression(assignment) if assignment.operator.is_assign() => {
                let symbol = assignment_symbol(self.scoping, &assignment.left)?;
                let value = match self.normalize(&assignment.right) {
                    Some(value) => value,
                    None if self.arbitrary_assignments.contains(&symbol) => {
                        IntegerPolynomial::variable(symbol)
                    }
                    None => return None,
                };
                self.bindings.insert(symbol, value.clone());
                Some(value)
            }
            _ => None,
        }
    }
}

/// Normalize a supported integer expression into a canonical polynomial over
/// symbol-resolved variables. `opaque_constants` can discharge independently
/// proven calls/member reads by exact source span. Assignments whose RHS is
/// intentionally unconstrained may be listed in `arbitrary_assignments`; their
/// post-assignment value becomes a fresh symbolic value of that variable.
#[must_use]
pub fn normalize_integer_polynomial(
    expression: &Expression<'_>,
    scoping: &Scoping,
    bindings: &HashMap<SymbolId, IntegerPolynomial>,
    opaque_constants: &HashMap<(u32, u32), i128>,
    arbitrary_assignments: &HashSet<SymbolId>,
) -> Option<IntegerPolynomial> {
    Normalizer {
        scoping,
        bindings: bindings.clone(),
        opaque_constants,
        arbitrary_assignments,
        _marker: std::marker::PhantomData,
    }
    .normalize(expression)
}

#[cfg(test)]
mod tests {
    use super::{normalize_integer_polynomial, IntegerPolynomial};
    use oxc_allocator::Allocator;
    use oxc_ast::{ast::Statement, AstKind};
    use oxc_ast_visit::Visit;
    use oxc_semantic::SemanticBuilder;
    use oxc_span::{GetSpan, SourceType};
    use oxc_syntax::symbol::SymbolId;
    use rolldown_redox::ecmascript::parse_program;
    use std::collections::{HashMap, HashSet};

    struct Probe {
        calls: Vec<(u32, u32)>,
        members: Vec<(u32, u32)>,
        symbols: HashMap<String, SymbolId>,
    }

    impl<'a> Visit<'a> for Probe {
        fn enter_node(&mut self, kind: AstKind<'a>) {
            match kind {
                AstKind::CallExpression(call) => {
                    let span = call.span();
                    self.calls.push((span.start, span.end));
                }
                AstKind::ComputedMemberExpression(member) => {
                    let span = member.span();
                    self.members.push((span.start, span.end));
                }
                AstKind::BindingIdentifier(identifier) => {
                    if let Some(symbol) = identifier.symbol_id.get() {
                        self.symbols.insert(identifier.name.to_string(), symbol);
                    }
                }
                _ => {}
            }
        }
    }

    #[test]
    fn reduces_selector_polynomial_to_captured_slot() {
        let source = r#"
            function f(v, T, H, q, U) {
                return 6 + (q() | 0) * T - T * H + 61 * H * H
                    - 305 * v * v * H + U[1] * v * T + 5 * v * v * T
                    + 2379 * v * H - 1403 * H;
            }
        "#;
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let semantic = SemanticBuilder::new().build(&parsed.program);
        assert!(semantic.diagnostics.is_empty());
        let mut probe = Probe {
            calls: Vec::new(),
            members: Vec::new(),
            symbols: HashMap::new(),
        };
        probe.visit_program(&parsed.program);
        let v = probe.symbols["v"];
        let h = probe.symbols["H"];
        let v_poly = IntegerPolynomial::variable(v);
        let h_poly = IntegerPolynomial::constant(5)
            .mul(&v_poly)
            .and_then(|p| p.mul(&v_poly))
            .and_then(|p| p.sub(&IntegerPolynomial::constant(39).mul(&v_poly)?))
            .and_then(|p| p.add(&IntegerPolynomial::constant(23)))
            .expect("seed polynomial");
        let bindings = HashMap::from([(h, h_poly)]);
        let mut constants = HashMap::new();
        constants.insert(probe.calls[0], 23);
        constants.insert(probe.members[0], -39);
        let Statement::FunctionDeclaration(function) = &parsed.program.body[0] else {
            panic!("function declaration");
        };
        let body = function.body.as_ref().expect("function body");
        let Statement::ReturnStatement(ret) = &body.statements[0] else {
            panic!("return statement");
        };
        let polynomial = normalize_integer_polynomial(
            ret.argument.as_ref().expect("return expression"),
            semantic.semantic.scoping(),
            &bindings,
            &constants,
            &HashSet::new(),
        )
        .expect("supported polynomial");
        assert_eq!(polynomial.constant_value(), Some(6));
    }
}
