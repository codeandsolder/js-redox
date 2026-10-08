use anyhow::{anyhow, Context, Result};
use clap::Parser as ClapParser;
use jsvm_lift::numeric::{eval_js_bitwise_i64, exact_i64, js_int32_from_i64};
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{Argument, AssignmentExpression, AssignmentTarget, Expression, Statement, SwitchCase},
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_span::{GetSpan, SourceType, Span};
use rolldown_redox::ecmascript::parse_program;
use serde::{Deserialize, Serialize};
use serde_json::Value as JsonValue;
use std::{
    collections::{BTreeMap, HashMap, HashSet, VecDeque},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Statically reduce linked JavaScript VM handler state machines")]
struct Args {
    jsonl: PathBuf,
    #[arg(long)]
    function_id: Option<String>,
}

#[derive(Debug, Deserialize)]
struct ScanReport {
    file: String,
    functions: Vec<FunctionMetric>,
    state_machines: Vec<StateMachine>,
    decoder_candidates: Vec<DecoderCandidate>,
    push_builders: Vec<PushBuilder>,
}

#[derive(Debug, Deserialize)]
struct FunctionMetric {
    id: String,
    start: u32,
    end: u32,
}

#[derive(Debug, Clone, Deserialize, Serialize)]
struct StateMachine {
    function_id: String,
    start: u32,
    end: u32,
    state_var: String,
    init_state: u64,
    mask: u64,
    shift: Option<u64>,
    selector_var: Option<String>,
    switch_cases: usize,
    preview: String,
}

#[derive(Debug, Clone, Deserialize)]
struct DecoderCandidate {
    function_id: String,
    object: String,
    builder_var: Option<String>,
    builder_start: Option<u32>,
    base: Option<String>,
    ip: String,
    width: u64,
    selector_var: Option<String>,
}

#[derive(Debug, Deserialize)]
struct PushBuilder {
    start: u32,
    values: Vec<Option<u64>>,
}

#[derive(Clone, Debug, PartialEq)]
enum Val {
    Num(i64),
    Bool(bool),
    Undefined,
    Sym(String),
    Unknown,
    Fork(Vec<ForkChoice>),
}

#[derive(Clone, Debug, PartialEq)]
struct ForkChoice {
    guard: String,
    value: i64,
}

impl Val {
    fn as_num(&self) -> Option<i64> {
        match self {
            Self::Num(v) => Some(*v),
            Self::Bool(v) => Some(i64::from(*v)),
            _ => None,
        }
    }

    const fn truthy(&self) -> Option<bool> {
        match self {
            Self::Num(v) => Some(*v != 0),
            Self::Bool(v) => Some(*v),
            Self::Undefined => Some(false),
            Self::Sym(_) | Self::Unknown | Self::Fork(_) => None,
        }
    }
}

type Env = HashMap<String, Val>;

#[derive(Clone, Debug)]
struct EvalCtx<'a> {
    source: &'a str,
    decoder: Option<&'a DecoderCandidate>,
    opcode: i64,
    state_var: Option<&'a str>,
    structural: HashSet<String>,
}

#[derive(Debug)]
enum Exec {
    Continue,
    Stop(&'static str),
    Fork(Vec<ForkChoice>),
}

#[derive(Clone, Debug)]
struct PathState {
    env: Env,
    effects: Vec<String>,
    states: Vec<u64>,
    guards: Vec<String>,
    iterations: usize,
    terminal: Option<String>,
}

#[derive(Debug, Serialize)]
struct ReducedVm {
    file: String,
    decoder: String,
    parent: String,
    state_machine: StateMachine,
    opcodes: Vec<ReducedOpcode>,
}

#[derive(Debug, Serialize)]
struct ReducedOpcode {
    opcode: u64,
    derived_env: BTreeMap<String, JsonValue>,
    paths: Vec<ReducedPath>,
    #[serde(skip_serializing_if = "Option::is_none")]
    states: Option<Vec<u64>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    effects: Option<Vec<String>>,
}

#[derive(Debug, Serialize)]
struct ReducedPath {
    guards: Vec<String>,
    states: Vec<u64>,
    effects: Vec<String>,
    terminal: Option<String>,
}

fn source_fragment(source: &str, span: Span) -> String {
    let start = span.start as usize;
    let end = (span.end as usize).min(source.len());
    source
        .get(start..end)
        .unwrap_or_default()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn expr_ident(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::Identifier(id) => Some(id.name.to_string()),
        Expression::ParenthesizedExpression(p) => expr_ident(&p.expression),
        _ => None,
    }
}

fn target_ident(target: &AssignmentTarget<'_>) -> Option<String> {
    match target {
        AssignmentTarget::AssignmentTargetIdentifier(id) => Some(id.name.to_string()),
        _ => None,
    }
}

fn num_literal(expr: &Expression<'_>) -> Option<i64> {
    match expr {
        Expression::NumericLiteral(n) => exact_i64(n.value),
        Expression::ParenthesizedExpression(p) => num_literal(&p.expression),
        _ => None,
    }
}

fn parse_fn_id(id: &str) -> Result<(u32, u32)> {
    let raw = id
        .strip_prefix("fn@")
        .ok_or_else(|| anyhow!("bad function id {id}"))?;
    let (a, b) = raw
        .split_once('-')
        .ok_or_else(|| anyhow!("bad function id {id}"))?;
    Ok((u32::from_str_radix(a, 16)?, u32::from_str_radix(b, 16)?))
}

fn computed_decoder_value(
    expr: &oxc_ast::ast::ComputedMemberExpression<'_>,
    env: &mut Env,
    dec: &DecoderCandidate,
    opcode: i64,
) -> Val {
    if expr_ident(&expr.object).as_deref() != Some(dec.object.as_str()) {
        return Val::Unknown;
    }
    let Ok(width) = i64::try_from(dec.width) else {
        return Val::Unknown;
    };

    if let Expression::AssignmentExpression(assign) = &expr.expression {
        if assign.operator.is_assign() {
            if let (Some(base), Some(expected_base)) =
                (target_ident(&assign.left), dec.base.as_ref())
            {
                if &base == expected_base {
                    if let Expression::BinaryExpression(bin) = &assign.right {
                        if bin.operator.as_str() == "*" {
                            let left_num = num_literal(&bin.left);
                            let right_num = num_literal(&bin.right);
                            let left_id = expr_ident(&bin.left);
                            let right_id = expr_ident(&bin.right);
                            let matched = (left_num == Some(width)
                                && right_id.as_deref() == Some(dec.ip.as_str()))
                                || (right_num == Some(width)
                                    && left_id.as_deref() == Some(dec.ip.as_str()));
                            if matched {
                                env.insert(base, Val::Sym("pc".into()));
                                return Val::Num(opcode);
                            }
                        }
                    }
                }
            }
        }
    }

    if let Expression::BinaryExpression(bin) = &expr.expression {
        if bin.operator.as_str() == "+" {
            if let Some(base) = dec.base.as_ref() {
                let offset = if expr_ident(&bin.left).as_deref() == Some(base.as_str()) {
                    num_literal(&bin.right)
                } else if expr_ident(&bin.right).as_deref() == Some(base.as_str()) {
                    num_literal(&bin.left)
                } else {
                    None
                };
                if let Some(off) = offset {
                    if off > 0 && off < width {
                        return Val::Sym(format!("operand{off}"));
                    }
                }
            }
        }
    }

    if dec.base.is_none() {
        if let Expression::BinaryExpression(bin) = &expr.expression {
            if bin.operator.as_str() == "*" {
                let matched = (num_literal(&bin.left) == Some(width)
                    && expr_ident(&bin.right).as_deref() == Some(dec.ip.as_str()))
                    || (num_literal(&bin.right) == Some(width)
                        && expr_ident(&bin.left).as_deref() == Some(dec.ip.as_str()));
                if matched {
                    return Val::Num(opcode);
                }
            }
        }
    }

    Val::Unknown
}

fn eval_unary(
    un: &oxc_ast::ast::UnaryExpression<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Val {
    let v = eval_expr(&un.argument, env, effects, ctx);
    match un.operator.as_str() {
        "void" => Val::Undefined,
        "!" => v.truthy().map_or(Val::Unknown, |x| Val::Bool(!x)),
        "~" => v
            .as_num()
            .map_or(Val::Unknown, |x| Val::Num(i64::from(!js_int32_from_i64(x)))),
        "+" => v.as_num().map_or(Val::Unknown, Val::Num),
        "-" => v.as_num().map_or(Val::Unknown, |x| Val::Num(-x)),
        _ => Val::Unknown,
    }
}

fn eval_logical(
    log: &oxc_ast::ast::LogicalExpression<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Val {
    let left = eval_expr(&log.left, env, effects, ctx);
    let Some(truth) = left.truthy() else {
        return Val::Unknown;
    };
    match log.operator.as_str() {
        "&&" => {
            if truth {
                eval_expr(&log.right, env, effects, ctx)
            } else {
                left
            }
        }
        "||" => {
            if truth {
                left
            } else {
                eval_expr(&log.right, env, effects, ctx)
            }
        }
        _ => Val::Unknown,
    }
}

fn eval_binary(
    bin: &oxc_ast::ast::BinaryExpression<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Val {
    let l = eval_expr(&bin.left, env, effects, ctx);
    let r = eval_expr(&bin.right, env, effects, ctx);
    let (Some(a), Some(b)) = (l.as_num(), r.as_num()) else {
        return Val::Unknown;
    };
    match bin.operator.as_str() {
        "==" | "===" => Val::Bool(a == b),
        "!=" | "!==" => Val::Bool(a != b),
        "<" => Val::Bool(a < b),
        "<=" => Val::Bool(a <= b),
        ">" => Val::Bool(a > b),
        ">=" => Val::Bool(a >= b),
        "&" | "|" | "^" | "<<" | ">>" | ">>>" => {
            eval_js_bitwise_i64(bin.operator.as_str(), a, b).map_or(Val::Unknown, Val::Num)
        }
        "+" => Val::Num(a.wrapping_add(b)),
        "-" => Val::Num(a.wrapping_sub(b)),
        "*" => Val::Num(a.wrapping_mul(b)),
        "/" if b != 0 => Val::Num(a / b),
        "%" if b != 0 => Val::Num(a % b),
        _ => Val::Unknown,
    }
}

fn eval_assignment(
    assign: &AssignmentExpression<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Val {
    let Some(name) = target_ident(&assign.left) else {
        effects.push(source_fragment(ctx.source, assign.span));
        return Val::Unknown;
    };

    if ctx.state_var == Some(name.as_str())
        && assign.operator.is_assign()
        && matches!(&assign.right, Expression::ConditionalExpression(_))
    {
        if let Expression::ConditionalExpression(cond) = &assign.right {
            let test = eval_expr(&cond.test, env, effects, ctx);
            if test.truthy().is_none() {
                let mut yes_env = env.clone();
                let mut no_env = env.clone();
                let mut sink = Vec::new();
                let yes = eval_expr(&cond.consequent, &mut yes_env, &mut sink, ctx);
                let no = eval_expr(&cond.alternate, &mut no_env, &mut sink, ctx);
                if let (Some(y), Some(n)) = (yes.as_num(), no.as_num()) {
                    let guard = source_fragment(ctx.source, cond.test.span());
                    return Val::Fork(vec![
                        ForkChoice {
                            guard: guard.clone(),
                            value: y,
                        },
                        ForkChoice {
                            guard: format!("!({guard})"),
                            value: n,
                        },
                    ]);
                }
            }
        }
    }

    let rhs = eval_expr(&assign.right, env, effects, ctx);
    if matches!(rhs, Val::Fork(_)) {
        return rhs;
    }
    match assign.operator.as_str() {
        "=" if rhs != Val::Unknown => {
            env.insert(name.clone(), rhs.clone());
            if !ctx.structural.contains(&name) {
                effects.push(source_fragment(ctx.source, assign.span));
            }
            rhs
        }
        "+=" => {
            let old = env.get(&name).and_then(Val::as_num);
            let value = rhs.as_num();
            if let (Some(a), Some(b)) = (old, value) {
                let out = Val::Num(a.wrapping_add(b));
                env.insert(name.clone(), out.clone());
                if !ctx.structural.contains(&name) {
                    effects.push(source_fragment(ctx.source, assign.span));
                }
                out
            } else {
                effects.push(source_fragment(ctx.source, assign.span));
                Val::Unknown
            }
        }
        "-=" => {
            let old = env.get(&name).and_then(Val::as_num);
            let value = rhs.as_num();
            if let (Some(a), Some(b)) = (old, value) {
                let out = Val::Num(a.wrapping_sub(b));
                env.insert(name.clone(), out.clone());
                if !ctx.structural.contains(&name) {
                    effects.push(source_fragment(ctx.source, assign.span));
                }
                out
            } else {
                effects.push(source_fragment(ctx.source, assign.span));
                Val::Unknown
            }
        }
        _ => {
            effects.push(source_fragment(ctx.source, assign.span));
            Val::Unknown
        }
    }
}

fn eval_expr(
    expr: &Expression<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Val {
    match expr {
        Expression::NumericLiteral(n) => exact_i64(n.value).map_or(Val::Unknown, Val::Num),
        Expression::BooleanLiteral(b) => Val::Bool(b.value),
        Expression::NullLiteral(_) => Val::Unknown,
        Expression::Identifier(id) => env.get(id.name.as_str()).cloned().unwrap_or(Val::Unknown),
        Expression::ParenthesizedExpression(p) => eval_expr(&p.expression, env, effects, ctx),
        Expression::ComputedMemberExpression(cm) => {
            if let Some(dec) = ctx.decoder {
                let value = computed_decoder_value(cm, env, dec, ctx.opcode);
                if value != Val::Unknown {
                    return value;
                }
            }
            Val::Unknown
        }
        Expression::UnaryExpression(un) => eval_unary(un, env, effects, ctx),
        Expression::LogicalExpression(log) => eval_logical(log, env, effects, ctx),
        Expression::BinaryExpression(bin) => eval_binary(bin, env, effects, ctx),
        Expression::ConditionalExpression(cond) => {
            let test = eval_expr(&cond.test, env, effects, ctx);
            let Some(truth) = test.truthy() else {
                return Val::Unknown;
            };
            if truth {
                eval_expr(&cond.consequent, env, effects, ctx)
            } else {
                eval_expr(&cond.alternate, env, effects, ctx)
            }
        }
        Expression::SequenceExpression(seq) => {
            let mut last = Val::Undefined;
            for item in &seq.expressions {
                last = eval_expr(item, env, effects, ctx);
                if matches!(last, Val::Fork(_)) {
                    break;
                }
            }
            last
        }
        Expression::AssignmentExpression(assign) => eval_assignment(assign, env, effects, ctx),
        _ => {
            effects.push(source_fragment(ctx.source, expr.span()));
            Val::Unknown
        }
    }
}

struct AssignmentCollector<'a> {
    max_pos: u32,
    assignments: Vec<&'a AssignmentExpression<'a>>,
}

impl<'a> Visit<'a> for AssignmentCollector<'a> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        if let AstKind::AssignmentExpression(assign) = kind {
            if assign.span.start < self.max_pos {
                self.assignments.push(assign);
            }
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn derive_env(
    parent_source: &str,
    max_pos: u32,
    dec: &DecoderCandidate,
    opcode: i64,
) -> Result<Env> {
    let wrapped = format!("({parent_source})");
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, &wrapped, SourceType::cjs());
    if parsed.fatal_error {
        return Err(anyhow!("parent function parse fatal_error"));
    }

    let mut collector = AssignmentCollector {
        max_pos: max_pos + 1,
        assignments: Vec::new(),
    };
    collector.visit_program(&parsed.program);

    let mut env = Env::new();
    if let Some(sel) = dec.selector_var.as_ref() {
        env.insert(sel.clone(), Val::Num(opcode));
    }

    let structural = HashSet::new();
    let ctx = EvalCtx {
        source: &wrapped,
        decoder: Some(dec),
        opcode,
        state_var: None,
        structural,
    };

    for _ in 0..4 {
        let before = env.clone();
        for assign in &collector.assignments {
            let Some(name) = target_ident(&assign.left) else {
                continue;
            };
            let mut sink = Vec::new();
            let rhs = eval_expr(&assign.right, &mut env, &mut sink, &ctx);
            match assign.operator.as_str() {
                "=" if rhs != Val::Unknown && !matches!(rhs, Val::Fork(_)) => {
                    env.insert(name, rhs);
                }
                "+=" => {
                    if let (Some(a), Some(b)) = (env.get(&name).and_then(Val::as_num), rhs.as_num())
                    {
                        env.insert(name, Val::Num(a.wrapping_add(b)));
                    }
                }
                "-=" => {
                    if let (Some(a), Some(b)) = (env.get(&name).and_then(Val::as_num), rhs.as_num())
                    {
                        env.insert(name, Val::Num(a.wrapping_sub(b)));
                    }
                }
                _ => {}
            }
        }
        if env == before {
            break;
        }
    }

    Ok(env)
}

fn unwrap_dispatch_body<'a>(statements: &'a [Statement<'a>]) -> Option<&'a [Statement<'a>]> {
    let Statement::ExpressionStatement(es) = statements.first()? else {
        return None;
    };
    let Expression::CallExpression(call) = &es.expression else {
        return None;
    };
    let first = call.arguments.first()?;
    match first {
        Argument::FunctionExpression(fun) => {
            fun.body.as_ref().map(|body| body.statements.as_slice())
        }
        Argument::ArrowFunctionExpression(fun) => match &fun.body {
            oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Some(body.statements.as_slice()),
            _ => None,
        },
        Argument::ParenthesizedExpression(paren) => match &paren.expression {
            Expression::FunctionExpression(fun) => {
                fun.body.as_ref().map(|body| body.statements.as_slice())
            }
            Expression::ArrowFunctionExpression(fun) => match &fun.body {
                oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => {
                    Some(body.statements.as_slice())
                }
                _ => None,
            },
            _ => None,
        },
        _ => None,
    }
}

fn exec_stmt(
    stmt: &Statement<'_>,
    env: &mut Env,
    effects: &mut Vec<String>,
    ctx: &EvalCtx<'_>,
) -> Exec {
    match stmt {
        Statement::BlockStatement(block) => {
            for s in &block.body {
                match exec_stmt(s, env, effects, ctx) {
                    Exec::Continue => {}
                    other => return other,
                }
            }
            Exec::Continue
        }
        Statement::ExpressionStatement(es) => {
            let value = eval_expr(&es.expression, env, effects, ctx);
            if let Val::Fork(choices) = value {
                Exec::Fork(choices)
            } else {
                Exec::Continue
            }
        }
        Statement::IfStatement(if_stmt) => {
            let test = eval_expr(&if_stmt.test, env, effects, ctx);
            let Some(truth) = test.truthy() else {
                effects.push(source_fragment(ctx.source, if_stmt.span));
                return Exec::Stop("unknown-if");
            };
            if truth {
                exec_stmt(&if_stmt.consequent, env, effects, ctx)
            } else if let Some(alt) = if_stmt.alternate.as_ref() {
                exec_stmt(alt, env, effects, ctx)
            } else {
                Exec::Continue
            }
        }
        Statement::ThrowStatement(thr) => {
            effects.push(format!(
                "throw {}",
                source_fragment(ctx.source, thr.argument.span())
            ));
            Exec::Stop("throw")
        }
        Statement::ReturnStatement(ret) => {
            let suffix = ret
                .argument
                .as_ref()
                .map(|arg| source_fragment(ctx.source, arg.span()))
                .unwrap_or_default();
            effects.push(format!("return {suffix}"));
            Exec::Stop("return")
        }
        Statement::TryStatement(tr) => {
            effects.push(source_fragment(ctx.source, tr.span));
            Exec::Continue
        }
        Statement::VariableDeclaration(decl) => {
            for d in &decl.declarations {
                let oxc_ast::ast::BindingPattern::BindingIdentifier(id) = &d.id else {
                    effects.push(source_fragment(ctx.source, d.span));
                    continue;
                };
                if let Some(init) = d.init.as_ref() {
                    let value = eval_expr(init, env, effects, ctx);
                    if value != Val::Unknown && !matches!(value, Val::Fork(_)) {
                        env.insert(id.name.to_string(), value);
                    } else {
                        effects.push(source_fragment(ctx.source, d.span));
                    }
                }
            }
            Exec::Continue
        }
        Statement::FunctionDeclaration(fun) => {
            effects.push(source_fragment(ctx.source, fun.span));
            Exec::Continue
        }
        Statement::BreakStatement(_) => Exec::Stop("break"),
        _ => {
            effects.push(source_fragment(ctx.source, stmt.span()));
            Exec::Continue
        }
    }
}

fn case_for_state<'a>(cases: &'a [SwitchCase<'a>], state: u64) -> Option<&'a SwitchCase<'a>> {
    let state = i64::try_from(state).ok()?;
    for case in cases {
        let Some(test) = case.test.as_ref() else {
            continue;
        };
        if num_literal(test) == Some(state) {
            return Some(case);
        }
    }
    None
}

fn reduce_paths(
    switch: &oxc_ast::ast::SwitchStatement<'_>,
    sm: &StateMachine,
    initial_env: Env,
    ctx: &EvalCtx<'_>,
) -> Vec<ReducedPath> {
    let Ok(initial_state) = i64::try_from(sm.init_state) else {
        return Vec::new();
    };
    let mut env = initial_env;
    env.insert(sm.state_var.clone(), Val::Num(initial_state));

    let mut queue = VecDeque::new();
    queue.push_back(PathState {
        env,
        effects: Vec::new(),
        states: Vec::new(),
        guards: Vec::new(),
        iterations: 0,
        terminal: None,
    });
    let mut done = Vec::new();

    while let Some(mut path) = queue.pop_front() {
        let mut forked = false;

        while path.iterations < 128 {
            path.iterations += 1;
            let Some(state_i) = path.env.get(&sm.state_var).and_then(Val::as_num) else {
                break;
            };
            let Ok(state) = u64::try_from(state_i) else {
                break;
            };
            if let (Some(sel), Some(shift)) = (sm.selector_var.as_ref(), sm.shift) {
                let selected = (state >> shift) & sm.mask;
                let Ok(selected) = i64::try_from(selected) else {
                    break;
                };
                path.env.insert(sel.clone(), Val::Num(selected));
            }

            let case_id = state & sm.mask;
            path.states.push(state);
            let Some(case) = case_for_state(&switch.cases, case_id) else {
                break;
            };

            let body = unwrap_dispatch_body(&case.consequent)
                .unwrap_or_else(|| case.consequent.as_slice());
            let before = path.env.get(&sm.state_var).cloned();

            let mut terminal = None;
            for stmt in body {
                if matches!(stmt, Statement::BreakStatement(_)) {
                    break;
                }
                match exec_stmt(stmt, &mut path.env, &mut path.effects, ctx) {
                    Exec::Continue => {}
                    Exec::Stop(reason) => {
                        terminal = Some(reason.to_string());
                        break;
                    }
                    Exec::Fork(choices) => {
                        for choice in choices {
                            let mut child = path.clone();
                            child
                                .env
                                .insert(sm.state_var.clone(), Val::Num(choice.value));
                            child.guards.push(choice.guard);
                            queue.push_back(child);
                        }
                        forked = true;
                        break;
                    }
                }
            }

            if forked {
                break;
            }
            if let Some(reason) = terminal {
                path.terminal = Some(reason);
                break;
            }
            if path.env.get(&sm.state_var) == before.as_ref() {
                path.effects.push("[no-state-change]".into());
                break;
            }
        }

        if !forked {
            done.push(ReducedPath {
                guards: path.guards,
                states: path.states,
                effects: path.effects,
                terminal: path.terminal,
            });
        }
    }
    done
}

fn reduce_state_machine(
    raw: &str,
    sm: &StateMachine,
    initial_env: Env,
    opcode: i64,
) -> Result<Vec<ReducedPath>> {
    let allocator = Allocator::default();
    let parsed = parse_program(&allocator, raw, SourceType::cjs());
    if parsed.fatal_error {
        return Err(anyhow!("state machine parse fatal_error"));
    }
    let Statement::ForStatement(for_stmt) = parsed
        .program
        .body
        .first()
        .ok_or_else(|| anyhow!("missing state machine statement"))?
    else {
        return Err(anyhow!("state machine span did not parse as for statement"));
    };
    let Statement::BlockStatement(block) = &for_stmt.body else {
        return Err(anyhow!("state machine body is not a block"));
    };
    let switch = block
        .body
        .iter()
        .find_map(|stmt| {
            if let Statement::SwitchStatement(sw) = stmt {
                Some(sw.as_ref())
            } else {
                None
            }
        })
        .ok_or_else(|| anyhow!("state machine switch missing"))?;

    let mut structural = HashSet::new();
    structural.insert(sm.state_var.clone());
    if let Some(sel) = sm.selector_var.as_ref() {
        structural.insert(sel.clone());
    }
    let ctx = EvalCtx {
        source: raw,
        decoder: None,
        opcode,
        state_var: Some(sm.state_var.as_str()),
        structural,
    };

    Ok(reduce_paths(switch, sm, initial_env, &ctx))
}

fn choose_machine<'a>(
    report: &'a ScanReport,
    dec: &DecoderCandidate,
) -> Result<Option<(&'a FunctionMetric, &'a StateMachine)>> {
    let (ds, de) = parse_fn_id(&dec.function_id)?;
    let mut containers: Vec<_> = report
        .functions
        .iter()
        .filter(|f| f.start <= ds && f.end >= de && f.id != dec.function_id)
        .collect();
    containers.sort_by_key(|f| f.end - f.start);

    for f in containers {
        let mut sms: Vec<_> = report
            .state_machines
            .iter()
            .filter(|sm| sm.function_id == f.id && sm.start > de)
            .collect();
        sms.sort_by_key(|sm| sm.start);
        if let Some(sm) = sms.first() {
            return Ok(Some((f, *sm)));
        }
    }
    Ok(None)
}

fn observed_opcodes(report: &ScanReport, dec: &DecoderCandidate) -> Vec<u64> {
    let Some(start) = dec.builder_start else {
        return Vec::new();
    };
    let Some(builder) = report.push_builders.iter().find(|b| b.start == start) else {
        return Vec::new();
    };
    let Ok(width) = usize::try_from(dec.width) else {
        return Vec::new();
    };
    if width == 0 {
        return Vec::new();
    }
    let mut out = Vec::new();
    for i in (0..builder.values.len()).step_by(width) {
        if let Some(Some(v)) = builder.values.get(i) {
            if !out.contains(v) {
                out.push(*v);
            }
        }
    }
    out.sort_unstable();
    out
}

fn derived_env_json(env: &Env) -> BTreeMap<String, JsonValue> {
    let mut out = BTreeMap::new();
    for (k, v) in env {
        let value = match v {
            Val::Num(n) => JsonValue::from(*n),
            Val::Bool(b) => JsonValue::from(*b),
            Val::Undefined => JsonValue::Null,
            Val::Sym(s) => JsonValue::from(s.clone()),
            Val::Unknown | Val::Fork(_) => continue,
        };
        out.insert(k.clone(), value);
    }
    out
}

fn reduce_report(report: &ScanReport, wanted: Option<&str>) -> Result<Vec<ReducedVm>> {
    let source =
        fs::read_to_string(&report.file).with_context(|| format!("reading {}", report.file))?;
    let mut out = Vec::new();

    for dec in &report.decoder_candidates {
        if dec.builder_var.is_none() || dec.selector_var.is_none() {
            continue;
        }
        if let Some(wanted) = wanted {
            if dec.function_id != wanted {
                continue;
            }
        }
        let Some((parent, sm)) = choose_machine(report, dec)? else {
            continue;
        };

        let parent_source = &source[parent.start as usize..parent.end as usize];
        let pre_handler_limit = sm.start - parent.start;
        let sm_source = &source[sm.start as usize..sm.end as usize];

        let mut rows = Vec::new();
        for opcode in observed_opcodes(report, dec) {
            let Ok(opcode_i64) = i64::try_from(opcode) else {
                continue;
            };
            let env = derive_env(parent_source, pre_handler_limit, dec, opcode_i64)?;
            let paths = reduce_state_machine(sm_source, sm, env.clone(), opcode_i64)?;
            let (states, effects) = if paths.len() == 1 {
                (
                    Some(paths[0].states.clone()),
                    Some(paths[0].effects.clone()),
                )
            } else {
                (None, None)
            };
            rows.push(ReducedOpcode {
                opcode,
                derived_env: derived_env_json(&env),
                paths,
                states,
                effects,
            });
        }

        out.push(ReducedVm {
            file: report.file.clone(),
            decoder: dec.function_id.clone(),
            parent: parent.id.clone(),
            state_machine: sm.clone(),
            opcodes: rows,
        });
    }

    Ok(out)
}

fn main() -> Result<()> {
    let args = Args::parse();
    let text = fs::read_to_string(&args.jsonl)
        .with_context(|| format!("reading {}", args.jsonl.display()))?;
    for (line_no, line) in text.lines().enumerate() {
        if line.trim().is_empty() {
            continue;
        }
        let report: ScanReport =
            serde_json::from_str(line).with_context(|| format!("parsing line {}", line_no + 1))?;
        for reduced in reduce_report(&report, args.function_id.as_deref())? {
            println!("{}", serde_json::to_string(&reduced)?);
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use jsvm_lift::numeric::eval_js_bitwise_i64;

    #[test]
    fn bitwise_evaluation_matches_javascript_32_bit_semantics() {
        assert_eq!(eval_js_bitwise_i64(">>>", -1, 0), Some(4_294_967_295));
        assert_eq!(
            eval_js_bitwise_i64(">>", 0x8000_0000, 0),
            Some(-2_147_483_648)
        );
        assert_eq!(eval_js_bitwise_i64("<<", 1, 33), Some(2));
        assert_eq!(
            eval_js_bitwise_i64("&", 0xffff_ffff, 0x8000_0000),
            Some(-2_147_483_648)
        );
    }
}
