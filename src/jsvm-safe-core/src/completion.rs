//! Backward demand analysis for ECMAScript Completion Record values.
//!
//! Script/eval evaluation may return the last value, whereas ordinary
//! function/module evaluation discards normal statement completion. Empty is
//! not `undefined`: a statement list propagates its previous value through an
//! empty completion. A break/continue can carry that value to an enclosing
//! label, loop or switch. This pass tracks demand on normal and jumping paths;
//! throw and return carry their own explicit values.
use oxc_ast::ast::{Program, Statement};
use oxc_span::{GetSpan, Span};
use std::collections::HashSet;

#[derive(Clone, Copy)]
struct Demand {
    normal: bool,
    jump: bool,
}

impl Demand {
    const fn any(self) -> bool {
        self.normal || self.jump
    }

    const fn repeated(self) -> Self {
        Self {
            normal: self.any(),
            jump: self.any(),
        }
    }
}

#[derive(Default)]
pub struct CompletionLiveness {
    live: HashSet<(u32, u32)>,
}

impl CompletionLiveness {
    pub(crate) fn analyze(program: &Program<'_>) -> Self {
        let mut analysis = Self::default();
        // CJS input is also used for classic/eval source: retain completion
        // unless module grammar explicitly rules out its observation.
        if !program.source_type.is_module() {
            analysis.list(
                &program.body,
                Demand {
                    normal: true,
                    jump: false,
                },
            );
        }
        analysis
    }

    pub(crate) fn needs_value(&self, span: Span) -> bool {
        self.live.contains(&(span.start, span.end))
    }

    /// Return whether the incoming list value can reach a demanded empty
    /// completion of this suffix. A later guaranteed nonempty expression
    /// kills that demand on normal paths, but not on a preceding jump.
    fn list(&mut self, statements: &[Statement<'_>], mut demand: Demand) -> bool {
        for statement in statements.iter().rev() {
            demand.normal = self.statement(statement, demand);
        }
        demand.normal
    }

    fn statement(&mut self, stmt: &Statement<'_>, demand: Demand) -> bool {
        if !demand.any() {
            return false;
        }
        let span = stmt.span();
        match stmt {
            Statement::ExpressionStatement(_) => {
                if demand.normal {
                    self.live.insert((span.start, span.end));
                }
                false // successful evaluation always supplies a value
            }
            Statement::BreakStatement(_) | Statement::ContinueStatement(_) => demand.jump,
            Statement::ReturnStatement(_) | Statement::ThrowStatement(_) => false,
            Statement::BlockStatement(block) => self.list(&block.body, demand),
            Statement::LabeledStatement(label) => self.statement(
                &label.body,
                Demand {
                    normal: demand.normal,
                    jump: demand.any(),
                },
            ),
            // UpdateEmpty(undefined) is applied to these statement forms.
            // Their result cannot inherit a preceding statement's value.
            Statement::IfStatement(branch) => {
                self.live.insert((span.start, span.end));
                self.statement(&branch.consequent, demand);
                if let Some(other) = &branch.alternate {
                    self.statement(other, demand);
                }
                false
            }
            Statement::WithStatement(with) => {
                self.statement(&with.body, demand);
                false
            }
            Statement::WhileStatement(node) => self.loop_body(span, &node.body, demand),
            Statement::DoWhileStatement(node) => self.loop_body(span, &node.body, demand),
            Statement::ForStatement(node) => self.loop_body(span, &node.body, demand),
            Statement::ForInStatement(node) => self.loop_body(span, &node.body, demand),
            Statement::ForOfStatement(node) => self.loop_body(span, &node.body, demand),
            Statement::SwitchStatement(switch) => {
                self.live.insert((span.start, span.end));
                let mut case_demand = demand.repeated();
                for case in switch.cases.iter().rev() {
                    case_demand.normal = self.list(&case.consequent, case_demand);
                }
                false
            }
            Statement::TryStatement(node) => {
                self.list(&node.block.body, demand);
                if let Some(handler) = &node.handler {
                    self.list(&handler.body.body, demand);
                }
                if let Some(finalizer) = &node.finalizer {
                    // A normal finally completion is ignored, but an abrupt
                    // finally completion replaces the pending completion.
                    self.list(
                        &finalizer.body,
                        Demand {
                            normal: false,
                            jump: demand.jump,
                        },
                    );
                }
                false
            }
            // Empty statements and declarations normally provide no value.
            // Do not enter function/class bodies: they are distinct completion
            // scopes, and cannot jump to a label in this script.
            _ => demand.normal,
        }
    }

    fn loop_body(&mut self, span: Span, body: &Statement<'_>, demand: Demand) -> bool {
        self.live.insert((span.start, span.end));
        self.statement(body, demand.repeated());
        false // loop accumulator V initially contains undefined
    }
}

/// Start a statement-list result with undefined, so an empty selected body
/// behaves like the original UpdateEmpty(undefined) construct. The outer
/// block also protects dangling-else and direct-child statement boundaries.
pub fn seed_undefined(body: &str) -> String {
    format!("{{\nvoid 0;\n{body}\n}}")
}

/// Selecting a known branch must preserve both `UpdateEmpty` and the statement
/// grammar around it. Simple value-producing/abrupt statements need no seed;
/// an explicit terminator prevents new ASI continuations after a removed else.
pub fn selected_if_branch(
    selected: Option<&Statement<'_>>,
    source: &str,
    completion_live: bool,
) -> String {
    let Some(statement) = selected else {
        return if completion_live {
            "void 0;".to_owned()
        } else {
            ";".to_owned()
        };
    };
    let text = crate::fragment(source, statement.span());
    match statement {
        Statement::ExpressionStatement(_)
        | Statement::ReturnStatement(_)
        | Statement::ThrowStatement(_) => {
            if text.trim_end().ends_with(';') {
                text.to_owned()
            } else {
                format!("{text}\n;")
            }
        }
        _ if completion_live => seed_undefined(text),
        Statement::BlockStatement(_) => text.to_owned(),
        _ => format!("{{\n{text}\n}}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use oxc_allocator::Allocator;
    use oxc_ast_visit::{walk, Visit};
    use oxc_span::SourceType;
    use rolldown_redox::ecmascript::parse_program;

    fn live_expressions(source: &str) -> Vec<String> {
        struct Probe<'a> {
            source: &'a str,
            analysis: &'a CompletionLiveness,
            live: Vec<String>,
        }
        impl<'a> Visit<'a> for Probe<'_> {
            fn visit_expression_statement(&mut self, node: &oxc_ast::ast::ExpressionStatement<'a>) {
                if self.analysis.needs_value(node.span) {
                    self.live
                        .push(crate::fragment(self.source, node.expression.span()).to_owned());
                }
                walk::walk_expression_statement(self, node);
            }
        }
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, source, SourceType::cjs());
        assert!(parsed.is_clean());
        let analysis = CompletionLiveness::analyze(&parsed.program);
        let mut probe = Probe {
            source,
            analysis: &analysis,
            live: Vec::new(),
        };
        probe.visit_program(&parsed.program);
        probe.live
    }

    #[test]
    #[ignore = "requires Node; differential checks script completion liveness"]
    fn demand_never_drops_observable_preceding_completion() -> Result<(), Box<dyn std::error::Error>>
    {
        let suffixes = [
            ";",
            "{}",
            "{;}",
            "{var x;}",
            "{let x;}",
            "{2;}",
            "{var x;2;}",
            "L:;",
            "L:{}",
            "L:{;}",
            "L:{let x;}",
            "L:{break L;}",
            "L:{2;break L;}",
            "L:{;break L;}",
            "L:{try{break L;}finally{;}}",
            "L:{try{2;break L;}finally{;}}",
            "L:{try{}finally{break L;}}",
            "if(false){}",
            "if(true){}",
            "if(false){2;}",
            "if(true){2;}",
            "while(false){}",
            "while(true){break;}",
            "do{}while(false)",
            "do{2;break;}while(false)",
            "for(;false;){}",
            "for(let i=0;i<1;i++){2;}",
            "switch(1){}",
            "switch(1){case 2:22;}",
            "switch(1){case 1:;}",
            "switch(1){default:;}",
            "switch(1){case 1:2;break;}",
            "switch(1){case 1:;break;}",
            "try{}catch(e){}",
            "try{}finally{}",
            "try{;}finally{;}",
            "try{2;}finally{}",
            "try{2;}finally{3;}",
            "try{throw 2;}catch(e){}",
            "try{throw 2;}catch(e){3;}",
            "try{throw 2;}catch(e){;}finally{3;}",
            "with({}){}",
            "with({}){;}",
            "with({}){2;}",
            "function f(){}",
            "class C{}",
        ];
        let suffixes = suffixes.into_iter().map(str::to_owned).collect::<Vec<_>>();
        assert_eq!(verify_normal_completion_demand(&suffixes)?, 13);
        Ok(())
    }

    /// Check soundness, not exact precision: any script value that a real
    /// engine carries from an earlier expression must be demanded. The same
    /// oracle is shared by hand-picked and grammar-composed regressions.
    fn verify_normal_completion_demand(
        suffixes: &[String],
    ) -> Result<usize, Box<dyn std::error::Error>> {
        use std::process::Command;
        let harness = r"
const vm=require('node:vm');
const suffixes=JSON.parse(process.argv[1]);
function observe(source) {
 try {
   const options={}; options.timeout=500;
   const v=vm.runInNewContext(source,Object.create(null),options);
   return v===undefined?['undefined']:['value',typeof v,String(v)];
 } catch(e) {
   return ['throw',e.name];
 }
}
console.log(JSON.stringify(suffixes.map(suffix=>{
 const value=observe('1;'+suffix);
 const empty=observe(';'+suffix);
 return JSON.stringify(value)!==JSON.stringify(empty);
})));
";
        let output = Command::new("node")
            .arg("-e")
            .arg(harness)
            .arg(serde_json::to_string(suffixes)?)
            .output()?;
        assert!(output.status.success(), "{output:?}");
        let observed: Vec<bool> = serde_json::from_slice(&output.stdout)?;
        assert_eq!(observed.len(), suffixes.len());

        let count = observed.iter().filter(|&&flag| flag).count();
        for (suffix, observable) in suffixes.iter().zip(observed) {
            let source = format!("1;{suffix}");
            let allocator = Allocator::default();
            let parsed = parse_program(&allocator, &source, SourceType::cjs());
            assert!(parsed.is_clean(), "{source}");
            let analysis = CompletionLiveness::analyze(&parsed.program);
            let first = parsed
                .program
                .body
                .first()
                .ok_or_else(|| std::io::Error::other("missing first expression"))?;
            assert!(
                !observable || analysis.needs_value(first.span()),
                "Dropped observable preceding script completion for {source}"
            );
        }
        Ok(count)
    }

    #[test]
    #[ignore = "requires Node; compositional script completion liveness oracle"]
    fn generated_statement_grammar_preserves_preceding_completion_demand(
    ) -> Result<(), Box<dyn std::error::Error>> {
        let bases = [
            ";",
            "{}",
            "{;}",
            "{let q;}",
            "{2;}",
            "2;",
            "void 0;",
            "if(false){}",
            "if(true){2;}",
            "if(false){2;}else{3;}",
            "while(false){}",
            "while(true){2;break;}",
            "do{2;}while(false)",
            "for(let i=0;i<1;i++){2;}",
            "switch(1){case 1:2;break;}",
            "switch(2){case 1:2;}",
            "try{2;}finally{}",
            "try{}finally{2;}",
            "try{throw 2;}catch(e){3;}",
            "with({}){2;}",
            "function f(){}",
            "class C{}",
        ];
        let mut suffixes = Vec::new();
        for base in bases {
            let contexts = [
                base.to_owned(),
                format!("{{{base}}}"),
                format!("OUT:{{{base}}}"),
                format!("OUT:{{{base} break OUT;}}"),
                format!("try{{{base}}}finally{{;}}"),
                format!("try{{;}}finally{{{base}}}"),
                format!("if(true){{{base}}}"),
                format!("if(false){{{base}}}"),
                format!("switch(1){{case 1:{{{base}}} break;}}"),
            ];
            for context in contexts {
                suffixes.push(context.clone());
                suffixes.push(format!("{context};"));
                suffixes.push(format!("{context} function after(){{}}"));
            }
        }
        assert_eq!(suffixes.len(), 594);
        let observable = verify_normal_completion_demand(&suffixes)?;
        assert!(
            observable >= 60,
            "insufficient observable paths: {observable}"
        );
        Ok(())
    }

    #[test]
    fn tracks_values_through_empty_statements_and_abrupt_paths() {
        for (source, expected) in [
            ("1; 2; var x;", vec!["2"]),
            ("1; {2; var x;}", vec!["2"]),
            ("1; {var x;}", vec!["1"]),
            ("outer: {1; {break outer;} 2;}", vec!["1", "2"]),
            ("outer: {1; if(flag) break outer; 2;}", vec!["2"]),
            ("while(flag){1; continue; 2;}", vec!["1", "2"]),
            ("switch(flag){case 1:1;case 2:2;break;}", vec!["2"]),
            ("switch(flag){case 1:1;break;case 2:2;}", vec!["1", "2"]),
            ("try {1;} finally {2;}", vec!["1"]),
            ("outer:try {1;} finally {2;break outer;}", vec!["1", "2"]),
            ("function f(){1;} class C{static{2;}} 3;", vec!["3"]),
        ] {
            assert_eq!(live_expressions(source), expected, "{source}");
        }
    }
}
