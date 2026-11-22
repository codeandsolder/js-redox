//! Declaration hazards for statement removal and relocation. Only descend
//! through the current execution region, never a nested function or class.
use oxc_ast::ast::{Statement, VariableDeclaration, VariableDeclarationKind};
use oxc_ast_visit::{walk, Visit};

#[derive(Clone, Copy)]
pub enum DeclarationHazard {
    /// Removing an unreachable statement can still remove a hoisted binding.
    Discard,
    /// Moving a guard across a scope exit can move disposal or Annex B effects.
    Relocate,
}

impl DeclarationHazard {
    pub(crate) fn present(self, statements: &[&Statement<'_>]) -> bool {
        let mut probe = Probe {
            policy: self,
            found: false,
        };
        for statement in statements {
            probe.visit_statement(statement);
            if probe.found {
                return true;
            }
        }
        false
    }
}

struct Probe {
    policy: DeclarationHazard,
    found: bool,
}

impl<'a> Visit<'a> for Probe {
    fn visit_variable_declaration(&mut self, node: &VariableDeclaration<'a>) {
        self.found |= match self.policy {
            DeclarationHazard::Discard => node.kind == VariableDeclarationKind::Var,
            DeclarationHazard::Relocate => !matches!(
                node.kind,
                VariableDeclarationKind::Var
                    | VariableDeclarationKind::Let
                    | VariableDeclarationKind::Const
            ),
        };
        if !self.found {
            walk::walk_variable_declaration(self, node);
        }
    }

    fn visit_statement(&mut self, statement: &Statement<'a>) {
        if self.found {
            return;
        }
        // Annex B may create an enclosing var binding even when the branch
        // never runs.
        if matches!(statement, Statement::FunctionDeclaration(_)) {
            self.found = true;
        } else {
            walk::walk_statement(self, statement);
        }
    }
    fn visit_function(&mut self, _: &oxc_ast::ast::Function<'a>, _: oxc_syntax::scope::ScopeFlags) {
    }
    fn visit_arrow_function_expression(&mut self, _: &oxc_ast::ast::ArrowFunctionExpression<'a>) {}
    fn visit_class(&mut self, _: &oxc_ast::ast::Class<'a>) {}
}
