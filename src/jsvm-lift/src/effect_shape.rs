use oxc_allocator::Allocator;
use oxc_ast::AstKind;
use oxc_ast_visit::{walk, Visit};
use oxc_span::SourceType;
use rolldown_redox::ecmascript::parse_program;
use std::{collections::HashMap, path::Path};

#[derive(Clone, Debug)]
pub struct EffectShape {
    pub text: String,
    pub hash: u64,
    pub ids: HashMap<String, usize>,
    pub reverse: HashMap<usize, String>,
}

#[derive(Default)]
struct ShapeVisitor {
    ids: HashMap<String, usize>,
    reverse: HashMap<usize, String>,
    next_id: usize,
    tokens: Vec<String>,
}

impl ShapeVisitor {
    fn canonical_id(&mut self, name: &str) -> usize {
        if let Some(id) = self.ids.get(name) {
            return *id;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.ids.insert(name.to_string(), id);
        self.reverse.insert(id, name.to_string());
        id
    }

    fn shape_text(&self) -> String {
        self.tokens.join("|")
    }
}

impl<'a> Visit<'a> for ShapeVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        // AstType discriminants are stable for the pinned Oxc version and give
        // a compact preorder structural stream.
        self.tokens.push(format!("K{}", kind.ty() as u8));
        match kind {
            AstKind::IdentifierReference(id) => {
                let n = self.canonical_id(id.name.as_str());
                self.tokens.push(format!("I{n}"));
            }
            AstKind::BindingIdentifier(id) => {
                let n = self.canonical_id(id.name.as_str());
                self.tokens.push(format!("B{n}"));
            }
            AstKind::IdentifierName(id) => self.tokens.push(format!("P:{}", id.name)),
            AstKind::NumericLiteral(_) => self.tokens.push("NUM".into()),
            AstKind::StringLiteral(_) => self.tokens.push("STR".into()),
            AstKind::BooleanLiteral(b) => self.tokens.push(format!("BOOL:{}", b.value)),
            AstKind::NullLiteral(_) => self.tokens.push("NULL".into()),
            AstKind::BinaryExpression(e) => {
                self.tokens.push(format!("BIN:{}", e.operator.as_str()));
            }
            AstKind::LogicalExpression(e) => {
                self.tokens.push(format!("LOG:{}", e.operator.as_str()));
            }
            AstKind::UnaryExpression(e) => self.tokens.push(format!("UN:{}", e.operator.as_str())),
            AstKind::UpdateExpression(e) => {
                self.tokens
                    .push(format!("UP:{}:{}", e.operator.as_str(), e.prefix));
            }
            AstKind::AssignmentExpression(e) => {
                self.tokens.push(format!("AS:{}", e.operator.as_str()));
            }
            AstKind::StaticMemberExpression(e) => {
                self.tokens.push(format!("MEM:{}", e.property.name));
            }
            AstKind::ComputedMemberExpression(_) => self.tokens.push("MEM:[]".into()),
            AstKind::CallExpression(e) => {
                self.tokens
                    .push(format!("CALL:{}:{}", e.arguments.len(), e.optional));
            }
            AstKind::NewExpression(e) => self.tokens.push(format!("NEW:{}", e.arguments.len())),
            AstKind::Function(f) => self.tokens.push(format!(
                "FN:{}:{}:{}",
                f.params.items.len(),
                f.r#async,
                f.generator
            )),
            AstKind::ArrowFunctionExpression(f) => {
                self.tokens
                    .push(format!("ARROW:{}:{}", f.params.items.len(), f.r#async));
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn fnv1a64(data: &[u8]) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325_u64;
    for byte in data {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

pub fn analyze_effect(source: &str) -> EffectShape {
    for candidate in [source.to_string(), format!("({source})")] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &candidate, SourceType::cjs());
        if !parsed.is_clean() {
            continue;
        }
        let mut visitor = ShapeVisitor::default();
        visitor.visit_program(&parsed.program);
        let text = visitor.shape_text();
        return EffectShape {
            hash: fnv1a64(text.as_bytes()),
            text,
            ids: visitor.ids,
            reverse: visitor.reverse,
        };
    }

    let text = "PARSEFAIL".to_string();
    EffectShape {
        hash: fnv1a64(text.as_bytes()),
        text,
        ids: HashMap::new(),
        reverse: HashMap::new(),
    }
}

pub fn family_name(file: &str) -> String {
    Path::new(file)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or(file)
        .to_string()
}

#[cfg(test)]
mod tests {
    use super::analyze_effect;

    #[test]
    fn alpha_renaming_preserves_shape() {
        let left = analyze_effect("let a=1;a=a+2;");
        let right = analyze_effect("let renamed=1;renamed=renamed+2;");
        assert_eq!(left.text, right.text);
        assert_eq!(left.hash, right.hash);
    }

    #[test]
    fn static_property_names_remain_semantic() {
        let left = analyze_effect("value.left;");
        let right = analyze_effect("value.right;");
        assert_ne!(left.text, right.text);
        assert_ne!(left.hash, right.hash);
    }

    #[test]
    fn anonymous_function_uses_parenthesized_fallback() {
        let shape = analyze_effect("function(value){return value;}");
        assert_ne!(shape.text, "PARSEFAIL");
        assert_eq!(shape.ids.get("value"), Some(&0));
    }

    #[test]
    fn malformed_source_has_stable_failure_shape() {
        let shape = analyze_effect("function (");
        assert_eq!(shape.text, "PARSEFAIL");
        assert!(shape.ids.is_empty());
        assert!(shape.reverse.is_empty());
    }
}
