use oxc_allocator::Allocator;
use oxc_ast::{ast::Program, AstKind};
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

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum PropertyMode {
    #[default]
    Literal,
    Opaque,
    Canonical,
}

struct ShapeVisitor {
    ids: HashMap<String, usize>,
    reverse: HashMap<usize, String>,
    props: HashMap<String, usize>,
    next_id: usize,
    next_prop: usize,
    tokens: Vec<String>,
    property_mode: PropertyMode,
}

impl ShapeVisitor {
    fn new(property_mode: PropertyMode) -> Self {
        Self {
            ids: HashMap::new(),
            reverse: HashMap::new(),
            props: HashMap::new(),
            next_id: 0,
            next_prop: 0,
            tokens: Vec::new(),
            property_mode,
        }
    }

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

    fn canonical_prop(&mut self, name: &str) -> usize {
        if let Some(id) = self.props.get(name) {
            return *id;
        }
        let id = self.next_prop;
        self.next_prop += 1;
        self.props.insert(name.to_string(), id);
        id
    }

    fn identifier_property_token(&mut self, name: &str) -> String {
        match self.property_mode {
            PropertyMode::Literal => format!("P:{name}"),
            PropertyMode::Opaque => "P:STATIC".into(),
            PropertyMode::Canonical => format!("P{}", self.canonical_prop(name)),
        }
    }

    fn member_property_token(&mut self, name: &str) -> String {
        match self.property_mode {
            PropertyMode::Literal => format!("MEM:{name}"),
            PropertyMode::Opaque => "MEM:STATIC".into(),
            PropertyMode::Canonical => format!("MEM:P{}", self.canonical_prop(name)),
        }
    }
}

impl<'a> Visit<'a> for ShapeVisitor {
    fn enter_node(&mut self, kind: AstKind<'a>) {
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
            AstKind::IdentifierName(id) => {
                let token = self.identifier_property_token(id.name.as_str());
                self.tokens.push(token);
            }
            AstKind::NumericLiteral(_) => self.tokens.push("NUM".into()),
            AstKind::StringLiteral(_) => self.tokens.push("STR".into()),
            AstKind::BooleanLiteral(b) => self.tokens.push(format!("BOOL:{}", b.value)),
            AstKind::NullLiteral(_) => self.tokens.push("NULL".into()),
            AstKind::BinaryExpression(e) => {
                self.tokens.push(format!("BIN:{}", e.operator.as_str()))
            }
            AstKind::LogicalExpression(e) => {
                self.tokens.push(format!("LOG:{}", e.operator.as_str()))
            }
            AstKind::UnaryExpression(e) => self.tokens.push(format!("UN:{}", e.operator.as_str())),
            AstKind::UpdateExpression(e) => {
                self.tokens
                    .push(format!("UP:{}:{}", e.operator.as_str(), e.prefix))
            }
            AstKind::AssignmentExpression(e) => {
                self.tokens.push(format!("AS:{}", e.operator.as_str()))
            }
            AstKind::StaticMemberExpression(e) => {
                let token = self.member_property_token(e.property.name.as_str());
                self.tokens.push(token);
            }
            AstKind::ComputedMemberExpression(_) => self.tokens.push("MEM:[]".into()),
            AstKind::CallExpression(e) => {
                self.tokens
                    .push(format!("CALL:{}:{}", e.arguments.len(), e.optional))
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
                    .push(format!("ARROW:{}:{}", f.params.items.len(), f.r#async))
            }
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &Program<'a>) {
        walk::walk_program(self, it);
    }
}

#[must_use]
pub fn hash_shape_text(text: &str) -> u64 {
    let mut h = 0xcbf2_9ce4_8422_2325_u64;
    for byte in text.as_bytes() {
        h ^= u64::from(*byte);
        h = h.wrapping_mul(0x0100_0000_01b3);
    }
    h
}

#[must_use]
pub fn analyze_program(program: &Program<'_>, property_mode: PropertyMode) -> EffectShape {
    let mut visitor = ShapeVisitor::new(property_mode);
    visitor.visit_program(program);
    let text = visitor.tokens.join("|");
    EffectShape {
        hash: hash_shape_text(&text),
        text,
        ids: visitor.ids,
        reverse: visitor.reverse,
    }
}

#[must_use]
pub fn analyze_effect(source: &str) -> EffectShape {
    for candidate in [source.to_string(), format!("({source})")] {
        let allocator = Allocator::default();
        let parsed = parse_program(&allocator, &candidate, SourceType::cjs());
        if parsed.is_clean() {
            return analyze_program(&parsed.program, PropertyMode::Literal);
        }
    }
    let text = "PARSEFAIL".to_string();
    EffectShape {
        hash: hash_shape_text(&text),
        text,
        ids: HashMap::new(),
        reverse: HashMap::new(),
    }
}

#[must_use]
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
