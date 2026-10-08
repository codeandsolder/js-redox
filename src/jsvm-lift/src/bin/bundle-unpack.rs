use anyhow::{Context, Result};
use clap::Parser as ClapParser;
use oxc_allocator::Allocator;
use oxc_ast::{
    ast::{
        Argument, ArrayExpressionElement, AssignmentTarget, BindingPattern, Expression,
        IdentifierReference, ObjectPropertyKind, PropertyKey,
    },
    AstKind,
};
use oxc_ast_visit::{walk, Visit};
use oxc_semantic::{Scoping, SemanticBuilder};
use oxc_span::{GetSpan, SourceType};
use oxc_syntax::symbol::SymbolId;
use rolldown_redox::ecmascript::parse_program;
use serde::Serialize;
use std::{
    collections::{BTreeMap, BTreeSet, HashMap, HashSet},
    fs,
    path::PathBuf,
};

#[derive(ClapParser, Debug)]
#[command(about = "Inventory statically explicit Webpack/Next JSONP chunk module tables")]
struct Args {
    input: PathBuf,
}

#[derive(Debug, Clone, Serialize)]
struct ModuleRecord {
    id: String,
    property_start: u32,
    property_end: u32,
    value_start: u32,
    value_end: u32,
    value_kind: String,
    method: bool,
    dependencies: Vec<String>,
    dependency_map: BTreeMap<String, String>,
    export_names: Vec<String>,
    commonjs_export: bool,
}

#[derive(Debug, Clone, Serialize)]
struct BundleRecord {
    kind: String,
    start: u32,
    end: u32,
    callee: String,
    chunk_ids: Vec<String>,
    module_table_start: u32,
    module_table_end: u32,
    modules: Vec<ModuleRecord>,
}

#[derive(Debug, Serialize)]
struct Report {
    schema: &'static str,
    input: String,
    diagnostics: usize,
    fatal_error: bool,
    bundles: Vec<BundleRecord>,
}

fn reference_symbol(scoping: &Scoping, id: &IdentifierReference<'_>) -> Option<SymbolId> {
    let reference_id = id.reference_id.get()?;
    scoping.get_reference(reference_id).symbol_id()
}

fn binding_symbol(pattern: &BindingPattern<'_>) -> Option<SymbolId> {
    let BindingPattern::BindingIdentifier(id) = pattern else {
        return None;
    };
    id.symbol_id.get()
}

fn expression_symbol(scoping: &Scoping, expr: &Expression<'_>) -> Option<SymbolId> {
    match expr {
        Expression::Identifier(id) => reference_symbol(scoping, id),
        Expression::ParenthesizedExpression(paren) => expression_symbol(scoping, &paren.expression),
        _ => None,
    }
}

fn unwrap_parenthesized<'a>(mut expr: &'a Expression<'a>) -> &'a Expression<'a> {
    while let Expression::ParenthesizedExpression(paren) = expr {
        expr = &paren.expression;
    }
    expr
}

fn arrow_block_body<'a>(
    function: &'a oxc_ast::ast::ArrowFunctionExpression<'a>,
) -> Option<&'a oxc_ast::ast::FunctionBody<'a>> {
    match &function.body {
        oxc_ast::ast::ArrowFunctionBody::FunctionBody(body) => Some(&**body),
        _ => None,
    }
}

fn computed_string(expr: &Expression<'_>) -> Option<String> {
    match expr {
        Expression::StringLiteral(value) => Some(value.value.to_string()),
        Expression::ParenthesizedExpression(paren) => computed_string(&paren.expression),
        _ => None,
    }
}

struct DependencyCollector<'s> {
    scoping: &'s Scoping,
    require_symbol: SymbolId,
    dependencies: BTreeSet<String>,
}

impl<'a> Visit<'a> for DependencyCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        let AstKind::CallExpression(call) = kind else {
            return;
        };
        let Expression::Identifier(callee) = &call.callee else {
            return;
        };
        if reference_symbol(self.scoping, callee) != Some(self.require_symbol) {
            return;
        }
        let Some(first) = call.arguments.first() else {
            return;
        };
        let dependency = match first {
            Argument::NumericLiteral(value)
                if value.value.is_finite() && value.value.fract() == 0.0 =>
            {
                Some(format!("{:.0}", value.value))
            }
            Argument::StringLiteral(value) => Some(value.value.to_string()),
            _ => None,
        };
        if let Some(dependency) = dependency {
            self.dependencies.insert(dependency);
        }
    }
}

struct ExportCollector<'s> {
    scoping: &'s Scoping,
    module_symbol: Option<SymbolId>,
    exports_symbol: Option<SymbolId>,
    require_symbol: Option<SymbolId>,
    names: BTreeSet<String>,
    commonjs_export: bool,
}

impl ExportCollector<'_> {
    fn is_exports_expr(&self, expr: &Expression<'_>) -> bool {
        self.exports_symbol.is_some()
            && expression_symbol(self.scoping, expr) == self.exports_symbol
    }

    fn is_module_exports_expr(&self, expr: &Expression<'_>) -> bool {
        let Some(module_symbol) = self.module_symbol else {
            return false;
        };
        match expr {
            Expression::StaticMemberExpression(member) => {
                member.property.name.as_str() == "exports"
                    && expression_symbol(self.scoping, &member.object) == Some(module_symbol)
            }
            Expression::ComputedMemberExpression(member) => {
                computed_string(&member.expression).as_deref() == Some("exports")
                    && expression_symbol(self.scoping, &member.object) == Some(module_symbol)
            }
            Expression::ParenthesizedExpression(paren) => {
                self.is_module_exports_expr(&paren.expression)
            }
            _ => false,
        }
    }

    fn add_name(&mut self, name: String) {
        if name != "__esModule" {
            self.names.insert(name);
        }
    }

    fn record_assignment(&mut self, assign: &oxc_ast::ast::AssignmentExpression<'_>) {
        match &assign.left {
            AssignmentTarget::StaticMemberExpression(member) => {
                let name = member.property.name.to_string();
                if self.is_exports_expr(&member.object)
                    || self.is_module_exports_expr(&member.object)
                {
                    self.add_name(name);
                } else if name == "exports"
                    && self.module_symbol.is_some()
                    && expression_symbol(self.scoping, &member.object) == self.module_symbol
                {
                    self.commonjs_export = true;
                }
            }
            AssignmentTarget::ComputedMemberExpression(member) => {
                let Some(name) = computed_string(&member.expression) else {
                    return;
                };
                if self.is_exports_expr(&member.object)
                    || self.is_module_exports_expr(&member.object)
                {
                    self.add_name(name);
                } else if name == "exports"
                    && self.module_symbol.is_some()
                    && expression_symbol(self.scoping, &member.object) == self.module_symbol
                {
                    self.commonjs_export = true;
                }
            }
            _ => {}
        }
    }

    fn record_call(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        let Some(require_symbol) = self.require_symbol else {
            return;
        };
        let (object, method) = match &call.callee {
            Expression::StaticMemberExpression(member) => {
                (&member.object, Some(member.property.name.to_string()))
            }
            Expression::ComputedMemberExpression(member) => {
                (&member.object, computed_string(&member.expression))
            }
            _ => return,
        };
        if method.as_deref() != Some("d")
            || expression_symbol(self.scoping, object) != Some(require_symbol)
        {
            return;
        }
        let Some(Argument::Identifier(exports)) = call.arguments.first() else {
            return;
        };
        if self.exports_symbol.is_none()
            || reference_symbol(self.scoping, exports) != self.exports_symbol
        {
            return;
        }
        let Some(Argument::ObjectExpression(object)) = call.arguments.get(1) else {
            return;
        };
        for property in &object.properties {
            let ObjectPropertyKind::ObjectProperty(property) = property else {
                continue;
            };
            if property.computed {
                continue;
            }
            if let Some(name) = Collector::property_key(&property.key) {
                self.add_name(name);
            }
        }
    }
}

impl<'a> Visit<'a> for ExportCollector<'_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::AssignmentExpression(assign) => self.record_assignment(assign),
            AstKind::CallExpression(call) => self.record_call(call),
            _ => {}
        }
    }
}

#[derive(Default)]
struct AmdLoaderEvidence {
    define_assignment: bool,
    require_assignment: bool,
    requirejs_assignment: bool,
    load_modules_assignment: bool,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
enum MemberReceiverKey {
    Local(SymbolId),
    Global(String),
}

struct AmdMemberGroup {
    callee: String,
    start: u32,
    end: u32,
    explicit_dependency_arrays: usize,
    modules: Vec<ModuleRecord>,
}

struct Collector<'s, 'c> {
    source: &'s str,
    scoping: &'c Scoping,
    bundles: Vec<BundleRecord>,
    amd_modules: Vec<ModuleRecord>,
    amd_start: Option<u32>,
    amd_end: Option<u32>,
    amd_member_groups: HashMap<MemberReceiverKey, AmdMemberGroup>,
    amd_loader_evidence: HashMap<SymbolId, AmdLoaderEvidence>,
}

impl Collector<'_, '_> {
    fn fragment(&self, span: oxc_span::Span) -> &str {
        self.source
            .get(span.start as usize..(span.end as usize).min(self.source.len()))
            .unwrap_or_default()
    }

    fn property_key(key: &PropertyKey<'_>) -> Option<String> {
        match key {
            PropertyKey::StaticIdentifier(id) => Some(id.name.to_string()),
            PropertyKey::NumericLiteral(n) if n.value.is_finite() && n.value.fract() == 0.0 => {
                Some(format!("{:.0}", n.value))
            }
            PropertyKey::StringLiteral(s) => Some(s.value.to_string()),
            _ => None,
        }
    }

    fn array_literal_ids(arr: &oxc_ast::ast::ArrayExpression<'_>) -> Option<Vec<String>> {
        let mut ids = Vec::new();
        for element in &arr.elements {
            match element {
                ArrayExpressionElement::NumericLiteral(n)
                    if n.value.is_finite() && n.value.fract() == 0.0 =>
                {
                    ids.push(format!("{:.0}", n.value));
                }
                ArrayExpressionElement::StringLiteral(s) => ids.push(s.value.to_string()),
                _ => return None,
            }
        }
        Some(ids)
    }

    fn amd_factory_expression_parts<'a>(
        expression: &'a Expression<'a>,
    ) -> Option<(
        &'a oxc_ast::ast::FormalParameters<'a>,
        &'a oxc_ast::ast::FunctionBody<'a>,
        oxc_span::Span,
        &'static str,
    )> {
        match expression {
            Expression::FunctionExpression(function) => {
                let body = function.body.as_ref()?;
                Some((&function.params, body.as_ref(), function.span, "function"))
            }
            Expression::ArrowFunctionExpression(function) => Some((
                &function.params,
                arrow_block_body(function)?,
                function.span,
                "arrow",
            )),
            Expression::ParenthesizedExpression(paren) => {
                Self::amd_factory_expression_parts(&paren.expression)
            }
            _ => None,
        }
    }

    fn amd_factory_parts<'a>(
        argument: &'a Argument<'a>,
    ) -> Option<(
        &'a oxc_ast::ast::FormalParameters<'a>,
        &'a oxc_ast::ast::FunctionBody<'a>,
        oxc_span::Span,
        &'static str,
    )> {
        match argument {
            Argument::FunctionExpression(function) => {
                let body = function.body.as_ref()?;
                Some((&function.params, body.as_ref(), function.span, "function"))
            }
            Argument::ArrowFunctionExpression(function) => Some((
                &function.params,
                arrow_block_body(function)?,
                function.span,
                "arrow",
            )),
            Argument::ParenthesizedExpression(paren) => {
                Self::amd_factory_expression_parts(&paren.expression)
            }
            _ => None,
        }
    }

    fn amd_exports(
        &self,
        deps: &[String],
        params: &oxc_ast::ast::FormalParameters<'_>,
        body: &oxc_ast::ast::FunctionBody<'_>,
    ) -> (Vec<String>, bool) {
        let mut module_symbol = None;
        let mut exports_symbol = None;
        let mut require_symbol = None;
        for (index, dep) in deps.iter().enumerate() {
            let symbol = params
                .items
                .get(index)
                .and_then(|param| binding_symbol(&param.pattern));
            match dep.as_str() {
                "module" => module_symbol = symbol,
                "exports" => exports_symbol = symbol,
                "require" => require_symbol = symbol,
                _ => {}
            }
        }
        let mut collector = ExportCollector {
            scoping: self.scoping,
            module_symbol,
            exports_symbol,
            require_symbol,
            names: BTreeSet::new(),
            commonjs_export: false,
        };
        collector.visit_function_body(body);
        (
            collector.names.into_iter().collect(),
            collector.commonjs_export,
        )
    }

    fn amd_module_record(&self, call: &oxc_ast::ast::CallExpression<'_>) -> Option<ModuleRecord> {
        if call.arguments.len() < 2 {
            return None;
        }
        let Argument::StringLiteral(name) = call.arguments.first()? else {
            return None;
        };
        let (deps, factory_argument) = match call.arguments.get(1)? {
            Argument::ArrayExpression(dep_array) => {
                (Self::array_literal_ids(dep_array)?, call.arguments.get(2)?)
            }
            factory => (Vec::new(), factory),
        };
        let (params, body, span, value_kind) = Self::amd_factory_parts(factory_argument)?;
        let (export_names, commonjs_export) = self.amd_exports(&deps, params, body);
        let dependencies = deps
            .into_iter()
            .filter(|dep| !matches!(dep.as_str(), "require" | "exports" | "module"))
            .collect();
        Some(ModuleRecord {
            id: name.value.to_string(),
            property_start: call.span.start,
            property_end: call.span.end,
            value_start: span.start,
            value_end: span.end,
            value_kind: value_kind.to_string(),
            method: false,
            dependencies,
            dependency_map: BTreeMap::new(),
            export_names,
            commonjs_export,
        })
    }

    fn unresolved_global_path(&self, expr: &Expression<'_>) -> Option<String> {
        match expr {
            Expression::Identifier(id) if reference_symbol(self.scoping, id).is_none() => {
                Some(id.name.to_string())
            }
            Expression::StaticMemberExpression(member) => {
                let base = self.unresolved_global_path(&member.object)?;
                Some(format!("{base}.{}", member.property.name))
            }
            Expression::ComputedMemberExpression(member) => {
                let base = self.unresolved_global_path(&member.object)?;
                let property = computed_string(&member.expression)?;
                Some(format!("{base}.{property}"))
            }
            Expression::ParenthesizedExpression(paren) => {
                self.unresolved_global_path(&paren.expression)
            }
            _ => None,
        }
    }

    fn amd_member_receiver(&self, callee: &Expression<'_>) -> Option<(MemberReceiverKey, String)> {
        let object = match callee {
            Expression::StaticMemberExpression(member)
                if member.property.name.as_str() == "define" =>
            {
                &member.object
            }
            Expression::ComputedMemberExpression(member)
                if computed_string(&member.expression).as_deref() == Some("define") =>
            {
                &member.object
            }
            _ => return None,
        };
        let receiver = expression_symbol(self.scoping, object)
            .map(MemberReceiverKey::Local)
            .or_else(|| {
                self.unresolved_global_path(object)
                    .map(MemberReceiverKey::Global)
            })?;
        Some((receiver, self.fragment(callee.span()).trim().to_string()))
    }

    fn record_amd_call(&mut self, call: &oxc_ast::ast::CallExpression<'_>) -> bool {
        let Some(record) = self.amd_module_record(call) else {
            return false;
        };
        match &call.callee {
            Expression::Identifier(callee) if callee.name.as_str() == "define" => {
                let define_is_resolved = reference_symbol(self.scoping, callee).is_some();
                if define_is_resolved
                    && !matches!(
                        call.arguments.get(1),
                        Some(Argument::ArrayExpression(dep_array))
                            if matches!(
                                Self::array_literal_ids(dep_array).as_deref(),
                                Some([first, second, ..])
                                    if first == "require" && second == "exports"
                            )
                    )
                {
                    return false;
                }
                self.amd_start = Some(
                    self.amd_start
                        .map_or(call.span.start, |old| old.min(call.span.start)),
                );
                self.amd_end = Some(
                    self.amd_end
                        .map_or(call.span.end, |old| old.max(call.span.end)),
                );
                self.amd_modules.push(record);
            }
            _ => {
                let Some((symbol, callee)) = self.amd_member_receiver(&call.callee) else {
                    return false;
                };
                let has_dependency_array =
                    matches!(call.arguments.get(1), Some(Argument::ArrayExpression(_)));
                let group =
                    self.amd_member_groups
                        .entry(symbol)
                        .or_insert_with(|| AmdMemberGroup {
                            callee,
                            start: call.span.start,
                            end: call.span.end,
                            explicit_dependency_arrays: 0,
                            modules: Vec::new(),
                        });
                group.start = group.start.min(call.span.start);
                group.end = group.end.max(call.span.end);
                group.explicit_dependency_arrays += usize::from(has_dependency_array);
                group.modules.push(record);
            }
        }
        true
    }

    fn record_amd_loader_assignment(&mut self, assign: &oxc_ast::ast::AssignmentExpression<'_>) {
        let (object, property) = match &assign.left {
            AssignmentTarget::StaticMemberExpression(member) => {
                (&member.object, Some(member.property.name.to_string()))
            }
            AssignmentTarget::ComputedMemberExpression(member) => {
                (&member.object, computed_string(&member.expression))
            }
            _ => return,
        };
        let Some(property) = property else {
            return;
        };
        let Some(symbol) = expression_symbol(self.scoping, object) else {
            return;
        };
        let evidence = self.amd_loader_evidence.entry(symbol).or_default();
        match property.as_str() {
            "define" => evidence.define_assignment = true,
            "require" => evidence.require_assignment = true,
            "requirejs" => evidence.requirejs_assignment = true,
            "loadModules" => evidence.load_modules_assignment = true,
            _ => {}
        }
    }

    fn module_dependencies(&self, value: &Expression<'_>) -> Vec<String> {
        let value = unwrap_parenthesized(value);
        let (params, body) = match value {
            Expression::FunctionExpression(function) => {
                let Some(body) = function.body.as_ref() else {
                    return Vec::new();
                };
                (&function.params, body.as_ref())
            }
            Expression::ArrowFunctionExpression(function) => {
                let Some(body) = arrow_block_body(function) else {
                    return Vec::new();
                };
                (&function.params, body)
            }
            _ => return Vec::new(),
        };
        let Some(require_symbol) = params
            .items
            .get(2)
            .and_then(|param| binding_symbol(&param.pattern))
        else {
            return Vec::new();
        };
        let mut collector = DependencyCollector {
            scoping: self.scoping,
            require_symbol,
            dependencies: BTreeSet::new(),
        };
        collector.visit_function_body(body);
        collector.dependencies.into_iter().collect()
    }

    fn module_exports(&self, value: &Expression<'_>) -> (Vec<String>, bool) {
        let value = unwrap_parenthesized(value);
        let (params, body) = match value {
            Expression::FunctionExpression(function) => {
                let Some(body) = function.body.as_ref() else {
                    return (Vec::new(), false);
                };
                (&function.params, body.as_ref())
            }
            Expression::ArrowFunctionExpression(function) => {
                let Some(body) = arrow_block_body(function) else {
                    return (Vec::new(), false);
                };
                (&function.params, body)
            }
            _ => return (Vec::new(), false),
        };
        let module_symbol = params
            .items
            .first()
            .and_then(|param| binding_symbol(&param.pattern));
        let exports_symbol = params
            .items
            .get(1)
            .and_then(|param| binding_symbol(&param.pattern));
        let require_symbol = params
            .items
            .get(2)
            .and_then(|param| binding_symbol(&param.pattern));
        let mut collector = ExportCollector {
            scoping: self.scoping,
            module_symbol,
            exports_symbol,
            require_symbol,
            names: BTreeSet::new(),
            commonjs_export: false,
        };
        collector.visit_function_body(body);
        (
            collector.names.into_iter().collect(),
            collector.commonjs_export,
        )
    }

    fn module_records(
        &self,
        module_table: &oxc_ast::ast::ObjectExpression<'_>,
    ) -> Option<Vec<ModuleRecord>> {
        let mut modules = Vec::with_capacity(module_table.properties.len());
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return None;
            };
            if prop.computed || prop.kind != oxc_ast::ast::PropertyKind::Init {
                return None;
            }
            let id = Self::property_key(&prop.key)?;
            let value = unwrap_parenthesized(&prop.value);
            let (value_kind, span) = match value {
                Expression::FunctionExpression(f) => ("function", f.span),
                Expression::ArrowFunctionExpression(f) => ("arrow", f.span),
                _ => return None,
            };
            let dependencies = self.module_dependencies(value);
            let (export_names, commonjs_export) = self.module_exports(value);
            modules.push(ModuleRecord {
                id,
                property_start: prop.span.start,
                property_end: prop.span.end,
                value_start: span.start,
                value_end: span.end,
                value_kind: value_kind.to_string(),
                method: prop.method,
                dependencies,
                dependency_map: BTreeMap::new(),
                export_names,
                commonjs_export,
            });
        }
        (!modules.is_empty()).then_some(modules)
    }

    fn browserify_dependency_map(
        dependency_map: &oxc_ast::ast::ObjectExpression<'_>,
    ) -> Option<BTreeMap<String, String>> {
        let mut dependencies = BTreeMap::new();
        for item in &dependency_map.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return None;
            };
            if prop.computed || prop.kind != oxc_ast::ast::PropertyKind::Init {
                return None;
            }
            let name = Self::property_key(&prop.key)?;
            let target = match unwrap_parenthesized(&prop.value) {
                Expression::NumericLiteral(value)
                    if value.value.is_finite() && value.value.fract() == 0.0 =>
                {
                    format!("{:.0}", value.value)
                }
                Expression::StringLiteral(value) => value.value.to_string(),
                _ => return None,
            };
            dependencies.insert(name, target);
        }
        Some(dependencies)
    }

    fn browserify_factory_parts<'a>(
        element: &'a ArrayExpressionElement<'a>,
    ) -> Option<(
        &'a oxc_ast::ast::FormalParameters<'a>,
        &'a oxc_ast::ast::FunctionBody<'a>,
        oxc_span::Span,
        &'static str,
    )> {
        match element {
            ArrayExpressionElement::FunctionExpression(function) => {
                let body = function.body.as_ref()?;
                Some((&function.params, body.as_ref(), function.span, "function"))
            }
            ArrayExpressionElement::ArrowFunctionExpression(function) => Some((
                &function.params,
                arrow_block_body(function)?,
                function.span,
                "arrow",
            )),
            _ => None,
        }
    }

    fn browserify_exports(
        &self,
        params: &oxc_ast::ast::FormalParameters<'_>,
        body: &oxc_ast::ast::FunctionBody<'_>,
    ) -> (Vec<String>, bool) {
        // Browserify factory ABI: (require, module, exports).
        let require_symbol = params
            .items
            .first()
            .and_then(|param| binding_symbol(&param.pattern));
        let module_symbol = params
            .items
            .get(1)
            .and_then(|param| binding_symbol(&param.pattern));
        let exports_symbol = params
            .items
            .get(2)
            .and_then(|param| binding_symbol(&param.pattern));
        let mut collector = ExportCollector {
            scoping: self.scoping,
            module_symbol,
            exports_symbol,
            require_symbol,
            names: BTreeSet::new(),
            commonjs_export: false,
        };
        collector.visit_function_body(body);
        (
            collector.names.into_iter().collect(),
            collector.commonjs_export,
        )
    }

    fn browserify_module_records(
        &self,
        module_table: &oxc_ast::ast::ObjectExpression<'_>,
    ) -> Option<Vec<ModuleRecord>> {
        if module_table.properties.len() < 2 {
            return None;
        }
        let mut modules = Vec::with_capacity(module_table.properties.len());
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return None;
            };
            if prop.computed || prop.kind != oxc_ast::ast::PropertyKind::Init {
                return None;
            }
            let id = Self::property_key(&prop.key)?;
            let Expression::ArrayExpression(pair) = unwrap_parenthesized(&prop.value) else {
                return None;
            };
            if pair.elements.len() != 2 {
                return None;
            }
            let (params, body, span, value_kind) =
                Self::browserify_factory_parts(&pair.elements[0])?;
            if params.items.len() < 3 {
                return None;
            }
            let ArrayExpressionElement::ObjectExpression(dependency_object) = &pair.elements[1]
            else {
                return None;
            };
            let dependency_map = Self::browserify_dependency_map(dependency_object)?;
            let (export_names, commonjs_export) = self.browserify_exports(params, body);
            modules.push(ModuleRecord {
                id,
                property_start: prop.span.start,
                property_end: prop.span.end,
                value_start: span.start,
                value_end: span.end,
                value_kind: value_kind.to_string(),
                method: prop.method,
                dependencies: Vec::new(),
                dependency_map,
                export_names,
                commonjs_export,
            });
        }
        let module_ids = modules
            .iter()
            .map(|module| module.id.clone())
            .collect::<HashSet<_>>();
        for module in &mut modules {
            module.dependencies = module
                .dependency_map
                .values()
                .filter(|dependency| module_ids.contains(dependency.as_str()))
                .cloned()
                .collect::<BTreeSet<_>>()
                .into_iter()
                .collect();
        }
        Some(modules)
    }

    fn browserify_bootstrap_arity(callee: &Expression<'_>) -> Option<usize> {
        match unwrap_parenthesized(callee) {
            Expression::FunctionExpression(function) => Some(function.params.items.len()),
            Expression::ArrowFunctionExpression(function) => Some(function.params.items.len()),
            _ => None,
        }
    }

    fn record_browserify_call(&mut self, call: &oxc_ast::ast::CallExpression<'_>) -> bool {
        if call.arguments.len() != 3 || Self::browserify_bootstrap_arity(&call.callee) != Some(3) {
            return false;
        }
        let Some(Argument::ObjectExpression(module_table)) = call.arguments.first() else {
            return false;
        };
        let Some(Argument::ObjectExpression(cache)) = call.arguments.get(1) else {
            return false;
        };
        if !cache.properties.is_empty() {
            return false;
        }
        let Some(Argument::ArrayExpression(entries)) = call.arguments.get(2) else {
            return false;
        };
        let Some(entry_ids) = Self::array_literal_ids(entries) else {
            return false;
        };
        if entry_ids.is_empty() {
            return false;
        }
        let Some(modules) = self.browserify_module_records(module_table) else {
            return false;
        };
        let module_ids = modules
            .iter()
            .map(|module| module.id.clone())
            .collect::<HashSet<_>>();
        if entry_ids
            .iter()
            .any(|entry| !module_ids.contains(entry.as_str()))
        {
            return false;
        }
        self.bundles.push(BundleRecord {
            kind: "browserify_module_table".into(),
            start: call.span.start,
            end: call.span.end,
            callee: "<browserify-bootstrap>".into(),
            chunk_ids: Vec::new(),
            module_table_start: module_table.span.start,
            module_table_end: module_table.span.end,
            modules,
        });
        true
    }

    fn direct_table_is_webpack_like(
        module_table: &oxc_ast::ast::ObjectExpression<'_>,
        modules: &[ModuleRecord],
    ) -> bool {
        if modules.len() < 16
            || modules
                .iter()
                .any(|m| !m.id.bytes().all(|b| b.is_ascii_digit()))
        {
            return false;
        }

        let mut conventional_arity = 0usize;
        for item in &module_table.properties {
            let ObjectPropertyKind::ObjectProperty(prop) = item else {
                return false;
            };
            let arity = match unwrap_parenthesized(&prop.value) {
                Expression::FunctionExpression(f) => f.params.items.len(),
                Expression::ArrowFunctionExpression(f) => f.params.items.len(),
                _ => return false,
            };
            if (2..=3).contains(&arity) {
                conventional_arity += 1;
            }
        }

        conventional_arity * 4 >= modules.len() * 3
    }

    fn record_object(&mut self, module_table: &oxc_ast::ast::ObjectExpression<'_>) {
        let Some(modules) = self.module_records(module_table) else {
            return;
        };
        if !Self::direct_table_is_webpack_like(module_table, &modules) {
            return;
        }
        self.bundles.push(BundleRecord {
            kind: "webpack_module_table".into(),
            start: module_table.span.start,
            end: module_table.span.end,
            callee: "<direct-object-module-table>".into(),
            chunk_ids: Vec::new(),
            module_table_start: module_table.span.start,
            module_table_end: module_table.span.end,
            modules,
        });
    }

    fn record_call(&mut self, call: &oxc_ast::ast::CallExpression<'_>) {
        if self.record_browserify_call(call) {
            return;
        }
        if self.record_amd_call(call) {
            return;
        }
        let callee = self.fragment(call.callee.span()).trim().to_string();
        if !(callee.ends_with(".push")
            || callee.ends_with("['push']")
            || callee.ends_with("[\"push\"]"))
        {
            return;
        }
        let Some(Argument::ArrayExpression(payload)) = call.arguments.first() else {
            return;
        };
        if payload.elements.len() < 2 {
            return;
        }
        let ArrayExpressionElement::ArrayExpression(chunk_ids_expr) = &payload.elements[0] else {
            return;
        };
        let Some(chunk_ids) = Self::array_literal_ids(chunk_ids_expr) else {
            return;
        };
        if chunk_ids.is_empty() {
            return;
        }
        let ArrayExpressionElement::ObjectExpression(module_table) = &payload.elements[1] else {
            return;
        };

        // A Webpack/Next JSONP payload module table is overwhelmingly
        // function-valued. Reject generic or partially dynamic object pushes.
        let Some(modules) = self.module_records(module_table) else {
            return;
        };

        self.bundles.push(BundleRecord {
            kind: "webpack_chunk_push".into(),
            start: call.span.start,
            end: call.span.end,
            callee,
            chunk_ids,
            module_table_start: module_table.span.start,
            module_table_end: module_table.span.end,
            modules,
        });
    }
}

impl<'a> Visit<'a> for Collector<'_, '_> {
    fn enter_node(&mut self, kind: AstKind<'a>) {
        match kind {
            AstKind::AssignmentExpression(assign) => self.record_amd_loader_assignment(assign),
            AstKind::CallExpression(call) => self.record_call(call),
            AstKind::ObjectExpression(object) => self.record_object(object),
            _ => {}
        }
    }

    fn visit_program(&mut self, it: &oxc_ast::ast::Program<'a>) {
        walk::walk_program(self, it);
    }
}

fn parse<'a>(
    allocator: &'a Allocator,
    source: &'a str,
    source_type: SourceType,
) -> rolldown_redox::ecmascript::ParseOutcome<'a> {
    parse_program(allocator, source, source_type)
}

fn main() -> Result<()> {
    let args = Args::parse();
    let source = fs::read_to_string(&args.input)
        .with_context(|| format!("reading {}", args.input.display()))?;
    let allocator = Allocator::default();
    let mut parsed = parse(&allocator, &source, SourceType::mjs());
    if parsed.fatal_error {
        parsed = parse(&allocator, &source, SourceType::cjs());
    }

    let mut diagnostics = parsed.diagnostics;
    let fatal_error = parsed.fatal_error;
    let mut bundles = if !fatal_error {
        let semantic_ret = SemanticBuilder::new()
            .with_check_syntax_error(true)
            .build(&parsed.program);
        diagnostics += semantic_ret.diagnostics.len();
        let semantic = semantic_ret.semantic;
        let mut collector = Collector {
            source: &source,
            scoping: semantic.scoping(),
            bundles: Vec::new(),
            amd_modules: Vec::new(),
            amd_start: None,
            amd_end: None,
            amd_member_groups: HashMap::new(),
            amd_loader_evidence: HashMap::new(),
        };
        collector.visit_program(&parsed.program);
        if !collector.amd_modules.is_empty() {
            let start = collector.amd_start.unwrap_or_default();
            let end = collector.amd_end.unwrap_or(start);
            collector.bundles.push(BundleRecord {
                kind: "amd_named_modules".into(),
                start,
                end,
                callee: "define".into(),
                chunk_ids: Vec::new(),
                module_table_start: start,
                module_table_end: end,
                modules: std::mem::take(&mut collector.amd_modules),
            });
        }
        let mut member_groups = std::mem::take(&mut collector.amd_member_groups)
            .into_iter()
            .filter_map(|(receiver, group)| {
                let proven = match receiver {
                    MemberReceiverKey::Global(_) => group.explicit_dependency_arrays > 0,
                    MemberReceiverKey::Local(symbol) => collector
                        .amd_loader_evidence
                        .get(&symbol)
                        .is_some_and(|evidence| {
                            evidence.define_assignment
                                && ((evidence.require_assignment
                                    && (evidence.requirejs_assignment || group.modules.len() >= 2))
                                    || (evidence.load_modules_assignment
                                        && group.modules.len() >= 2))
                        }),
                };
                proven.then_some(group)
            })
            .collect::<Vec<_>>();
        member_groups.sort_by_key(|group| group.start);
        for group in member_groups {
            collector.bundles.push(BundleRecord {
                kind: "member_named_modules".into(),
                start: group.start,
                end: group.end,
                callee: group.callee,
                chunk_ids: Vec::new(),
                module_table_start: group.start,
                module_table_end: group.end,
                modules: group.modules,
            });
        }
        collector.bundles
    } else {
        Vec::new()
    };

    // The object inside a JSONP chunk push also satisfies the direct-table
    // shape. Prefer the richer chunk-push record when both describe the same
    // table.
    let pushed_tables = bundles
        .iter()
        .filter(|bundle| bundle.kind == "webpack_chunk_push")
        .map(|bundle| (bundle.module_table_start, bundle.module_table_end))
        .collect::<HashSet<_>>();
    bundles.retain(|bundle| {
        bundle.kind != "webpack_module_table"
            || !pushed_tables.contains(&(bundle.module_table_start, bundle.module_table_end))
    });
    bundles.sort_by_key(|b| b.start);

    let report = Report {
        schema: "js-bundle-inventory/v5",
        input: args.input.display().to_string(),
        diagnostics,
        fatal_error,
        bundles,
    };
    println!("{}", serde_json::to_string(&report)?);
    Ok(())
}
