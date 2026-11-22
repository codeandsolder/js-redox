//! Synthetic class-definition timing, abrupt completion and key semantics.
use super::compare_sources;
use anyhow::Result;

#[test]
#[ignore = "requires Node; semantic CI invokes explicitly"]
fn depythonify_safe_deob_literal_class_definition_runtime_equivalence() -> Result<()> {
    compare_sources(
        "literal-class-definition",
        [
            "function effect(x){events.push(x);return x} events.push(typeof(class {field=effect('instance');#x=effect('private');m(){effect('method')}}));",
            "function effect(x){events.push(x);return x} events.push(typeof(class extends null {}),typeof(class extends function(){effect('constructor')} {}),typeof(class extends (class{}) {}));",
            "events.push(typeof(class { static [2 ** 1.5]=1; static ['name']=1 }),typeof(class {static ['__proto__']=null}));",
            "function effect(x){events.push(x);return x} events.push(typeof(class {static [effect('key1')]=effect('value1');[effect('key2')](){} static {effect('block')}}));",
            "function effect(x){events.push(x);return x} try{typeof(class {static ['prototype']=effect('initializer');[effect('later-key')](){}})}catch(e){events.push(e.name)}",
            "function effect(x){events.push(x);return x} try{typeof(class {static ['prototype'](){};[effect('later-key')](){}})}catch(e){events.push(e.name)}",
            "try{typeof(class extends (()=>{}) {})}catch(e){events.push(e.name)} try{typeof(class extends 1 {})}catch(e){events.push(e.name)} typeof(class {static {; {2 ** 1.5;}}});",
            "function effect(x){events.push(x);return x} let k={toString(){return effect('coercion')}}; events.push(typeof(class {[k](){};static #x=effect('private')}));",
        ].into_iter().map(str::to_owned).collect(),
    )
}
