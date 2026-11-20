//! Regression for oxc-project/oxc#29927; retain after removing the backport.
use oxc_compat::{BabelTargets, EngineTargets};
use serde_json::json;

#[test]
fn unsupported_babel_targets_are_not_silently_ignored() -> Result<(), serde_json::Error> {
    for targets in [
        json!({"edge": "100", "esmodules": true}),
        json!({"edge": "100", "browsers": ["defaults"]}),
        json!({"edge": "100", "chrome": 120}),
        json!({"edge": "100", "firefox": 120.5}),
        json!({"edge": "100", "node": "current"}),
        json!({"edge": "100", "safari": "tp"}),
    ] {
        let parsed: BabelTargets = serde_json::from_value(targets.clone())?;
        assert!(EngineTargets::try_from(parsed).is_err(), "{targets}");
    }
    let supported: BabelTargets = serde_json::from_value(json!({"edge": "100"}))?;
    assert!(EngineTargets::try_from(supported).is_ok());
    Ok(())
}
