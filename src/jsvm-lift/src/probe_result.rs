//! The outcome of an AST visitor that is looking for one specific site.
//!
//! A target not encountered, a target encountered but not proven, and a
//! proven value are distinct states during traversal. Callers which expose
//! only a proven value can then deliberately collapse the other two cases.

/// One-shot structural/evidence lookup in an AST.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum ProbeResult<T> {
    /// The visitor has not yet encountered the requested site.
    NotVisited,
    /// The requested site was seen, but the requested evidence was not proven.
    Unproven,
    /// The requested site was seen and its evidence was proven.
    Proven(T),
}

impl<T> Default for ProbeResult<T> {
    fn default() -> Self {
        Self::NotVisited
    }
}

impl<T> ProbeResult<T> {
    pub(crate) fn resolve(proof: Option<T>) -> Self {
        match proof {
            Some(proof) => Self::Proven(proof),
            None => Self::Unproven,
        }
    }

    pub(crate) fn is_decided(&self) -> bool {
        !matches!(self, Self::NotVisited)
    }

    pub(crate) fn into_proven(self) -> Option<T> {
        match self {
            Self::Proven(value) => Some(value),
            Self::NotVisited | Self::Unproven => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::ProbeResult;

    #[test]
    fn a_rejected_site_stops_search_without_creating_proof() {
        let mut result = ProbeResult::<u32>::default();
        assert!(!result.is_decided());
        result = ProbeResult::resolve(None);
        assert!(result.is_decided());
        assert_eq!(result.into_proven(), None);
    }

    #[test]
    fn a_proven_site_preserves_its_value() {
        let result = ProbeResult::resolve(Some(false));
        assert!(result.is_decided());
        assert_eq!(result.into_proven(), Some(false));
    }
}
