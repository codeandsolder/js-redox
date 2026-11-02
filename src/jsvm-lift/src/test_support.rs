use std::{
    error::Error,
    fmt::{self, Debug, Display},
};

#[derive(Debug)]
pub(crate) struct TestFailure {
    context: &'static str,
    detail: String,
}

impl TestFailure {
    fn missing(context: &'static str) -> Self {
        Self {
            context,
            detail: "value was absent".to_string(),
        }
    }

    fn error(context: &'static str, error: impl Debug) -> Self {
        Self {
            context,
            detail: format!("{error:?}"),
        }
    }
}

impl Display for TestFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{}: {}", self.context, self.detail)
    }
}

impl Error for TestFailure {}

pub(crate) type TestResult = Result<(), TestFailure>;

pub(crate) trait TestValue<T> {
    fn test_value(self, context: &'static str) -> Result<T, TestFailure>;
}

impl<T> TestValue<T> for Option<T> {
    fn test_value(self, context: &'static str) -> Result<T, TestFailure> {
        self.ok_or_else(|| TestFailure::missing(context))
    }
}

impl<T, E: Debug> TestValue<T> for Result<T, E> {
    fn test_value(self, context: &'static str) -> Result<T, TestFailure> {
        self.map_err(|error| TestFailure::error(context, error))
    }
}
