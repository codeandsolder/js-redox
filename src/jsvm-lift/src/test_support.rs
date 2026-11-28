use std::{
    error::Error,
    fmt::{self, Debug, Display},
    path::PathBuf,
};

#[derive(Debug)]
pub struct TestFailure {
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

pub type TestResult = Result<(), TestFailure>;

pub trait TestValue<T> {
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

pub fn source_slice<'a>(
    source: &'a str,
    start: u32,
    end: u32,
    context: &'static str,
) -> Result<&'a str, TestFailure> {
    let start = usize::try_from(start).map_err(|error| TestFailure::error(context, error))?;
    let end = usize::try_from(end).map_err(|error| TestFailure::error(context, error))?;
    source.get(start..end).test_value(context)
}

pub fn source_offset(
    source: &str,
    needle: &str,
    context: &'static str,
) -> Result<u32, TestFailure> {
    let offset = source.find(needle).test_value(context)?;
    u32::try_from(offset).map_err(|error| TestFailure::error(context, error))
}

pub fn source_rfind(source: &str, needle: &str, context: &'static str) -> Result<u32, TestFailure> {
    let offset = source.rfind(needle).test_value(context)?;
    u32::try_from(offset).map_err(|error| TestFailure::error(context, error))
}

pub fn source_span(
    source: &str,
    needle: &str,
    context: &'static str,
) -> Result<oxc_span::Span, TestFailure> {
    let start = source_offset(source, needle, context)?;
    let len = u32::try_from(needle.len()).map_err(|error| TestFailure::error(context, error))?;
    let end = start.checked_add(len).test_value(context)?;
    Ok(oxc_span::Span::new(start, end))
}

/// Locate fixtures from the executing test's working tree, rather than a
/// compile-time manifest path that may belong to a remote build sandbox.
pub fn workspace_root() -> Result<PathBuf, TestFailure> {
    let cwd = std::env::current_dir().test_value("test working directory")?;
    cwd.ancestors()
        .find(|path| path.join("Cargo.toml").is_file() && path.join("corpus/generated").is_dir())
        .map(std::path::Path::to_path_buf)
        .test_value("js-redox workspace containing generated fixtures")
}
