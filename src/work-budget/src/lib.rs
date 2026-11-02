//! Cooperative, hierarchical work budgets for analysis of untrusted inputs.
//!
//! A [`WorkBudget`] is cheap to clone and safe to share across threads. Child
//! budgets inherit every ancestor constraint while adding their own tighter
//! deadline and/or deterministic work allowance. Algorithms should checkpoint
//! at natural progress boundaries and charge deterministic work where a useful
//! unit exists.

use std::{
    error::Error,
    fmt,
    io::{self, Read},
    process::{Command, Output, Stdio},
    sync::{
        atomic::{AtomicU64, AtomicU8, Ordering},
        Arc, Mutex,
    },
    thread,
    time::{Duration, Instant},
};

const ACTIVE: u8 = 0;
const DEADLINE_EXCEEDED: u8 = 1;
const WORK_EXCEEDED: u8 = 2;
const CANCELLED: u8 = 3;

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct BudgetLimits {
    pub wall_time: Option<Duration>,
    pub work: Option<u64>,
}

impl BudgetLimits {
    #[must_use]
    pub const fn unlimited() -> Self {
        Self {
            wall_time: None,
            work: None,
        }
    }

    #[must_use]
    pub const fn wall_time(wall_time: Duration) -> Self {
        Self {
            wall_time: Some(wall_time),
            work: None,
        }
    }

    #[must_use]
    pub const fn work(work: u64) -> Self {
        Self {
            wall_time: None,
            work: Some(work),
        }
    }

    #[must_use]
    pub const fn with_wall_time(mut self, wall_time: Duration) -> Self {
        self.wall_time = Some(wall_time);
        self
    }

    #[must_use]
    pub const fn with_work(mut self, work: u64) -> Self {
        self.work = Some(work);
        self
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BudgetExceededKind {
    Deadline,
    Work,
    Cancelled,
}

impl fmt::Display for BudgetExceededKind {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Deadline => formatter.write_str("deadline exceeded"),
            Self::Work => formatter.write_str("work allowance exhausted"),
            Self::Cancelled => formatter.write_str("cancelled"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct BudgetExceeded {
    scope: Arc<str>,
    kind: BudgetExceededKind,
    elapsed: Duration,
    work_limit: Option<u64>,
    work_consumed: Option<u64>,
    inherited: bool,
}

impl BudgetExceeded {
    #[must_use]
    pub fn scope(&self) -> &str {
        &self.scope
    }

    #[must_use]
    pub const fn kind(&self) -> BudgetExceededKind {
        self.kind
    }

    #[must_use]
    pub const fn elapsed(&self) -> Duration {
        self.elapsed
    }

    #[must_use]
    pub const fn work_limit(&self) -> Option<u64> {
        self.work_limit
    }

    #[must_use]
    pub const fn work_consumed(&self) -> Option<u64> {
        self.work_consumed
    }

    /// Whether the exhausted constraint belongs to an ancestor of the budget
    /// that observed it, rather than the observing operation's local scope.
    #[must_use]
    pub const fn is_inherited(&self) -> bool {
        self.inherited
    }

    /// Whether the exhausted constraint belongs to the budget scope that
    /// observed it rather than one of its ancestors.
    #[must_use]
    pub const fn is_local(&self) -> bool {
        !self.inherited
    }

    fn with_inherited(mut self, inherited: bool) -> Self {
        self.inherited = inherited;
        self
    }
}

impl fmt::Display for BudgetExceeded {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "work budget {} in {:?} after {:?}",
            self.kind, self.scope, self.elapsed
        )?;
        if let (Some(consumed), Some(limit)) = (self.work_consumed, self.work_limit) {
            write!(formatter, " ({consumed}/{limit} work units consumed)")?;
        }
        Ok(())
    }
}

impl Error for BudgetExceeded {}

#[derive(Debug)]
pub enum CommandRunError {
    Spawn(io::Error),
    Wait(io::Error),
    Output(io::Error),
    Budget(BudgetExceeded),
}

impl fmt::Display for CommandRunError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Spawn(error) => write!(formatter, "spawning child process: {error}"),
            Self::Wait(error) => write!(formatter, "waiting for child process: {error}"),
            Self::Output(error) => write!(formatter, "reading child process output: {error}"),
            Self::Budget(error) => error.fmt(formatter),
        }
    }
}

impl Error for CommandRunError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Spawn(error) | Self::Wait(error) | Self::Output(error) => Some(error),
            Self::Budget(error) => Some(error),
        }
    }
}

impl CommandRunError {
    #[must_use]
    pub const fn budget(&self) -> Option<&BudgetExceeded> {
        match self {
            Self::Budget(error) => Some(error),
            _ => None,
        }
    }

    #[must_use]
    pub const fn spawn_io_error(&self) -> Option<&io::Error> {
        match self {
            Self::Spawn(error) => Some(error),
            _ => None,
        }
    }
}

fn join_output_reader(
    handle: thread::JoinHandle<io::Result<Vec<u8>>>,
) -> Result<Vec<u8>, CommandRunError> {
    match handle.join() {
        Ok(result) => result.map_err(CommandRunError::Output),
        Err(_) => Err(CommandRunError::Output(io::Error::other(
            "child output reader thread panicked",
        ))),
    }
}

/// Run a child process under the same cooperative budget used by in-process
/// analysis.
///
/// `stdout` and `stderr` are drained concurrently so a verbose child cannot
/// deadlock on full pipes. The child is killed and reaped when the budget is
/// exhausted or cancelled. The budget is checked at most 10 ms apart while
/// the child is running.
pub fn run_command(command: &mut Command, budget: &WorkBudget) -> Result<Output, CommandRunError> {
    budget.checkpoint().map_err(CommandRunError::Budget)?;
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().map_err(CommandRunError::Spawn)?;
    let stdout = child.stdout.take().ok_or_else(|| {
        CommandRunError::Output(io::Error::other("child stdout pipe was not created"))
    })?;
    let stderr = child.stderr.take().ok_or_else(|| {
        CommandRunError::Output(io::Error::other("child stderr pipe was not created"))
    })?;
    let stdout_reader = thread::spawn(move || {
        let mut reader = stdout;
        let mut output = Vec::new();
        reader.read_to_end(&mut output)?;
        Ok(output)
    });
    let stderr_reader = thread::spawn(move || {
        let mut reader = stderr;
        let mut output = Vec::new();
        reader.read_to_end(&mut output)?;
        Ok(output)
    });

    let status = loop {
        if let Err(error) = budget.checkpoint() {
            let _ = child.kill();
            let _ = child.wait();
            let _ = join_output_reader(stdout_reader);
            let _ = join_output_reader(stderr_reader);
            return Err(CommandRunError::Budget(error));
        }
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => thread::sleep(Duration::from_millis(10)),
            Err(error) => {
                let _ = child.kill();
                let _ = child.wait();
                let _ = join_output_reader(stdout_reader);
                let _ = join_output_reader(stderr_reader);
                return Err(CommandRunError::Wait(error));
            }
        }
    };

    let stdout = join_output_reader(stdout_reader)?;
    let stderr = join_output_reader(stderr_reader)?;
    budget.checkpoint().map_err(CommandRunError::Budget)?;
    Ok(Output {
        status,
        stdout,
        stderr,
    })
}

#[derive(Debug)]
struct BudgetState {
    scope: Arc<str>,
    started: Instant,
    deadline: Option<Instant>,
    work_limit: Option<u64>,
    remaining_work: AtomicU64,
    status: AtomicU8,
}

impl BudgetState {
    fn new(scope: Arc<str>, limits: BudgetLimits) -> Self {
        let started = Instant::now();
        // An unrepresentably distant deadline is effectively unbounded. Treating
        // `Instant` overflow as `started` would turn a huge allowance into an
        // immediate timeout.
        let deadline = limits
            .wall_time
            .and_then(|duration| started.checked_add(duration));
        Self {
            scope,
            started,
            deadline,
            work_limit: limits.work,
            remaining_work: AtomicU64::new(limits.work.unwrap_or(0)),
            status: AtomicU8::new(ACTIVE),
        }
    }

    fn exceeded(&self, kind: BudgetExceededKind, now: Instant) -> BudgetExceeded {
        let work_consumed = self.work_limit.map(|limit| {
            let remaining = self.remaining_work.load(Ordering::Relaxed).min(limit);
            limit - remaining
        });
        BudgetExceeded {
            scope: Arc::clone(&self.scope),
            kind,
            elapsed: now.saturating_duration_since(self.started),
            work_limit: self.work_limit,
            work_consumed,
            inherited: false,
        }
    }

    fn status_error(&self, now: Instant) -> Option<BudgetExceeded> {
        let kind = match self.status.load(Ordering::Acquire) {
            ACTIVE => return None,
            DEADLINE_EXCEEDED => BudgetExceededKind::Deadline,
            WORK_EXCEEDED => BudgetExceededKind::Work,
            CANCELLED => BudgetExceededKind::Cancelled,
            _ => BudgetExceededKind::Cancelled,
        };
        Some(self.exceeded(kind, now))
    }

    fn checkpoint(&self, now: Instant) -> Result<(), BudgetExceeded> {
        if let Some(error) = self.status_error(now) {
            return Err(error);
        }
        if self.deadline.is_some_and(|deadline| now >= deadline) {
            let _ = self.status.compare_exchange(
                ACTIVE,
                DEADLINE_EXCEEDED,
                Ordering::AcqRel,
                Ordering::Acquire,
            );
            if let Some(error) = self.status_error(now) {
                return Err(error);
            }
            return Err(self.exceeded(BudgetExceededKind::Deadline, now));
        }
        Ok(())
    }

    fn ensure_work_available(&self, units: u64, now: Instant) -> Result<(), BudgetExceeded> {
        self.checkpoint(now)?;
        if units == 0 || self.work_limit.is_none() {
            return Ok(());
        }
        if self.remaining_work.load(Ordering::Acquire) < units {
            let _ = self.status.compare_exchange(
                ACTIVE,
                WORK_EXCEEDED,
                Ordering::AcqRel,
                Ordering::Acquire,
            );
            if let Some(error) = self.status_error(now) {
                return Err(error);
            }
            return Err(self.exceeded(BudgetExceededKind::Work, now));
        }
        Ok(())
    }

    fn charge_work(&self, units: u64) {
        if units == 0 || self.work_limit.is_none() {
            return;
        }
        let previous = self.remaining_work.fetch_sub(units, Ordering::AcqRel);
        debug_assert!(previous >= units);
    }
}

/// A hierarchical cooperative budget.
///
/// Each child stores its own constraint plus the inherited ancestor constraints.
/// A checkpoint or work charge must satisfy every constraint in the chain.
#[derive(Debug, Clone)]
pub struct WorkBudget {
    states: Arc<[Arc<BudgetState>]>,
    charge_lock: Arc<Mutex<()>>,
}

impl WorkBudget {
    #[must_use]
    pub fn new(scope: impl Into<Arc<str>>, limits: BudgetLimits) -> Self {
        Self {
            states: Arc::from([Arc::new(BudgetState::new(scope.into(), limits))]),
            charge_lock: Arc::new(Mutex::new(())),
        }
    }

    #[must_use]
    pub fn unlimited(scope: impl Into<Arc<str>>) -> Self {
        Self::new(scope, BudgetLimits::unlimited())
    }

    #[must_use]
    pub fn child(&self, scope: impl Into<Arc<str>>, limits: BudgetLimits) -> Self {
        let mut states = self.states.iter().cloned().collect::<Vec<_>>();
        states.push(Arc::new(BudgetState::new(scope.into(), limits)));
        Self {
            states: Arc::from(states),
            charge_lock: Arc::clone(&self.charge_lock),
        }
    }

    /// Check cancellation/deadline constraints without charging deterministic work.
    pub fn checkpoint(&self) -> Result<(), BudgetExceeded> {
        let now = Instant::now();
        for (index, state) in self.states.iter().enumerate() {
            if let Err(error) = state.checkpoint(now) {
                return Err(error.with_inherited(index + 1 < self.states.len()));
            }
        }
        Ok(())
    }

    /// Charge deterministic work against every bounded scope in the hierarchy.
    ///
    /// The charge is transactional across parent/child scopes: if any scope is
    /// already exhausted, no ancestor or sibling-visible allowance is consumed.
    pub fn consume(&self, units: u64) -> Result<(), BudgetExceeded> {
        let _guard = self
            .charge_lock
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        let now = Instant::now();
        for (index, state) in self.states.iter().enumerate() {
            if let Err(error) = state.ensure_work_available(units, now) {
                return Err(error.with_inherited(index + 1 < self.states.len()));
            }
        }
        for state in self.states.iter() {
            state.charge_work(units);
        }
        Ok(())
    }

    /// Cooperatively cancel the current (innermost) scope.
    pub fn cancel(&self) {
        let _guard = self
            .charge_lock
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if let Some(state) = self.states.last() {
            let _ = state.status.compare_exchange(
                ACTIVE,
                CANCELLED,
                Ordering::AcqRel,
                Ordering::Acquire,
            );
        }
    }

    #[must_use]
    pub fn is_exhausted(&self) -> bool {
        self.checkpoint().is_err()
    }

    #[must_use]
    pub fn depth(&self) -> usize {
        self.states.len()
    }

    #[must_use]
    pub fn has_work_limit(&self) -> bool {
        self.states.iter().any(|state| state.work_limit.is_some())
    }
}

/// Adapts a [`WorkBudget`] to callback/visitor APIs that cannot return errors.
///
/// The first budget error is latched. With deterministic work limits, every
/// unit is charged exactly. Without work limits, deadline/cancellation checks
/// are amortized to one per `poll_interval` units.
#[derive(Debug, Clone)]
pub struct BudgetPoller {
    budget: WorkBudget,
    poll_interval: u64,
    pending: u64,
    error: Option<BudgetExceeded>,
    exact_work: bool,
}

impl BudgetPoller {
    #[must_use]
    pub fn new(budget: &WorkBudget, poll_interval: u64) -> Self {
        Self {
            budget: budget.clone(),
            poll_interval: poll_interval.max(1),
            pending: 0,
            error: None,
            exact_work: budget.has_work_limit(),
        }
    }

    /// Record progress. Returns `false` after the budget is exhausted so a
    /// callback can prune the remaining subtree immediately.
    pub fn poll(&mut self, units: u64) -> bool {
        if self.error.is_some() {
            return false;
        }
        if self.exact_work {
            if let Err(error) = self.budget.consume(units) {
                self.error = Some(error);
                return false;
            }
            return true;
        }

        self.pending = self.pending.saturating_add(units);
        if self.pending < self.poll_interval {
            return true;
        }
        self.pending = 0;
        if let Err(error) = self.budget.checkpoint() {
            self.error = Some(error);
            return false;
        }
        true
    }

    pub fn finish(&mut self) -> Result<(), BudgetExceeded> {
        if let Some(error) = self.error.clone() {
            return Err(error);
        }
        self.pending = 0;
        self.budget.checkpoint()
    }
}

/// Find a budget-exhaustion error anywhere in a standard error source chain.
#[must_use]
pub fn find_budget_exceeded<'a>(
    mut error: &'a (dyn Error + 'static),
) -> Option<&'a BudgetExceeded> {
    loop {
        if let Some(exceeded) = error.downcast_ref::<BudgetExceeded>() {
            return Some(exceeded);
        }
        error = error.source()?;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deterministic_work_limit_is_shared_by_clones() {
        let budget = WorkBudget::new("scan", BudgetLimits::work(5));
        let other = budget.clone();
        assert!(budget.consume(2).is_ok());
        assert!(other.consume(3).is_ok());
        assert!(matches!(
            budget.consume(1),
            Err(ref error)
                if error.kind() == BudgetExceededKind::Work
                    && error.scope() == "scan"
                    && error.work_limit() == Some(5)
                    && error.work_consumed() == Some(5)
        ));
    }

    #[test]
    fn child_enforces_both_parent_and_local_limits() {
        let root = WorkBudget::new("project", BudgetLimits::work(10));
        let child = root.child("unit", BudgetLimits::work(3));
        assert_eq!(child.depth(), 2);
        assert!(child.consume(3).is_ok());
        assert!(matches!(
            child.consume(1),
            Err(ref error)
                if error.scope() == "unit"
                    && error.kind() == BudgetExceededKind::Work
                    && error.is_local()
        ));

        let sibling = root.child("sibling", BudgetLimits::work(10));
        // The rejected child charge must not consume parent allowance.
        assert!(sibling.consume(7).is_ok());
        assert!(matches!(
            sibling.consume(1),
            Err(ref error) if error.scope() == "project" && error.is_inherited()
        ));
    }

    #[test]
    fn zero_deadline_fails_immediately_and_stays_failed() {
        let budget = WorkBudget::new("parse", BudgetLimits::wall_time(Duration::ZERO));
        assert!(matches!(
            budget.checkpoint(),
            Err(ref error)
                if error.kind() == BudgetExceededKind::Deadline && error.scope() == "parse"
        ));
        assert!(matches!(
            budget.checkpoint(),
            Err(ref error) if error.kind() == BudgetExceededKind::Deadline
        ));
    }

    #[test]
    fn explicit_cancellation_is_visible_to_all_clones() {
        let budget = WorkBudget::unlimited("analysis");
        let other = budget.clone();
        budget.cancel();
        assert!(matches!(
            other.checkpoint(),
            Err(ref error) if error.kind() == BudgetExceededKind::Cancelled
        ));
    }

    #[test]
    fn poller_charges_work_exactly_when_work_is_bounded() {
        let budget = WorkBudget::new("visitor", BudgetLimits::work(2));
        let mut poller = BudgetPoller::new(&budget, 256);
        assert!(poller.poll(1));
        assert!(poller.poll(1));
        assert!(!poller.poll(1));
        assert!(matches!(
            poller.finish(),
            Err(ref error) if error.kind() == BudgetExceededKind::Work
        ));
    }

    #[test]
    fn poller_latches_cancellation_for_non_result_visitors() {
        let budget = WorkBudget::unlimited("visitor");
        let mut poller = BudgetPoller::new(&budget, 2);
        assert!(poller.poll(1));
        budget.cancel();
        assert!(!poller.poll(1));
        assert!(!poller.poll(1));
        assert!(matches!(
            poller.finish(),
            Err(ref error) if error.kind() == BudgetExceededKind::Cancelled
        ));
    }

    #[cfg(unix)]
    #[test]
    fn budgeted_command_captures_output() {
        let budget = WorkBudget::new("child", BudgetLimits::wall_time(Duration::from_secs(1)));
        let mut command = Command::new("sh");
        command.args(["-c", "printf stdout; printf stderr >&2"]);
        let output = run_command(&mut command, &budget).expect("child should complete");
        assert!(output.status.success());
        assert_eq!(output.stdout, b"stdout");
        assert_eq!(output.stderr, b"stderr");
    }

    #[cfg(unix)]
    #[test]
    fn budgeted_command_kills_child_after_deadline() {
        let budget = WorkBudget::new("child", BudgetLimits::wall_time(Duration::from_millis(20)));
        let mut command = Command::new("sh");
        command.args(["-c", "sleep 5"]);
        assert!(matches!(
            run_command(&mut command, &budget),
            Err(CommandRunError::Budget(ref error))
                if error.kind() == BudgetExceededKind::Deadline
        ));
    }
}
