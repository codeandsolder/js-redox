/**
 * Normalize V8 function coverage in best-effort or precise mode.
 * Offsets are V8 UTF-16 source offsets, NOT byte offsets into captured files.
 * Only positive counters prove execution; an absent script or zero counter
 * does not prove a source was never executed.
 */
export function normalizeExecutionCoverage(snapshot) {
  if (!Array.isArray(snapshot?.result)) {
    throw new TypeError("Profiler coverage snapshot must return result[]");
  }
  return snapshot.result.map((script) => {
    const functions = (script.functions || []).map((fn) => ({
      functionName: fn.functionName || "",
      isBlockCoverage: Boolean(fn.isBlockCoverage),
      ranges: (fn.ranges || []).map((range) => ({
        startOffset: range.startOffset,
        endOffset: range.endOffset,
        count: range.count,
      })),
    }));
    return {
      scriptId: script.scriptId,
      url: script.url || "",
      functions,
      positiveFunctions: functions.filter((fn) => fn.ranges.some((range) => range.count > 0)).length,
      positiveRanges: functions.reduce(
        (total, fn) => total + fn.ranges.filter((range) => range.count > 0).length, 0,
      ),
    };
  });
}

export function summarizeExecutionCoverage(sessions) {
  const captured = sessions.filter((session) => session.status === "captured");
  const scripts = captured.flatMap((session) => session.scripts);
  return {
    sessions: sessions.length,
    capturedSessions: captured.length,
    unavailableSessions: sessions.length - captured.length,
    observedScriptProfiles: scripts.length,
    positiveScriptProfiles: scripts.filter((script) => script.positiveRanges > 0).length,
    positiveFunctionProfiles: scripts.reduce((n, script) => n + script.positiveFunctions, 0),
    positiveRanges: scripts.reduce((n, script) => n + script.positiveRanges, 0),
  };
}


// Best-effort uses V8's existing invocation feedback; unlike precise coverage,
// it does not disable optimization or install per-block counters.
export const COVERAGE_MODES = Object.freeze(["none", "best-effort", "precise"]);

export function coverageSnapshotMethod(mode) {
  switch (mode) {
    case "best-effort": return "Profiler.getBestEffortCoverage";
    case "precise": return "Profiler.takePreciseCoverage";
    default: throw new TypeError(`coverage mode ${mode} has no snapshot method`);
  }
}

export async function enableExecutionCoverage(session, mode) {
  if (!COVERAGE_MODES.includes(mode)) throw new TypeError(`unknown coverage mode: ${mode}`);
  if (mode === "none") return { status: "disabled", mode };
  try {
    await session.send("Profiler.enable");
    if (mode === "precise") {
      await session.send("Profiler.startPreciseCoverage", { callCount: true, detailed: true });
    }
    return { status: "started", mode, session };
  } catch (error) {
    return { status: "unavailable", mode, error: String(error) };
  }
}

export async function collectExecutionCoverage(state, withTimeout, timeoutMs) {
  const { mode, status } = state;
  if (status !== "started") return { status, error: state.error ?? null, scripts: [] };
  try {
    const method = coverageSnapshotMethod(mode);
    const snapshot = await withTimeout(state.session.send(method), timeoutMs, method);
    return {
      status: "captured",
      timestamp: snapshot.timestamp ?? null,
      scripts: normalizeExecutionCoverage(snapshot),
    };
  } catch (error) {
    return { status: "unavailable", error: String(error), scripts: [] };
  }
}
