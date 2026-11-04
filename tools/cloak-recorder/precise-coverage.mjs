/**
 * Normalize V8 precise code coverage while retaining function/block ranges.
 * Offsets are V8 UTF-16 source offsets, NOT byte offsets into captured files.
 * Only positive counters prove execution; an absent script or zero counter
 * does not prove a source was never executed.
 */
export function normalizePreciseCoverage(snapshot) {
  if (!Array.isArray(snapshot?.result)) {
    throw new TypeError("Profiler.takePreciseCoverage must return result[]");
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

export function summarizePreciseCoverage(sessions) {
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
