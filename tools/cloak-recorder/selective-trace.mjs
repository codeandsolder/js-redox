/** Explicit, bounded debugger breakpoint witnesses. Never universal path proofs. */
export function validateTraceSpec(spec) {
  if (!spec || !Array.isArray(spec.points) || spec.points.length < 1 || spec.points.length > 24) {
    throw new Error("trace spec needs 1..24 points");
  }
  const maxHits = spec.maxHits ?? 16;
  const maxScopeProperties = spec.maxScopeProperties ?? 24;
  if (!Number.isSafeInteger(maxHits) || maxHits < 1 || maxHits > 128) {
    throw new Error("maxHits must be an integer from 1 to 128");
  }
  if (!Number.isSafeInteger(maxScopeProperties) || maxScopeProperties < 1 || maxScopeProperties > 64) {
    throw new Error("maxScopeProperties must be an integer from 1 to 64");
  }
  const maxFunctionLocations = spec.maxFunctionLocations ?? 16;
  if (!Number.isSafeInteger(maxFunctionLocations) || maxFunctionLocations < 0 || maxFunctionLocations > 64) {
    throw new Error("maxFunctionLocations must be an integer from 0 to 64");
  }
  const points = spec.points.map((point, index) => {
    const selectors = ["url", "urlRegex", "scriptHash"].filter(
      (name) => typeof point?.[name] === "string" && point[name].length > 0,
    );
    if (selectors.length !== 1 || selectors.some((key) => point[key].length > 2048)) {
      throw new Error("trace point " + index + ": exactly one bounded URL, regex or script hash required");
    }
    if (!Number.isSafeInteger(point.lineNumber) || point.lineNumber < 0) {
      throw new Error("trace point " + index + ": zero-based lineNumber required");
    }
    if (point.columnNumber !== undefined &&
        (!Number.isSafeInteger(point.columnNumber) || point.columnNumber < 0)) {
      throw new Error("trace point " + index + ": columnNumber must be nonnegative");
    }
    const expressions = point.expressions ?? [];
    if (!Array.isArray(expressions) || expressions.length > 8 ||
        expressions.some((x) => typeof x !== "string" || x.length < 1 || x.length > 256)) {
      throw new Error("trace point " + index + ": at most 8 bounded expressions");
    }
    if (selectors[0] === "urlRegex") new RegExp(point.urlRegex);
    return {
      id: "trace-" + index,
      [selectors[0]]: point[selectors[0]],
      lineNumber: point.lineNumber,
      ...(point.columnNumber === undefined ? {} : { columnNumber: point.columnNumber }),
      expressions,
    };
  });
  return { schema: "js-redox/selective-trace-config/v1", maxHits, maxScopeProperties, maxFunctionLocations, points };
}

export function breakpointParams(point) {
  const params = { lineNumber: point.lineNumber };
  for (const key of ["url", "urlRegex", "scriptHash", "columnNumber"]) {
    if (point[key] !== undefined) params[key] = point[key];
  }
  return params;
}

export function compactRemoteValue(remote) {
  if (!remote) return { status: "missing" };
  const value = {
    type: remote.type ?? null,
    subtype: remote.subtype ?? null,
    description: typeof remote.description === "string" ? remote.description.slice(0, 240) : null,
  };
  if (Object.hasOwn(remote, "value")) value.value = remote.value;
  if (typeof remote.unserializableValue === "string") value.unserializableValue = remote.unserializableValue;
  if (typeof remote.objectId === "string") value.inspectorObjectId = remote.objectId;
  return value;
}

// DevTools represents a function's actual definition as an internal
// [[FunctionLocation]] property. Its script ID is scoped to this CDP session.
// Never infer a function's identity from its display name or source string.
export function parseFunctionDefinition(properties) {
  const internal = properties?.internalProperties;
  if (!Array.isArray(internal)) return null;
  const location = internal.find((entry) => entry?.name === "[[FunctionLocation]]")?.value?.value;
  if (!location || typeof location !== "object" ||
      typeof location.scriptId !== "string" || location.scriptId.length === 0 ||
      !Number.isSafeInteger(location.lineNumber) || location.lineNumber < 0 ||
      !Number.isSafeInteger(location.columnNumber) || location.columnNumber < 0) {
    return null;
  }
  return {
    scriptId: location.scriptId,
    lineNumber: location.lineNumber,
    columnNumber: location.columnNumber,
    evidence: "Runtime.getProperties.internalProperties.[[FunctionLocation]]",
  };
}

export async function inspectFunctionDefinition(session, remote) {
  if (remote?.type !== "function" || typeof remote.objectId !== "string") return null;
  try {
    const properties = await session.send("Runtime.getProperties", {
      objectId: remote.objectId, ownProperties: true, generatePreview: false,
    });
    return parseFunctionDefinition(properties);
  } catch {
    // Bound/native/proxy functions and inspector errors may have no source location.
    return null;
  }
}

async function identityFor(session, remote) {
  if (!remote?.objectId) return null;
  try {
    const result = await session.send("HeapProfiler.getHeapObjectId", { objectId: remote.objectId });
    return result.heapSnapshotObjectId && result.heapSnapshotObjectId !== "0" ? result.heapSnapshotObjectId : null;
  } catch {
    return null;
  }
}

export async function capturePausedWitness(session, event, point, config) {
  const frames = (event.callFrames || []).slice(0, 16).map((frame) => ({
    functionName: frame.functionName || "",
    location: frame.location,
    functionLocation: frame.functionLocation ?? null,
    url: frame.url || "",
  }));
  const topFrame = event.callFrames?.[0];
  // One paused-state budget shared across local/closure and explicit expressions.
  // Reuse identical inspector handles; they are only valid within this pause.
  const definitionCache = new Map();
  let remainingDefinitions = config.maxFunctionLocations ?? 16;
  async function attachFunctionDefinition(remote, record) {
    if (remote?.type !== "function" || !remote.objectId) return;
    if (!definitionCache.has(remote.objectId)) {
      if (remainingDefinitions === 0) return;
      remainingDefinitions -= 1;
      definitionCache.set(remote.objectId, await inspectFunctionDefinition(session, remote));
    }
    const definition = definitionCache.get(remote.objectId);
    if (definition) record.functionDefinition = definition;
  }
  const scopes = [];
  if (topFrame) {
    for (const scope of (topFrame.scopeChain || []).filter(
      (scope) => ["local", "closure", "catch", "block"].includes(scope.type),
    ).slice(0, 4)) {
      const row = { type: scope.type, name: scope.name || null, variables: [] };
      if (scope.object?.objectId) {
        try {
          const properties = await session.send("Runtime.getProperties", {
            objectId: scope.object.objectId,
            ownProperties: true,
            generatePreview: false,
          });
          for (const prop of (properties.result || []).slice(0, config.maxScopeProperties)) {
            const entry = {
              name: prop.name,
              ...(prop.value
                ? { value: compactRemoteValue(prop.value) }
                : { status: prop.get || prop.set ? "accessor_not_called" : "unavailable" }),
            };
            if (prop.value?.objectId) entry.heapObjectId = await identityFor(session, prop.value);
            if (entry.value) await attachFunctionDefinition(prop.value, entry.value);
            row.variables.push(entry);
          }
        } catch (error) {
          row.error = String(error);
        }
      }
      scopes.push(row);
    }
  }
  const expressions = [];
  for (const expression of point.expressions) {
    if (!topFrame?.callFrameId) break;
    try {
      const result = await session.send("Debugger.evaluateOnCallFrame", {
        callFrameId: topFrame.callFrameId, expression,
        silent: true, throwOnSideEffect: true, returnByValue: false,
      });
      if (result.exceptionDetails) {
        expressions.push({ expression, status: "evaluation_rejected", exception: result.exceptionDetails.text });
      } else {
        const value = compactRemoteValue(result.result);
        if (result.result?.objectId) value.heapObjectId = await identityFor(session, result.result);
        await attachFunctionDefinition(result.result, value);
        expressions.push({ expression, status: "observed", value });
      }
    } catch (error) {
      expressions.push({ expression, status: "unavailable", error: String(error) });
    }
  }
  return {
    pointId: point.id,
    reason: event.reason,
    hitBreakpoints: event.hitBreakpoints || [],
    frames, scopes, expressions,
  };
}

export async function captureAndResume(session, event, point, config) {
  try {
    return await capturePausedWitness(session, event, point, config);
  } finally {
    await session.send("Debugger.resume");
  }
}
