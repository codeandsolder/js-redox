export const WORKER_TARGET_TYPES = new Set([
  "worker",
  "shared_worker",
  "service_worker",
  "worklet",
  "shared_storage_worklet",
  "auction_worklet",
]);

export const WORKER_TARGET_FILTER = [
  ...[...WORKER_TARGET_TYPES].map((type) => ({ type, exclude: false })),
  { exclude: true },
];

export function isWorkerTargetType(type) {
  return WORKER_TARGET_TYPES.has(type);
}

export function createNestedCdpRouter(rootSession) {
  let nextMessageId = 1;
  const states = new Map();
  const pending = new Map();
  const parents = new Map();
  const children = new Map();

  function stateFor(sessionId) {
    let state = states.get(sessionId);
    if (!state) {
      state = { closed: false, handlers: new Map() };
      states.set(sessionId, state);
    }
    return state;
  }

  function pendingKey(sessionId, messageId) {
    return `${sessionId}:${messageId}`;
  }

  function registerParent(sessionId, parentSessionId = null) {
    if (!sessionId) return;
    if (parents.has(sessionId)) return;
    parents.set(sessionId, parentSessionId);
    if (parentSessionId === null) return;
    let descendants = children.get(parentSessionId);
    if (!descendants) {
      descendants = new Set();
      children.set(parentSessionId, descendants);
    }
    descendants.add(sessionId);
  }

  function emit(sessionId, event, params) {
    const handlers = stateFor(sessionId).handlers.get(event);
    if (!handlers) return;
    for (const handler of [...handlers]) handler(params);
  }

  function closeSession(sessionId, reason = "CDP target detached") {
    const state = stateFor(sessionId);
    if (state.closed) return;

    for (const childSessionId of [...(children.get(sessionId) || [])]) {
      closeSession(childSessionId, reason);
    }
    children.delete(sessionId);

    const parentSessionId = parents.get(sessionId);
    if (parentSessionId !== undefined && parentSessionId !== null) {
      children.get(parentSessionId)?.delete(sessionId);
    }

    state.closed = true;
    for (const [key, waiter] of pending) {
      if (!key.startsWith(`${sessionId}:`)) continue;
      pending.delete(key);
      waiter.reject(new Error(reason));
    }
    emit(sessionId, "close");
  }

  function handleProtocolMessage(sessionId, message) {
    let payload;
    try {
      payload = JSON.parse(message);
    } catch {
      return;
    }

    if (payload.id !== undefined) {
      const key = pendingKey(sessionId, payload.id);
      const waiter = pending.get(key);
      if (!waiter) return;
      pending.delete(key);
      if (payload.error) waiter.reject(new Error(JSON.stringify(payload.error)));
      else waiter.resolve(payload.result || {});
      return;
    }

    if (!payload.method) return;
    if (payload.method === "Target.attachedToTarget" && payload.params?.sessionId) {
      registerParent(payload.params.sessionId, sessionId);
    }
    if (payload.method === "Target.receivedMessageFromTarget" && payload.params?.sessionId) {
      handleProtocolMessage(payload.params.sessionId, payload.params.message);
    }
    if (payload.method === "Target.detachedFromTarget" && payload.params?.sessionId) {
      closeSession(payload.params.sessionId);
    }
    emit(sessionId, payload.method, payload.params || {});
  }

  rootSession.on("Target.receivedMessageFromTarget", ({ sessionId, message }) => {
    registerParent(sessionId, null);
    handleProtocolMessage(sessionId, message);
  });

  rootSession.on("Target.detachedFromTarget", ({ sessionId }) => {
    if (sessionId) closeSession(sessionId);
  });

  async function forwardMessage(sessionId, message) {
    const parentSessionId = parents.get(sessionId);
    if (parentSessionId === undefined || parentSessionId === null) {
      await rootSession.send("Target.sendMessageToTarget", { sessionId, message });
      return;
    }
    await session(parentSessionId).send("Target.sendMessageToTarget", { sessionId, message });
  }

  function session(sessionId) {
    registerParent(sessionId, parents.get(sessionId) ?? null);
    const state = stateFor(sessionId);
    const adapter = {
      send(method, params = {}) {
        if (state.closed) return Promise.reject(new Error(`CDP session ${sessionId} is closed`));
        const id = nextMessageId++;
        const key = pendingKey(sessionId, id);
        return new Promise((resolve, reject) => {
          pending.set(key, { resolve, reject });
          forwardMessage(
            sessionId,
            JSON.stringify({ id, method, params }),
          ).catch((error) => {
            pending.delete(key);
            reject(error);
          });
        });
      },
      on(event, handler) {
        let handlers = state.handlers.get(event);
        if (!handlers) {
          handlers = new Set();
          state.handlers.set(event, handlers);
        }
        handlers.add(handler);
        return adapter;
      },
      off(event, handler) {
        state.handlers.get(event)?.delete(handler);
        return adapter;
      },
    };
    return adapter;
  }

  return { session };
}
