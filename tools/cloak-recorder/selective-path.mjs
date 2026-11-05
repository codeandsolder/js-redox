import { capturePausedWitness } from "./selective-trace.mjs";

// One controller per CDP target/session. Multiple breakpoints can coexist, but
// the target's debugger is paused in only one location at a time.
// This is a bounded *sequence of witnessed locations*, not a complete trace.
export function createSelectivePathController({
  session, sessionName, config, acquireHit, onHit, onError,
}) {
  let active = null;

  const fail = (point, stage, error) => onError({
    cdpSession: sessionName, pointId: point?.id ?? null,
    stage, error: String(error),
  });

  async function onPaused(event, breakpoints) {
    // The next Debugger.paused event after a successful step command is our
    // next location. Never infer a branch just from a missing event.
    let command = "Debugger.resume";
    let point = null;
    try {
      if (active !== null) {
        point = active.point;
        const stepPoint = {
          id: point.id,
          expressions: point.stepExpressions,
        };
        const state = await capturePausedWitness(session, event, stepPoint, config);
        active.hit.steps.push({
          index: active.hit.steps.length,
          ...state,
        });
        if (active.hit.steps.length < point.followSteps) {
          command = point.stepMode === "over" ? "Debugger.stepOver" : "Debugger.stepInto";
        } else {
          active.hit.pathWitnessStatus = "bounded_steps_recorded";
          active = null;
        }
      } else {
        const breakpoint = (event.hitBreakpoints || []).find((id) => breakpoints?.has(id));
        point = breakpoint ? breakpoints.get(breakpoint) : null;
        if (point && acquireHit()) {
          const state = await capturePausedWitness(session, event, point, config);
          const hit = {
            ...state,
            cdpSession: sessionName,
            at: Date.now(),
            steps: [],
            pathWitnessStatus: point.followSteps > 0
              ? "steps_requested" : "not_requested",
            pathWitnessRequestedSteps: point.followSteps,
            pathWitnessMode: point.stepMode,
          };
          onHit(hit);
          if (point.followSteps > 0) {
            active = { point, hit };
            command = point.stepMode === "over" ? "Debugger.stepOver" : "Debugger.stepInto";
          }
        }
      }
    } catch (error) {
      fail(point, "paused-state-capture", error);
      if (active !== null) {
        active.hit.pathWitnessStatus = "capture_failed";
        active = null;
      }
    }

    try {
      await session.send(command);
    } catch (error) {
      fail(point, command, error);
      if (active !== null) {
        active.hit.pathWitnessStatus = "debugger_command_failed";
        active = null;
      }
      if (command !== "Debugger.resume") {
        try {
          await session.send("Debugger.resume");
        } catch (resumeError) {
          fail(point, "Debugger.resume-fallback", resumeError);
        }
      }
    }
  }

  function finish() {
    if (active) {
      active.hit.pathWitnessStatus = "step_events_incomplete";
      active = null;
    }
  }

  return { onPaused, finish };
}
