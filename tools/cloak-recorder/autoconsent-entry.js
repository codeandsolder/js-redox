import AutoConsent from "@duckduckgo/autoconsent";
import { autoconsent } from "@duckduckgo/autoconsent/rules/rules.json";

(() => {
  const key = "__jsRedoxAutoconsent";
  if (Object.prototype.hasOwnProperty.call(globalThis, key)) return;

  const record = {
    startedAt: Date.now(),
    messages: [],
    error: null,
    consent: null,
  };

  Object.defineProperty(globalThis, key, {
    value: record,
    configurable: true,
    enumerable: false,
    writable: false,
  });

  try {
    const consent = new AutoConsent(
      (message) => {
        record.messages.push({ at: Date.now(), message });
        return Promise.resolve();
      },
      {
        enabled: true,
        autoAction: "optIn",
        disabledCmps: [],
        enablePrehide: false,
        enableCosmeticRules: true,
        enableGeneratedRules: true,
        detectRetries: 4,
        isMainWorld: true,
        prehideTimeout: 0,
        enableHeuristicDetection: true,
        enablePopupMutationObserver: true,
        visualTest: false,
        logs: {
          lifecycle: false,
          rulesteps: false,
          detectionsteps: false,
          evals: false,
          errors: false,
          messages: false,
          waits: false,
        },
        performanceLoggingEnabled: false,
        heuristicPopupSearchTimeout: 1500,
        heuristicMode: "tier2",
      },
      { autoconsent },
    );
    record.consent = consent;
    consent.start();
  } catch (error) {
    record.error = String(error?.stack || error);
  }
})();
