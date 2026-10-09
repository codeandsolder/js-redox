const sleep = (ms) => new Promise((resolve) => setTimeout(resolve, ms));

export function isTerminalTargetClosedError(error) {
  const message = String(error?.message || error);
  return (
    message.includes("Target page, context or browser has been closed") ||
    message.includes("Target closed") ||
    message.includes("Page closed") ||
    message.includes("Browser has been closed")
  );
}

export function isTransientScrollNavigationError(error) {
  const message = String(error?.message || error);
  return (
    message.includes("Execution context was destroyed") ||
    message.includes("Cannot find context with specified id") ||
    message.includes("Inspected target navigated or closed") ||
    message.includes("Frame was detached")
  );
}

export async function evaluateDuringScroll(page, opts, events, phase, fn, onRetry = null) {
  const maxAttempts = 3;
  for (let attempt = 1; attempt <= maxAttempts; attempt += 1) {
    try {
      return await page.evaluate(fn);
    } catch (error) {
      if (!isTransientScrollNavigationError(error) || attempt >= maxAttempts) throw error;
      events.push({
        at: Date.now(),
        type: "scroll-navigation-retry",
        phase,
        attempt,
        url: page.url(),
        error: String(error),
      });
      if (onRetry) onRetry();
      try {
        await page.waitForLoadState("domcontentloaded", { timeout: Math.min(opts.timeoutMs, 5_000) });
      } catch {
        // A continuously navigating page may not become idle; the evaluate retry
        // below is still bounded and remains the source of truth.
      }
      await sleep(opts.fastScroll ? 100 : 250);
    }
  }
  throw new Error(`scroll evaluation failed after ${maxAttempts} attempts: ${phase}`);
}
