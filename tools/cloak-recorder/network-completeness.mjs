export function classifyRelevantBodies(records, isExpected) {
  const relevantResponses = records.filter((record) => isExpected(record) && record.status > 0);
  const abortedRelevantResponses = relevantResponses.filter(
    (record) => !record.body && record.failure,
  );
  const expectedBodies = relevantResponses.filter((record) => !record.failure);
  const missingBodies = expectedBodies.filter((record) => !record.body);
  const failedBodies = missingBodies.filter((record) => record.bodyCapture?.status === "failed");
  return { relevantResponses, abortedRelevantResponses, expectedBodies, missingBodies, failedBodies };
}
