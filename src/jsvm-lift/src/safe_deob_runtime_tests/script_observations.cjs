// Test-only runtime for synthetic fixtures, injected after the input batch.
const vm = require('node:vm');

// Match the observable scalar domain of the tests. Arrays are traversed by
// their index descriptors to distinguish holes and undefined without invoking
// getters. Other object/function completions preserve the previous explicit
// String observation, not a claim of general heap or callable equivalence.
function encode(value, active = new Set()) {
    const type = typeof value;
    if (type === 'number') {
        return [type, Object.is(value, -0) ? '-0' : String(value)];
    }
    if (value === null) return ['null'];
    if (type === 'undefined' || type === 'bigint' || type === 'symbol' || type === 'function') {
        return [type, String(value)];
    }
    if (!Array.isArray(value)) {
        return [type, type === 'object' ? String(value) : value];
    }
    if (active.has(value)) throw Error('cyclic array observation is unsupported');
    active.add(value);
    const entries = [];
    for (let i = 0; i < value.length; i++) {
        const descriptor = Object.getOwnPropertyDescriptor(value, i);
        if (!descriptor) {
            entries.push(['hole']);
        } else {
            if (!Object.hasOwn(descriptor, 'value')) {
                throw Error('accessor array observation is unsupported');
            }
            entries.push(encode(descriptor.value, active));
        }
    }
    active.delete(value);
    return ['array', entries];
}

function observe(text, label) {
    // Parse and observation failures are harness errors, not matching runtime
    // exceptions. Only the script's execution itself belongs in the try block.
    const script = new vm.Script(text, {filename: label});
    const events = [];
    const globals = browserGlobals ? {events, atob} : {events};
    let result;
    let thrown = false;
    try {
        result = script.runInNewContext(globals, {timeout: 10000});
    } catch (error) {
        if (error?.code === 'ERR_SCRIPT_EXECUTION_TIMEOUT') throw error;
        result = error;
        thrown = true;
    }
    return JSON.stringify([
        thrown ? ['throw', String(result)] : ['return', encode(result)],
        encode(events)
    ]);
}
for (const row of comparisons) {
    const before = observe(row.original, row.label + ':original');
    const after = observe(row.rewritten, row.label + ':rewritten');
    if (before !== after) {
        let offset = 0;
        while (offset < before.length && before[offset] === after[offset]) offset++;
        throw Error(row.label + ': mismatch at encoded offset ' + offset +
            '\noriginal: ' + before.slice(Math.max(0, offset - 80), offset + 160) +
            '\nrewritten: ' + after.slice(Math.max(0, offset - 80), offset + 160));
    }
}
console.log(comparisons.length);
