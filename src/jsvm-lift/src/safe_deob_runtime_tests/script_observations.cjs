// Test-only runtime for synthetic fixtures, injected after the input batch.
const vm = require('node:vm');
const types = require('node:util').types;
const {isNativeError, isProxy} = types;
const intrinsicNames = [
    'Object', 'Array', 'Error', 'EvalError', 'RangeError', 'ReferenceError',
    'SyntaxError', 'TypeError', 'URIError', 'AggregateError', 'SuppressedError'
];
const exoticChecks = [
    types.isArgumentsObject, types.isAnyArrayBuffer, types.isArrayBufferView,
    types.isBoxedPrimitive, types.isDate, types.isExternal,
    types.isGeneratorObject, types.isMap, types.isMapIterator,
    types.isModuleNamespaceObject, types.isPromise, types.isRegExp,
    types.isSet, types.isSetIterator, types.isWeakMap, types.isWeakSet
];
const symbolDescription = Object.getOwnPropertyDescriptor(Symbol.prototype, 'description').get;
const wellKnownSymbols = new Map(
    Object.getOwnPropertyNames(Symbol)
        .map(key => [Symbol[key], key])
        .filter(([value]) => typeof value === 'symbol')
);

// Own descriptors avoid evaluating accessors. For Error name/message, walk
// the prototype chain without invoking a getter or a proxy trap.
function dataProperty(value, key) {
    for (let current = value; current !== null; current = Object.getPrototypeOf(current)) {
        if (isProxy(current)) throw Error('unsupported observation: proxy property lookup');
        const descriptor = Object.getOwnPropertyDescriptor(current, key);
        if (!descriptor) continue;
        if (!Object.hasOwn(descriptor, 'value')) {
            throw Error('unsupported observation: accessor error property');
        }
        return descriptor.value;
    }
    return undefined;
}

// One identity table for the final completion and the event trace. Ordinary
// records/arrays preserve ordered own keys, data/accessor descriptors,
// extensibility, and aliases/cycles. Native errors also preserve own
// descriptors (except stack) and the data values of inherited name/message.
// Function bodies have only a source-text projection, not callable equivalence.
// Known exotic objects and unrecognized prototypes fail the harness.
function makeEncoder(realmPrototypes) {
    const seen = new Map();
    const prototypes = new Map([[null, 'null']]);
    for (const [index, name] of intrinsicNames.entries()) {
        const host = globalThis[name]?.prototype;
        if (host !== undefined) prototypes.set(host, 'host-' + name);
        const realm = realmPrototypes[index];
        if (realm !== undefined) prototypes.set(realm, name);
    }

    function encodeDescriptor(descriptor) {
        const flags = [descriptor.enumerable, descriptor.configurable];
        if (Object.hasOwn(descriptor, 'value')) {
            return ['data', ...flags, descriptor.writable, encode(descriptor.value)];
        }
        return ['accessor', ...flags, encode(descriptor.get), encode(descriptor.set)];
    }

    function encode(value) {
        const type = typeof value;
        switch (type) {
            case 'number': return [type, Object.is(value, -0) ? '-0' : String(value)];
            case 'undefined': return [type];
            case 'bigint': return [type, String(value)];
            case 'boolean':
            case 'string': return [type, value];
        }
        if (value === null) return ['null'];
        if (type === 'symbol') {
            const globalKey = Symbol.keyFor(value);
            if (globalKey !== undefined) return ['global-symbol', globalKey];
            if (wellKnownSymbols.has(value)) return ['well-known-symbol', wellKnownSymbols.get(value)];
        } else if (isProxy(value)) {
            throw Error('unsupported observation: proxy');
        }
        if (seen.has(value)) return ['ref', seen.get(value)];
        const id = seen.size;
        seen.set(value, id);
        if (type === 'symbol') return ['symbol', id, encode(symbolDescription.call(value))];
        if (type === 'function') return ['function', id, Function.prototype.toString.call(value)];
        const error = isNativeError(value);
        if (!error && exoticChecks.some(check => check(value))) {
            throw Error('unsupported observation: exotic object');
        }
        const prototype = Object.getPrototypeOf(value);
        if (!prototypes.has(prototype)) throw Error('unsupported observation: object prototype');
        // Stack traces contain source locations and may invoke prepareStackTrace
        // on some Node versions. They are explicitly outside this projection.
        const properties = Reflect.ownKeys(value)
            .filter(key => !error || key !== 'stack')
            .map(key => [
                encode(key),
                encodeDescriptor(Object.getOwnPropertyDescriptor(value, key))
            ]);
        return [
            error ? 'error' : Array.isArray(value) ? 'array' : 'record',
            id,
            prototypes.get(prototype),
            Object.isExtensible(value),
            properties,
            ...(error ? [encode(dataProperty(value, 'name')), encode(dataProperty(value, 'message'))] : [])
        ];
    }
    return encode;
}

function observe(text, label) {
    // Parse and observation failures are harness errors, not matching runtime
    // exceptions. Only the script's execution itself belongs in the try block.
    const script = new vm.Script(text, {filename: label});
    const events = [];
    const globals = browserGlobals ? {events, atob} : {events};
    const context = vm.createContext(globals);
    const realmPrototypes = vm.runInContext(
        JSON.stringify(intrinsicNames) + '.map(name => globalThis[name]?.prototype)', context
    );
    let result;
    let thrown = false;
    try {
        result = script.runInContext(context, {timeout: 10000});
    } catch (error) {
        if (!isProxy(error) && isNativeError(error) &&
            Object.getOwnPropertyDescriptor(error, 'code')?.value === 'ERR_SCRIPT_EXECUTION_TIMEOUT') {
            throw error;
        }
        result = error;
        thrown = true;
    }
    const encode = makeEncoder(realmPrototypes);
    return JSON.stringify([
        [thrown ? 'throw' : 'return', encode(result)],
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
