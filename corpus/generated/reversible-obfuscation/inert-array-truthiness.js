
// Pure allocated literals are truthy and cannot invoke user code.
function inertGuard() {
    let counter = 0;
    const seen = [];
    while (!["", null, 1, false, [2], {}, /x/, void 0] == 0) {
        seen.push(++counter);
        if (counter === 2) break;
    }
    return seen;
}
// Array elements still execute on every loop test.
function effectfulGuard() {
    const seen = [];
    let index = 0;
    while (![seen.push("test"), ++index] == 0) {
        seen.push("body");
        if (index === 2) break;
    }
    return seen;
}
function spreadGuard() {
    const seen = [];
    const iterable = {
        [Symbol.iterator]() {
            seen.push("iterator");
            return [1][Symbol.iterator]();
        }
    };
    let index = 0;
    while (![...iterable] == 0) {
        seen.push(++index);
        if (index === 2) break;
    }
    return seen;
}
function tdzGuard() {
    try {
        while (![later] == 0) { break; }
    } catch (error) {
        return error.name;
    }
    let later = "ready";
    return later;
}
console.log(JSON.stringify([inertGuard(), effectfulGuard(), spreadGuard(), tdzGuard()]));


function collapsedSilentChain(flag) {
    const events=[];
    let state=57, recovery=0;
    while(![""]==0) try {
        if(state==57) state=73;
        else if(state==73) state=37;
        else if(state==37) state=25;
        else if(state==25) {
            events.push("work");
            state=flag?92:90;
        } else if(state==92) {
            recovery=1;
            throw Error("caught");
        } else if(state==90) return events;
    } catch(error) {
        events.push(error.message);
        if(recovery==1) state=90;
        else throw error;
    }
}
function catchIntoSilentChain() {
    const events=[];
    let state=1, raised=false;
    while(true) try {
        if(state==1) {
            if(!raised) { raised=true; throw Error("once"); }
            state=2;
        } else if(state==2) state=3;
        else if(state==3) state=4;
        else if(state==4) return events;
    } catch(error) {
        events.push(error.message);
        state=2;
    }
}
console.log(JSON.stringify([collapsedSilentChain(false),collapsedSilentChain(true),catchIntoSilentChain()]));


function effectfulTerminal(flag) {
    const events=[];
    let state=1;
    while(true) try {
        if(state==1) {
            events.push("enter");
            state=flag?2:(events.push("alternative"),5);
        } else if(state==2) state=3;
        else if(state==3) { events.push("true"); state=6; }
        else if(state==5) { events.push("false"); state=6; }
        else if(state==6) return events;
    } catch(error) { throw error; }
}
function catchRootTerminal() {
    const events=[];
    let state=1, first=true;
    while(true) try {
        if(state==1) {
            events.push("normal");
            if(first) { first=false; throw Error("once"); }
            state=2;
        } else if(state==2) state=3;
        else if(state==3) return events;
    } catch(error) {
        events.push(error.message);
        state=2;
    }
}
console.log(JSON.stringify([effectfulTerminal(true),effectfulTerminal(false),catchRootTerminal()]));


function nonthrowingReturn(log) {
    let state = 1;
    while (true) try {
        if (state == 1) { log.push("before"); state = 2; }
        else if (state == 2) return log;
    } catch (error) { log.push("caught"); throw error; }
}
function catchRootReturn(log) {
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("once"); }
            state = 2;
        } else if (state == 2) return log;
    } catch (error) { log.push(error.message); state = 2; }
}
function throwingGetterReturn(log) {
    let state = 1;
    const object = { get value() { log.push("getter"); throw Error("bad"); } };
    while (true) try {
        if (state == 1) state = 2;
        else if (state == 2) return object.value;
    } catch (error) {
        log.push(error.message);
        log.push(state);
        return log;
    }
}
console.log(JSON.stringify([
    nonthrowingReturn([]),
    catchRootReturn([]),
    throwingGetterReturn([])
]));


function finallyObservesState(log) {
    let state = 1;
    try {
        while (true) try {
            if (state == 1) state = 2;
            else if (state == 2) return "done";
        } catch (error) { throw error; }
    } finally { log.push(state); }
}
const observed = [];
const returned = finallyObservesState(observed);
console.log(JSON.stringify(["finally", returned, observed]));


function automaticSemicolonTerminal() {
    let state = 1;
    while (true) try {
        if (state == 1) {
            state = 2
        } else if (state == 2) return "asi";
    } catch (error) { throw error; }
}
console.log(JSON.stringify(["automatic-semicolon", automaticSemicolonTerminal()]));


function lexicalShadowingReturn(log) {
    function execute(value) {
        let state = 0;
        while (true) try {
            if (state == 0) {
                let value = "inner";
                log.push(value);
                state = 1;
            } else if (state == 1) return value;
        } catch (error) { throw error; }
    }
    return execute("outer");
}
const shadowLog = [];
console.log(JSON.stringify(["shadowed-return", lexicalShadowingReturn(shadowLog), shadowLog]));


function convergentReturn(flag) {
    const events = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = flag ? 2 : 3;
        else if (state === 2) { events.push("left"); state = 4; }
        else if (state === 3) { events.push("right"); state = 4; }
        else if (state === 4) return events;
    } catch (error) { throw error; }
}
function inertLiteralReturn(flag) {
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) return ["left", true];
        else if (state == 3) return ["right", false];
    } catch (error) { throw error; }
}
console.log(JSON.stringify([
    "factored-convergent",
    convergentReturn(true),
    convergentReturn(false),
    inertLiteralReturn(true),
    inertLiteralReturn(false)
]));


function oneEntryEffectfulRegion(flag) {
    const events = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = 2;
        else if (state == 2) {
            events.push("effect");
            state = flag ? 3 : 4;
        } else if (state == 3) return ["left", events];
        else if (state == 4) return ["right", events];
    } catch (error) { throw error; }
}
function oneEntryCaughtException() {
    const events = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = 2;
        else if (state === 2) {
            events.push("before-throw");
            throw Error("expected");
        }
    } catch (error) {
        events.push(error.message);
        return [state, events];
    }
}
function independentCatchEntry() {
    const events = [];
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("retry"); }
            state = 2;
        } else if (state == 2) {
            events.push("entered-two");
            state = 3;
        } else if (state == 3) return events;
    } catch (error) {
        events.push(error.message);
        state = 2;
    }
}
console.log(JSON.stringify([
    "single-entry-regions",
    oneEntryEffectfulRegion(true),
    oneEntryEffectfulRegion(false),
    oneEntryCaughtException(),
    independentCatchEntry()
]));


function convergentEffectfulPredecessor(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state === 1) {
            if (flag) { log.push("left"); state = 2; }
            else { log.push("right"); state = 2; }
        } else if (state === 2) {
            log.push("tail");
            return [state, log];
        }
    } catch (error) { throw error; }
}
function convergentThrowCatch(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) {
            if (flag) { log.push("L"); state = 2; }
            else { log.push("R"); state = 2; }
        } else if (state == 2) {
            log.push("before-throw");
            throw Error("expected");
        }
    } catch (error) {
        log.push(error.message);
        return [state, log];
    }
}
function divergentPredecessor(flag) {
    let state = 1;
    while (true) try {
        if (state == 1) {
            if (flag) state = 2;
            else state = 3;
        } else if (state == 2) return "two";
        else if (state == 3) return "three";
    } catch (error) { throw error; }
}
console.log(JSON.stringify([
    "generalized-single-entry",
    convergentEffectfulPredecessor(true),
    convergentEffectfulPredecessor(false),
    convergentThrowCatch(true),
    convergentThrowCatch(false),
    divergentPredecessor(true),
    divergentPredecessor(false)
]));


function diamondJoin(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = flag ? 2 : 3;
        else if (state === 2) { log.push("left"); state = 4; }
        else if (state === 3) { log.push("right"); state = 4; }
        else if (state === 4) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function triangleJoin(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 4;
        else if (state == 2) { log.push("detour"); state = 4; }
        else if (state == 4) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function diamondThrowCatch(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) { log.push("left"); state = 4; }
        else if (state == 3) { log.push("right"); state = 4; }
        else if (state == 4) {
            log.push("before-throw");
            throw Error("expected");
        }
    } catch (error) {
        log.push(error.message);
        return [state, log];
    }
}
function diamondCompetingCatchRoot(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) { log.push("left"); state = 4; }
        else if (state == 3) { log.push("right"); state = 4; }
        else if (state == 4) { log.push("join"); return log; }
        else if (state == 6) state = 4;
    } catch (error) {
        log.push(error.message);
        state = 6;
    }
}
console.log(JSON.stringify([
    "diamond-join-regions",
    diamondJoin(true), diamondJoin(false),
    triangleJoin(true), triangleJoin(false),
    diamondThrowCatch(true), diamondThrowCatch(false),
    diamondCompetingCatchRoot(true), diamondCompetingCatchRoot(false)
]));


function diamondBackedge(flag) {
    const log = [];
    let state = 1, rounds = 0;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) { log.push("left"); state = 4; }
        else if (state == 3) { log.push("right"); state = 4; }
        else if (state == 4) {
            log.push("join");
            if (rounds++ < 1) state = 1;
            else return log;
        }
    } catch (error) { throw error; }
}
function diamondIndependentSideCatchRoot(flag) {
    const log = [];
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("retry"); }
            state = flag ? 2 : 3;
        } else if (state == 2) { log.push("left"); state = 4; }
        else if (state == 3) { log.push("right"); state = 4; }
        else if (state == 4) { log.push("join"); return log; }
    } catch (error) {
        log.push(error.message);
        state = 2;
    }
}
console.log(JSON.stringify([
    "diamond-cycles-and-catch-roots",
    diamondBackedge(true), diamondBackedge(false),
    diamondIndependentSideCatchRoot(true), diamondIndependentSideCatchRoot(false)
]));


function diamondWithIndependentLinearMerge(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = flag ? 2 : 3;
        else if (state === 2) { log.push("left"); state = 4; }
        else if (state === 3) { log.push("right"); state = 4; }
        else if (state === 4) { log.push("join"); state = 5; }
        else if (state === 5) { log.push("tail"); state = 6; }
        else if (state === 6) { log.push("finish"); return [state, log]; }
    } catch (error) { throw error; }
}
console.log(JSON.stringify([
    "diamond-plus-independent-linear",
    diamondWithIndependentLinearMerge(true),
    diamondWithIndependentLinearMerge(false)
]));


function multiHopDiamond(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = flag ? 2 : 3;
        else if (state === 2) { log.push("L1"); state = 5; }
        else if (state === 3) { log.push("R1"); state = 6; }
        else if (state === 5) { log.push("L2"); state = 7; }
        else if (state === 6) { log.push("R2"); state = 7; }
        else if (state === 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function multiHopTriangle(flag, extra) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 7;
        else if (state == 2) {
            if (extra) { log.push("A"); state = 5; }
            else { log.push("B"); state = 5; }
        } else if (state == 5) { log.push("detour"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function multiHopThrowCatch(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) { log.push("L1"); state = 5; }
        else if (state == 3) { log.push("R1"); state = 6; }
        else if (state == 5) { log.push("L2"); state = 7; }
        else if (state == 6) { log.push("R2"); state = 7; }
        else if (state == 7) { log.push("join"); throw Error("expected"); }
    } catch (error) {
        log.push(error.message);
        return [state, log];
    }
}
function multiHopIndependentCatchEntry(flag) {
    const log = [];
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("restart"); }
            state = flag ? 2 : 3;
        } else if (state == 2) { log.push("L1"); state = 5; }
        else if (state == 3) { log.push("R1"); state = 6; }
        else if (state == 5) { log.push("L2"); state = 7; }
        else if (state == 6) { log.push("R2"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
        else if (state == 9) state = 5;
    } catch (error) {
        log.push(error.message);
        state = 9;
    }
}
console.log(JSON.stringify([
    "multi-hop-join-regions",
    multiHopDiamond(true), multiHopDiamond(false),
    multiHopTriangle(true, true), multiHopTriangle(true, false),
    multiHopTriangle(false, false),
    multiHopThrowCatch(true), multiHopThrowCatch(false),
    multiHopIndependentCatchEntry(true),
    multiHopIndependentCatchEntry(false)
]));


function boundedMultiHopSideCycle(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) {
            log.push("loop");
            if (log.length > 2) return [state, log];
            state = 5;
        } else if (state == 5) state = 2;
        else if (state == 3) { log.push("other"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
console.log(JSON.stringify([
    "multi-hop-bounded-cycle",
    boundedMultiHopSideCycle(true),
    boundedMultiHopSideCycle(false)
]));


function branchingDagThreeWay(choice) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state === 1) state = choice === 0 ? 2 : choice === 1 ? 3 : 4;
        else if (state === 2) { log.push("a"); state = 7; }
        else if (state === 3) { log.push("b"); state = 7; }
        else if (state === 4) { log.push("c"); state = 7; }
        else if (state === 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function branchingDagNested(outer, inner) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = outer ? 2 : 3;
        else if (state == 2) state = inner ? 4 : 5;
        else if (state == 3) { log.push("right"); state = 6; }
        else if (state == 4) { { let scoped = "left"; log.push(scoped); } state = 7; }
        else if (state == 5) { log.push("middle"); state = 7; }
        else if (state == 6) { log.push("detour"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function branchingDagCatchSideEntry(choice) {
    const log = [];
    let state = 1, first = true;
    while (true) try {
        if (state == 1) {
            if (first) { first = false; throw Error("restart"); }
            state = choice === 0 ? 2 : choice === 1 ? 3 : 4;
        } else if (state == 2) { log.push("a"); state = 7; }
        else if (state == 3) { log.push("b"); state = 7; }
        else if (state == 4) { log.push("c"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
        else if (state == 9) state = 4;
    } catch (error) { log.push(error.message); state = 9; }
}
function branchingDagCycle(flag) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = flag ? 2 : 3;
        else if (state == 2) { log.push("spin"); state = log.length > 2 ? 7 : 4; }
        else if (state == 4) state = 2;
        else if (state == 3) { log.push("other"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
    } catch (error) { throw error; }
}
function branchingDagThrowingCase(choice) {
    const log = [];
    let state = 1;
    while (true) try {
        if (state == 1) state = choice === 0 ? 2 : choice === 1 ? 3 : 4;
        else if (state == 2) { log.push("a"); state = 7; }
        else if (state == 3) { log.push("throw"); throw Error("expected"); state = 7; }
        else if (state == 4) { log.push("c"); state = 7; }
        else if (state == 7) { log.push("join"); return [state, log]; }
    } catch (error) { log.push(error.message); return [state, log]; }
}
console.log(JSON.stringify([
    "branching-dag-regions",
    branchingDagThreeWay(0), branchingDagThreeWay(1), branchingDagThreeWay(2),
    branchingDagNested(true, true), branchingDagNested(true, false),
    branchingDagNested(false, true), branchingDagNested(false, false),
    branchingDagCatchSideEntry(0), branchingDagCatchSideEntry(1), branchingDagCatchSideEntry(2),
    branchingDagCycle(true), branchingDagCycle(false),
    branchingDagThrowingCase(0), branchingDagThrowingCase(1), branchingDagThrowingCase(2)
]));


function caughtSameStateRetry() {
    let state = 1;
    let attempts = 0, caught = 0;
    while (true) try {
        if (state == 1) state = 2;
        else if (state == 2) {
            attempts++;
            if (attempts == 1) throw Error("retry");
            state = 3;
        } else if (state == 3) return [state, attempts, caught];
    } catch (error) { caught++; }
}
console.log(JSON.stringify(["implicit-catch-retry", caughtSameStateRetry()]));


function caughtIntermediateStateRetry() {
    let state = 1;
    let attempts = 0, caught = 0;
    while (true) try {
        if (state == 1) {
            state = 2;
            attempts++;
            if (attempts == 1) throw Error("retry");
            state = 3;
        } else if (state == 2) {
            return ["resumed-intermediate", state, attempts, caught];
        } else if (state == 3) {
            return ["normal", state, attempts, caught];
        }
    } catch (error) { caught++; }
}
console.log(JSON.stringify(["intermediate-catch-retry", caughtIntermediateStateRetry()]));


function exhaustiveCatchFiniteDomain(flag, throwEffect) {
    let state = 1;
    let selector = 46;
    const log = [];
    while (true) try {
        if (state == 1) { if (flag) selector = 92; state = 2; }
        else if (state == 2) {
            log.push("effect");
            if (throwEffect) throw Error("expected");
            state = 3;
        } else if (state == 3) return [state, selector, log];
    } catch (error) {
        if (selector === 46) throw error;
        if (selector == 92) { log.push("caught"); state = 3; }
    }
}
function nonexhaustiveCatchFiniteDomain() {
    let state = 1;
    let selector = 46;
    let attempts = 0;
    while (true) try {
        if (state == 1) { selector = 13; state = 2; }
        else if (state == 2) {
            if (attempts++ === 0) throw Error("retry");
            state = 3;
        } else if (state == 3) return [state, attempts];
    } catch (error) {
        if (selector == 46) throw error;
        if (selector == 92) state = 3;
    }
}
console.log(JSON.stringify([
    "finite-catch-domain",
    exhaustiveCatchFiniteDomain(false, false),
    exhaustiveCatchFiniteDomain(true, false),
    exhaustiveCatchFiniteDomain(true, true),
    nonexhaustiveCatchFiniteDomain()
]));
try {
    exhaustiveCatchFiniteDomain(false, true);
    console.log("unexpected-throw-survival");
} catch (error) {
    console.log(JSON.stringify(["finite-catch-rethrow", error.message]));
}


function capturedSelectorMutatorCatchRetry() {
    let state = 1;
    let selector = 46;
    let change;
    let attempts = 0;
    const log = [];
    while (true) try {
        if (state == 1) {
            change = () => { selector = 46; };
            selector = 92;
            state = 2;
        } else if (state == 2) {
            log.push("effect");
            if (attempts++ == 0) throw Error("retry");
            state = 3;
        } else if (state == 3) return [state, selector, attempts, log];
    } catch (error) {
        if (selector == 46) throw error;
        change();
        if (selector == 92) state = 3;
    }
}
console.log(JSON.stringify(["captured-selector-mutation", capturedSelectorMutatorCatchRetry()]));


function exhaustiveShortCircuitCatch(flag, shouldThrow) {
    let state = 1;
    let selector = 46;
    let observed;
    const log = [];
    while (true) try {
        if (state == 1) { if (flag) selector = 92; state = 2; }
        else if (state == 2) {
            log.push("effect");
            if (shouldThrow) throw Error("expected");
            state = 3;
        } else if (state == 3) return [state, observed, log];
    } catch (error) {
        if (selector == 46) throw error;
        selector == 92 && (observed = error.message, state = 3);
    }
}
function nonexhaustiveShortCircuitCatch() {
    let state = 1;
    let selector = 92;
    let attempts = 0;
    while (true) try {
        if (state == 1) state = 2;
        else if (state == 2) {
            if (attempts++ == 0) throw Error("retry");
            state = 3;
        } else if (state == 3) return [state, attempts];
    } catch (error) {
        if (selector == 46) throw error;
        selector == 92 || (state = 3);
    }
}
console.log(JSON.stringify([
    "catch-short-circuit",
    exhaustiveShortCircuitCatch(false, false),
    exhaustiveShortCircuitCatch(true, false),
    exhaustiveShortCircuitCatch(true, true),
    nonexhaustiveShortCircuitCatch()
]));
try {
    exhaustiveShortCircuitCatch(false, true);
    console.log("bad-unhandled-throw");
} catch (error) {
    console.log(JSON.stringify(["catch-short-circuit-rethrow", error.message]));
}


function uniqueNaturalLoopBackedge(limit) {
    let state = 1, count = 0, log = [];
    while (true) try {
        if (state == 1) state = count < limit ? 2 : 3;
        else if (state == 2) { log.push(count); count++; state = 1; }
        else if (state == 3) return [state, count, log];
    } catch (error) { throw error; }
}
function twoHopNaturalLoopBackedge(limit, abort) {
    let state = 1, count = 0, log = [];
    while (true) try {
        if (state === 1) state = count < limit ? 2 : 3;
        else if (state === 2) { log.push("side"); state = 4; }
        else if (state === 4) {
            log.push("tail");
            if (abort) throw Error("expected");
            count++;
            state = 1;
        } else if (state === 3) return [state, count, log];
    } catch (error) { return [state, error.message, log]; }
}
function multiEntryNaturalLoopReject(limit) {
    let state = 1, count = 0, log = [];
    while (true) try {
        if (state == 1) state = count < limit ? 2 : 3;
        else if (state == 2) { log.push(count); count++; state = 1; }
        else if (state == 3) return [state, count, log];
        else if (state == 4) state = 2;
    } catch (error) { state = 4; }
}
console.log(JSON.stringify([
    "exception-scc-backedge",
    uniqueNaturalLoopBackedge(0), uniqueNaturalLoopBackedge(1), uniqueNaturalLoopBackedge(4),
    twoHopNaturalLoopBackedge(0, false), twoHopNaturalLoopBackedge(2, false),
    twoHopNaturalLoopBackedge(2, true), multiEntryNaturalLoopReject(3)
]));


function multiDeclaratorInitializerOverwrite() {
    const log = [];
    let state = 1, other = (state = 2);
    while (true) try {
        if (state == 1) { log.push("wrong"); return log; }
        else if (state == 2) { log.push("correct"); return log; }
    } catch (error) { throw error; }
}
function multiDeclaratorInitializerSecond(limit) {
    const log = [];
    let count = 0, state = 1;
    while (true) try {
        if (state == 1) state = count < limit ? 2 : 3;
        else if (state == 2) { log.push(count); count++; state = 1; }
        else if (state == 3) return [count, log];
    } catch (error) { throw error; }
}
console.log(JSON.stringify([
    "declarator-binding-spans", multiDeclaratorInitializerOverwrite(),
    multiDeclaratorInitializerSecond(0), multiDeclaratorInitializerSecond(3)
]));
