
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
