function f(log) {
    let state=57;
    while(true) try {
        if(state==99){log.push("dead");state=30;}
        else if(state==57)state=73;
        else if(state==73)state=30;
        if(state==30)return log;
    } catch(error) { throw error; }
}
