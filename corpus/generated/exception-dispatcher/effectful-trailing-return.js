function f(log) {
    let state=1;
    while(true) try {
        if(state==99){log.push("dead");state=30;}
        else if(state==1)state=30;
        if(state==30)return log.push("done");
    } catch(error) {throw error;}
}
