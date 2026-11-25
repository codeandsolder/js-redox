function f(log) {
    let state=1;
    while((state=99,true)) try {
        if(state==1) return "initial";
        else if(state==99) return "condition";
        else if(state==2) return "other";
    } catch(error) { state=2; }
}
