(function () {
    const c = String.fromCharCode;
    const folded = "A" + c(66) + c(67);
    const astral = c(0xd83d, 0xde00);
    const unpaired = c(0xd800);
    let blockFolded;
    {
        blockFolded = c(68);
    }

    let mutable = String.fromCharCode;
    mutable = function (value) { return "mut:" + value; };

    function useBeforeInit(flag) {
        if (flag) return before(65);
        var before = String.fromCharCode;
        return "ok";
    }
    globalThis.__keepFromCharCodeBeforeInit = useBeforeInit;

    function nestedAlias() {
        const outer = String.fromCharCode;
        function helper() { return outer(65); }
        return helper;
    }
    globalThis.__keepNestedFromCharCodeAlias = nestedAlias;

    console.log(folded, astral, unpaired.length, blockFolded, mutable(65), useBeforeInit(false));
})();
