(function () {
    var rt = ["Y29va2ll", "cmVsb2Fk"];
    var ct = ["us49uStFKk5Z", 17, true, null, "u", "u!s@4#9", "Z"];

    function Q(t, n) {
        return n = rt[t], atob(n);
    }

    function C(t, n) {
        if ("string" != typeof (n = ct[t])) return n;
        for (
            var i, o, e, r, c, u, s = void 0,
                a = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
                f = 0,
                d = (d = n).replace(/[^A-Za-z0-9\+\/\=]/g, s = "");
            f < d.length;
        )
            o = a.indexOf(d.charAt(f++)),
            u = (15 & (c = a.indexOf(d.charAt(f++)))) << 4 | (r = a.indexOf(d.charAt(f++))) >> 2,
            i = (3 & r) << 6 | (e = a.indexOf(d.charAt(f++))),
            s += String.fromCharCode(o << 2 | c >> 4),
            64 != r && (s += String.fromCharCode(u)),
            64 != e && (s += String.fromCharCode(i));
        return s;
    }

    var fixedSide = 0;
    var fixedSideTable = ["us49uStFKk5Z"];
    function CFixedSide(t, n) {
        if ("string" != typeof (n = fixedSideTable[t])) return n;
        for (
            var i, o, e, r, c, u, s = void 0,
                a = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
                f = 0,
                d = (d = n).replace(/[^A-Za-z0-9\+\/\=]/g, s = "");
            f < d.length;
        )
            fixedSide += 1,
            o = a.indexOf(d.charAt(f++)),
            u = (15 & (c = a.indexOf(d.charAt(f++)))) << 4 | (r = a.indexOf(d.charAt(f++))) >> 2,
            i = (3 & r) << 6 | (e = a.indexOf(d.charAt(f++))),
            s += String.fromCharCode(o << 2 | c >> 4),
            64 != r && (s += String.fromCharCode(u)),
            64 != e && (s += String.fromCharCode(i));
        return s;
    }

    function F(t, n) {
        return -3 * (t & n) - 6 * (t & ~n) + 5 * (t | ~n) + 2 * ~(t & n) - 7 * ~(t | n) - 1 * ~(t | ~n);
    }

    function strictEq(t, n) {
        return t === n;
    }

    function bitOr(t, n) {
        return t | n;
    }

    function reassigned(t, n) {
        return t + n;
    }
    reassigned = function(t, n) {
        return t - n;
    };

    var invalid = ["A"];
    function QInvalid(t, n) {
        return n = invalid[t], atob(n);
    }

    var decoyStandard = ["bm90LWRlY29kZWQ="];
    function QDecoy(t, n) {
        n = decoyStandard[t];
        atob("YQ==");
        return n;
    }

    var decoyCustom = ["dGhpcy1tdXN0LXN0YXktcmF3"];
    function CDecoy(t, n) {
        n = decoyCustom[t];
        var alphabet = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ";
        alphabet.indexOf(n.charAt(0));
        String.fromCharCode(65);
        return n;
    }

    var escapedTable = ["YQ=="];
    function QEscaped(t, n) {
        return n = escapedTable[t], atob(n);
    }
    var escapedAlias = escapedTable;
    escapedAlias[0] = "Yg==";

    var internalEscapedTable = ["YQ=="];
    function QInternalEscaped(t, n) {
        var alias = internalEscapedTable;
        alias[0] = "Yw==";
        return n = internalEscapedTable[t], atob(n);
    }

    var reassignedTable = ["YQ=="];
    function QReassigned(t, n) {
        return n = reassignedTable[t], atob(n);
    }
    QReassigned = function() {
        return "x";
    };

    var sideEffect = 0;
    var sideTable = ["YQ=="];
    function QSideEffect(t, n) {
        sideEffect += 1;
        return n = sideTable[t], atob(n);
    }

    var dynamicChoice = typeof process === "undefined";

    var invalidResult;
    try {
        QInvalid(0);
        invalidResult = "accepted";
    } catch (_) {
        invalidResult = "invalid";
    }

    console.log(
        Q(0),
        Q(1),
        C(0),
        C(1),
        C(2),
        C(3),
        invalidResult,
        QDecoy(0),
        CDecoy(0),
        C(F(0, 1)),
        strictEq(-0, 0),
        strictEq(0 / 0, 0 / 0),
        bitOr(4294967297, 0),
        reassigned(5, 2),
        C(4).length,
        C(4).charCodeAt(0),
        C(4).charCodeAt(1),
        C(4).charCodeAt(2),
        C(5),
        C(6).length,
        C(6).charCodeAt(0),
        C(bitOr(7, 0)),
        QEscaped(0),
        QInternalEscaped(0),
        QReassigned(0),
        QSideEffect(0),
        sideEffect,
        C(dynamicChoice ? 0 : 1),
        C(dynamicChoice ? 0 : 7),
        CFixedSide(0),
        fixedSide
    );
})();
