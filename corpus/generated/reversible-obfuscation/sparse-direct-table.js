(function () {
    var sideEffects = 0;
    function standardDynamic() {
        sideEffects += 1;
        return "Yw==";
    }
    function customDynamic() {
        sideEffects += 1;
        return 99;
    }

    var standard = ["YQ==", standardDynamic(), "Yg=="];
    function QSparse(t, n) {
        return n = standard[t], atob(n);
    }

    var custom = ["us49uStFKk5Z", customDynamic(), 17];
    function CSparse(t, n) {
        if ("string" != typeof (n = custom[t])) return n;
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


    var nestedTable = ["us49uStFKk5Z", customDynamic()];
    function INested(t) {
        var n = nestedTable[t];
        return "string" == typeof n ? function(n, i, o, e) {
            var r, c, u, x,
                s = "318mC4sQfF7VWJ/h5AiBOtzHogbKun2jvxwlp6NkXD=eUraRTy9+GcS0qYEIdLMPZ",
                a = "";
            for (i = 0, n = n.replace(/[^A-Za-z0-9\+\/\=]/g, ""); i < n.length;) {
                e = s.indexOf(n.charAt(i++)) << 2 | (o = s.indexOf(n.charAt(i++))) >> 4;
                c = (15 & o) << 4 | (u = s.indexOf(n.charAt(i++))) >> 2;
                r = (3 & u) << 6 | (x = s.indexOf(n.charAt(i++)));
                a += String.fromCharCode(e);
                64 != u && (a += String.fromCharCode(c));
                64 != x && (a += String.fromCharCode(r));
            }
            return a;
        }(n) : n;
    }
    function nestedCaller() {
        return INested(0);
    }

    console.log(
        QSparse(0),
        QSparse(2),
        CSparse(0),
        CSparse(2),
        QSparse(1),
        CSparse(1),
        nestedCaller(),
        INested(1),
        sideEffects
    );
})();
