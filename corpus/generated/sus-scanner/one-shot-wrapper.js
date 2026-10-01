const once = (function () {
    let armed = !![];
    return function (context, callback) {
        const invoke = armed ? function () {
            if (callback) {
                return callback.apply(context, arguments);
            }
        } : function () {};
        return armed = ![], invoke;
    };
})();

once(null, function () { return 7; })();
