const factory = (function () {
    let armed = !![];
    return function (context, callback) {
        const invoke = callback ? function () {
            return callback.apply(context, arguments);
        } : function () {};
        return invoke;
    };
})();

factory(null, function () { return 7; })();
