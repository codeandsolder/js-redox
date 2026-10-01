(() => {
  var modules = {
  10000: function (module, exports, require) { exports.value = 0; },
  10001: function (module, exports, require) { exports.value = 1; },
  10002: function (module, exports, require) { exports.value = 2; },
  10003: function (module, exports, require) { exports.value = 3; },
  10004: function (module, exports, require) { exports.value = 4; },
  10005: function (module, exports, require) { exports.value = 5; },
  10006: function (module, exports, require) { exports.value = 6; },
  10007: function (module, exports, require) { exports.value = 7; },
  10008: function (module, exports, require) { exports.value = 8; },
  10009: function (module, exports, require) { exports.value = 9; },
  10010: function (module, exports, require) { exports.value = 10; },
  10011: function (module, exports, require) { exports.value = 11; },
  10012: function (module, exports, require) { exports.value = 12; },
  10013: function (module, exports, require) { exports.value = 13; },
  10014: function (module, exports, require) { exports.value = 14; },
  10015: function (module, exports, require) { exports.value = 15; }
  };
  globalThis.__directBundleFixture = modules;
})();

(self.webpackChunkFixture = self.webpackChunkFixture || []).push([
  [77],
  {
    20001: function (module, exports, require) { exports.name = "a"; },
    20002: (module, exports, require) => { exports.name = "b"; }
  }
]);
