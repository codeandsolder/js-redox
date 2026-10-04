(() => {
  const unicodeOffsetFixture = "µ";
  void unicodeOffsetFixture;
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
    20001: function (module, exports, require) {
      exports.name = require(20002).name;
      function registerNamedExport() {
        require.d(exports, { named: () => exports.name });
      }
      function shadowRequire(require) {
        return require(29999);
      }
      function shadowExports(exports) {
        exports.shadowed = true;
      }
      const nestedModules = {
        40000: function (module, exports, require) { exports.inner = "private"; },
        41000: function (module, exports, require) { exports.value = 0; },
        41001: function (module, exports, require) { exports.value = 1; },
        41002: function (module, exports, require) { exports.value = 2; },
        41003: function (module, exports, require) { exports.value = 3; },
        41004: function (module, exports, require) { exports.value = 4; },
        41005: function (module, exports, require) { exports.value = 5; },
        41006: function (module, exports, require) { exports.value = 6; },
        41007: function (module, exports, require) { exports.value = 7; },
        41008: function (module, exports, require) { exports.value = 8; },
        41009: function (module, exports, require) { exports.value = 9; },
        41010: function (module, exports, require) { exports.value = 10; },
        41011: function (module, exports, require) { exports.value = 11; },
        41012: function (module, exports, require) { exports.value = 12; },
        41013: function (module, exports, require) { exports.value = 13; },
        41014: function (module, exports, require) { exports.value = 14; }
      };
      require(40000);
      void registerNamedExport;
      void shadowRequire;
      void shadowExports;
      void nestedModules;
    },
    20002: ((module, exports, require) => {
      module.exports = { name: "b" };
    })
  }
]);

(self.webpackChunkFixture = self.webpackChunkFixture || []).push([
  [78],
  {
    40000: function (module, exports, require) {
      exports.peer = "peer";
    }
  }
]);
