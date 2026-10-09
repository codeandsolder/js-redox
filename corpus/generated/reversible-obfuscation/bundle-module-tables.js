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

if (typeof define === "function") {
  define("amd/alpha", ["require", "exports", "amd/beta"], function (require, exports, beta) {
    exports.value = beta.value;
  });
  define("amd/beta", ["require", "exports"], function (require, exports) {
    exports.value = "beta";
  });
}

(function (define) {
  define("amd/local", ["require", "exports"], function (require, exports) {
    exports.local = true;
  });
  define("not-amd/local-helper", ["dep"], function (dep) {
    return dep;
  });
})(function () {});


(function () {
  const embeddedLoader = {};
  function embeddedDefine() {}
  embeddedDefine.amd = { embedded: true };
  embeddedLoader.require = function (name) { return name; };
  embeddedLoader.requirejs = embeddedLoader.require;
  embeddedLoader.define = embeddedDefine;
  embeddedLoader.define("embedded/alpha", ["embedded/beta"], function (beta) {
    return { value: beta.value };
  });
  embeddedLoader.define("embedded/beta", [], function () {
    return { value: "beta" };
  });
  embeddedLoader.define("embedded/no-deps", function () {
    return { value: "no-deps" };
  });

  const arbitrary = {
    define(name, deps, factory) {
      return factory(deps[0]);
    }
  };
  arbitrary.define("not-amd/member-helper", ["dep"], function (dep) {
    return dep;
  });

  const loaderLike = {};
  loaderLike.require = function (name) { return name; };
  loaderLike.define = function (name, deps, factory) { return factory(deps[0]); };
  loaderLike.define("not-amd/single-loaderlike", ["dep"], function (dep) {
    return dep;
  });

  const loadModulesLoader = {};
  loadModulesLoader.loadModules = function () {};
  loadModulesLoader.define = function () {};
  loadModulesLoader.define("loadmodules/alpha", ["loadmodules/beta"], (function (beta) {
    return beta;
  }));
  loadModulesLoader.define("loadmodules/beta", [], (function () {
    return { value: "beta" };
  }));
})();

GlobalLoader.define("global/alpha", ["global/beta"], (function (beta) {
  return beta;
}));
GlobalLoader.define("global/beta", [], function () {
  return { value: "beta" };
});

customElements.define("not-module-inline-function", function () {
  return "not a module factory";
});

!function browserify(modules, cache, entries) {
  function load(id) {
    if (cache[id]) return cache[id].exports;
    const module = cache[id] = { exports: {} };
    const tuple = modules[id];
    function localRequire(name) {
      return load(tuple[1][name]);
    }
    tuple[0](localRequire, module, module.exports);
    return module.exports;
  }
  for (let i = 0; i < entries.length; i++) load(entries[i]);
}({
  50001: [function (require, module, exports) {
    exports.value = require("./beta").value;
    void require("external-package");
  }, { "./beta": 50002, "external-package": "external-package" }],
  50002: [function (require, module, exports) {
    module.exports = { value: "beta" };
  }, {}]
}, {}, [50001]);


(function () {
  function browserifyReturned(modules, cache, entries) {
    function load(id) {
      if (cache[id]) return cache[id].exports;
      const module = cache[id] = { exports: {} };
      const tuple = modules[id];
      function localRequire(name) {
        return load(tuple[1][name]);
      }
      tuple[0](localRequire, module, module.exports);
      return module.exports;
    }
    for (let i = 0; i < entries.length; i++) load(entries[i]);
    return load;
  }
  return browserifyReturned;
})()({
  51001: [function (require, module, exports) {
    exports.value = require("./beta").value;
  }, { "./beta": 51002, "external-missing": undefined }],
  51002: [function (require, module, exports) {
    module.exports = { value: "returned-bootstrap" };
  }, {}]
}, {}, [51001]);

(function () {
  let mutableBootstrap = function (modules, cache, entries) {
    return [modules, cache, entries];
  };
  return mutableBootstrap;
})()({
  52001: [function (require, module, exports) {
    exports.value = require("./beta").value;
  }, { "./beta": 52002 }],
  52002: [function (require, module, exports) {
    module.exports = { value: "must-not-detect" };
  }, {}]
}, {}, [52001]);


const __webpack_modules__ = {
  rspA(module, exports, require) {
    exports.value = require("rspB").value;
  },
  rspB(module, exports) {
    module.exports = { value: "rspack-style" };
  }
};
void __webpack_modules__;

(function () {
  const __webpack_modules__ = {
    mustNotDetect: 123
  };
  void __webpack_modules__;
})();

(function () {
  const runtimeTable = {
    runA(module, exports, require) {
      exports.value = require("runB").value;
    },
    runB(module, exports) {
      module.exports = { value: "runtime-table" };
    }
  };
  const cache = {};
  function runtimeRequire(id) {
    if (cache[id]) return cache[id].exports;
    const module = cache[id] = { exports: {} };
    runtimeTable[id](module, module.exports, runtimeRequire);
    return module.exports;
  }
  runtimeRequire.m = runtimeTable;
  void runtimeRequire("runA");
})();

!function (modules) {
  const cache = {};
  function legacyRequire(id) {
    if (cache[id]) return cache[id].exports;
    const module = cache[id] = { exports: {} };
    modules[id].call(module.exports, module, module.exports, legacyRequire);
    return module.exports;
  }
  legacyRequire.m = modules;
  void legacyRequire(0);
}([
  function (module, exports, require) {
    exports.value = require(1).value;
  },
  function (module) {
    module.exports = { value: "array-table" };
  }
]);

(function (modules) {
  function ordinaryLoader(id) {
    return modules[id];
  }
  void ordinaryLoader(0);
})([
  function () {
    return "must-not-detect-array";
  }
]);


webpackJsonp([91], {
  jsonpA: function (module, exports, require) {
    exports.value = require("jsonpB").value;
  },
  jsonpB: function (module) {
    module.exports = { value: "jsonp-object" };
  }
});

webpackJsonp([92], [
  ,
  function (module, exports, require) {
    exports.value = require(2).value;
  },
  function (module) {
    module.exports = { value: "jsonp-sparse-array" };
  }
]);

(function () {
  function webpackJsonp(chunkIds, table) {
    return [chunkIds, table];
  }
  webpackJsonp([93], {
    jsonpShadow: function () {
      return "must-not-detect";
    }
  });
})();


(function () {
  const __webpack_modules__ = [
    function (module, exports, require) {
      exports.namedArray = require(1).namedArray;
    },
    function (module) {
      module.exports = { namedArray: "named-array-table" };
    }
  ];
  void __webpack_modules__;
})();

((modules) => {
  const cache = {};
  function arrowRequire(id) {
    if (cache[id]) return cache[id].exports;
    const module = cache[id] = { exports: {} };
    modules[id].call(module.exports, module, module.exports, arrowRequire);
    return module.exports;
  }
  arrowRequire.m = modules;
  void arrowRequire(3);
})([
  ,
  ,
  ,
  function (module, exports, require) {
    exports.arrowValue = require(4).arrowValue;
  },
  function (module) {
    module.exports = { arrowValue: "arrow-array-table" };
  }
]);

((modules) => {
  function ordinaryArrowLoader(id) {
    return modules[id];
  }
  void ordinaryArrowLoader(7);
})([
  ,
  ,
  ,
  ,
  ,
  ,
  ,
  function () {
    return "must-not-detect-arrow-array";
  }
]);


(window.webpackJsonp = window.webpackJsonp || []).push([[94], [
  ,
  ,
  ,
  ,
  ,
  function (module, exports, require) {
    exports.pushArray = require(6).pushArray;
  },
  function (module) {
    module.exports = { pushArray: "push-array-table" };
  }
]]);

const ordinaryChunkSink = [];
ordinaryChunkSink.push([[95], [
  ,
  ,
  ,
  ,
  ,
  ,
  ,
  ,
  function () {
    return "must-not-detect-generic-push-array";
  }
]]);


const notwebpackJsonpQueue = [];
notwebpackJsonpQueue.push([[96], [
  function () {
    return "must-not-detect-substring-push-array";
  }
]]);


(window.wsc_webpackJsonp = window.wsc_webpackJsonp || []).push([[97], [
  function (module) {
    module.exports = { namespacedPush: "namespaced-webpack-queue" };
  }
]]);


!function (modules) {
  function objectBootstrapRequire(id) {
    const module = { exports: {} };
    modules[id](module, module.exports, objectBootstrapRequire);
    return module.exports;
  }
  objectBootstrapRequire.m = modules;
  void objectBootstrapRequire("objectBootstrapA");
}({
  objectBootstrapA: function (module, exports, require) {
    exports.value = require("objectBootstrapB").value;
  },
  objectBootstrapB: function (module) {
    module.exports = { value: "object-bootstrap" };
  }
});

(window.webpackChunkConcat = window.webpackChunkConcat || []).push([[99], Array(3).concat([
  function (module, exports, require) {
    exports.concatValue = require(4).concatValue;
  },
  function (module) {
    module.exports = { concatValue: "offset-concat-table" };
  }
])]);

(window.webpackChunkConcat = window.webpackChunkConcat || []).push([[100], Array(window.dynamicWebpackOffset).concat([
  function () {
    return "must-not-detect-dynamic-concat-offset";
  }
])]);

webpackJsonpFirebase([98], {
  firebaseA: function (module, exports, require) {
    exports.value = require("firebaseB").value;
  },
  firebaseB: function (module) {
    module.exports = { value: "firebase-jsonp" };
  }
});

(function () {
  function webpackJsonpFirebase(chunkIds, table) {
    return [chunkIds, table];
  }
  webpackJsonpFirebase([101], {
    firebaseShadow: function () {
      return "must-not-detect-shadowed-firebase";
    }
  });
})();
