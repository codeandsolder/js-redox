(function () {
  function p() {
    var table = ["y29VA2LL"];
    p = function () {
      return table;
    };
    return p();
  }

  function d(a, b) {
    var c = p();
    return d = function (x, y) {
      x = x - 0x10;
      var v = c[x];
      if (d.ready === undefined) {
        var decode = function (s) {
          var alphabet = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789+/=";
          var bytes = "";
          var uri = "";
          var helper = "" + decode;
          for (var q = 0, r, ch, i = 0;
            ch = s.charAt(i++);
            ~ch && (r = q % 4 ? r * 64 + ch : ch, q++ % 4)
              ? bytes += helper.charCodeAt(0) === 0
                ? String.fromCharCode(0)
                : String.fromCharCode(255 & r >> (-2 * q & 6))
              : 0) {
            ch = alphabet.indexOf(ch);
          }
          for (var j = 0; j < bytes.length; j++) {
            uri += "%" + ("00" + bytes.charCodeAt(j).toString(16)).slice(-2);
          }
          return decodeURIComponent(uri);
        };
        d.decode = decode;
        d.ready = true;
      }
      v = d.decode(v);
      return v;
    }, d(a, b);
  }

  console.log(d(0x10));
})();
