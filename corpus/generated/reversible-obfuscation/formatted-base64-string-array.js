(function () {
  function p() {
    var table = ["CMvSB2fK", "mJq1ndi0rKHuthnj", "nNH1rKHOuq", "y29VA2LL"];
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
          for (var q = 0, r, ch, i = 0;
            ch = s.charAt(i++);
            ~ch && (r = q % 4 ? r * 64 + ch : ch, q++ % 4)
              ? bytes += String.fromCharCode(255 & r >> (-2 * q & 6))
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

  (function (provider, target) {
    var G = d, t = provider();
    while (true) {
      try {
        var checksum = parseInt(G(0x10)) * 10 + parseInt(G(0x11));
        if (checksum === target) break;
        else t.push(t.shift());
      } catch (e) {
        t.push(t.shift());
      }
    }
  })(p, 2454246);

  const alias = d;
  console.log(alias(0x12), d(0x13));
})();
