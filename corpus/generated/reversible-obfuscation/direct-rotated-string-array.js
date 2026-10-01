(function () {
  function tableProvider() {
    var table = ["11cookie", "22reload", "33open", "44close"];
    tableProvider = function () {
      return table;
    };
    return tableProvider();
  }

  function decode(index, unused) {
    index = index - 100;
    const table = tableProvider();
    let value = table[index];
    return value;
  }

  (function (provider, target) {
    const alias = decode;
    const table = provider();
    while (true) {
      try {
        const checksum = parseInt(alias(100)) * 10 + parseInt(alias(101));
        if (checksum === target) break;
        else table.push(table.shift());
      } catch (error) {
        table.push(table.shift());
      }
    }
  })(tableProvider, 253);

  const alias1 = decode;
  const alias2 = alias1;

  function dynamicLookup(index) {
    return alias1(index);
  }

  console.log(alias1(102), alias2(103), dynamicLookup(100));
})();
