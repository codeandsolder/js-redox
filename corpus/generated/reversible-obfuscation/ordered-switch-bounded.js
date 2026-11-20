const out = [];
for (let order = [1, "1", true, 0], index = 0; true;) {
  switch (order[index++]) {
    case "1": out.push("B"); continue;
    case 1: out.push("A"); continue;
    case true: out.push("C"); continue;
    case 0: out.push("D"); break;
  }
  break;
}
console.log(out.join(""));
