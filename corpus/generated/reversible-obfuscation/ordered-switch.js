const order = "2|0|3|1".split("|");
let index = 0;
const out = [];
while (!![]) {
  switch (order[index++]) {
    case "0":
      out.push("B");
      continue;
    case "1":
      out.push("D");
      continue;
    case "2":
      out.push("A");
      continue;
    case "3":
      out.push("C");
      continue;
  }
  break;
}
console.log(out.join(""));
