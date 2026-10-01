const order = ["0", "1"];
let index = 0;
order.reverse();
const out = [];
while (true) {
  switch (order[index++]) {
    case "0":
      out.push("A");
      continue;
    case "1":
      out.push("B");
      continue;
  }
  break;
}
console.log(out.join(""));
