const prefix = "hel";
const greeting = prefix + "lo";
const forty = 20 + 20;
const answer = forty + 2;
const record = { answer };

function shadowed() {
  const answer = 1;
  const alias = answer;
  return alias + 1;
}

function sourceBeforeDeclaration() {
  return later;
}
const later = 7;

console.log(greeting, answer, shadowed(), record.answer, sourceBeforeDeclaration());
