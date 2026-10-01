function returnsFalse() {
  return!1;
}

function returnsTrue() {
  return!0;
}

function throwsTrue() {
  try {
    throw!0;
  } catch (value) {
    return value;
  }
}

console.log(returnsFalse(), returnsTrue(), throwsTrue());
