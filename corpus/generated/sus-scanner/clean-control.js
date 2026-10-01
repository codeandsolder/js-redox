export function formatUser(user) {
  const pieces = [user.firstName, user.lastName].filter(Boolean);
  return pieces.join(" ");
}

export function total(items) {
  return items.reduce((sum, item) => sum + item.price, 0);
}

export function findById(items, id) {
  return items.find((item) => item.id === id);
}

console.log(formatUser({ firstName: "Ada", lastName: "Lovelace" }));
