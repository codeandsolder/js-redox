function getArray(root) {
  return root.Array;
}
function identity(root) {
  return root;
}
function install(resolver, sourceProperty, targetSelector, aliasProperty) {
  void resolver;
  void sourceProperty;
  void targetSelector;
  void aliasProperty;
}
install(getArray, "push", 1, "f2AA");
install(identity, "__residual", 0, "i2AA");
console.log("ok");
