include "../../src/functional/TreeSort.dfy"

method Main() {
  TreeSortTest();
}

method TreeSortTest() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  var sorted := TreeSort(list, Leaf);
  List_Print(sorted);
}
