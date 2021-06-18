include "../../src/imperative/TreeSort.dfy"

method Main() {
  Test_TreeSort();
}

method Test_TreeSort() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  var sorted := TreeSort(list);
  List_Print(sorted);
}
