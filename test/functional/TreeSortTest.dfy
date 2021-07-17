include "../../src/functional/TreeSort.dfy"

method Main() {
  Test_TreeSort();
  Test_Lemma_TreeSortOrdering();
  Test_Lemma_TreeSortIntegrity();
}

method Test_TreeSort() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  var sorted := TreeSort(list);
  var expected := Cons(2, Cons(4, Cons(7, Cons(10, Cons(12, List_Empty)))));
  assert expected == sorted;
}

method Test_Lemma_TreeSortOrdering() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  { Lemma_TreeSortOrdering(list); }
  assert list_ordered(TreeSort(list));
}

method Test_Lemma_TreeSortIntegrity() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  { Lemma_TreeSortIntegrity(list); }
  assert List_ToMultiset(TreeSort(list)) == List_ToMultiset(list);
}
