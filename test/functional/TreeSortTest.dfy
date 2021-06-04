include "../../src/functional/TreeSort.dfy"

method Main() {
  Test_TreeSort();
  Test_Lemma_TreeSortListIsOrdered();
  Test_Lemma_TreeSortSameElemsThanList();
}

method Test_TreeSort() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  var sorted := TreeSort(list);
  var expected := Cons(2, Cons(4, Cons(7, Cons(10, Cons(12, List_Empty)))));
  assert expected == sorted;
}

method Test_Lemma_TreeSortListIsOrdered() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  { Lemma_TreeSortListIsOrdered(list); }
  assert list_is_ordered(TreeSort(list));
}

method Test_Lemma_TreeSortSameElemsThanList() {
  var list := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  { Lemma_TreeSortSameElemsThanList(list); }
  assert List_ToMultiset(TreeSort(list)) == List_ToMultiset(list);
}
