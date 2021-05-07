include "../../../src/data-types/list/List.dfy"

method Main() {
  InsertIntoListTest();
  ConcatTwoListsTest();
}

method InsertIntoListTest() {
  var list: List<int> := List_Empty;
  list := List_Insert(list, 2);
  list := List_Insert(list, 10);
  list := List_Insert(list, 4);
  list := List_Insert(list, 12);
  list := List_Insert(list, 7);

  assert(list == Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty))))));
}

method ConcatTwoListsTest() {
  var a: List<int> := List_Empty;
  a := List_Insert(a, 2);
  a := List_Insert(a, 10);

  var b: List<int> := List_Empty;
  b := List_Insert(b, 4);
  b := List_Insert(b, 12);
  b := List_Insert(b, 7);

  var c := List_Concat(a, b);
  assert(c == Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty))))));
}
