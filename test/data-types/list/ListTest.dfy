include "../../../src/data-types/list/List.dfy"

method Main() {
  InsertIntoListTest();
  ConcatTwoListsTest();
  SizeZeroTest();
  SizeTest();
}

method InsertIntoListTest() {
  var list: List<int> := List_Empty;
  list := List_Insert(list, 2);
  list := List_Insert(list, 10);
  list := List_Insert(list, 4);
  list := List_Insert(list, 12);
  list := List_Insert(list, 7);
  var expected := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  assert(expected == list);
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
  var expected := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  assert(expected == c);
}

method SizeZeroTest() {
  var list: List<int> := List_Empty;
  var size := List_Size(list);
  var expected := 0;
  assert(expected == size);
}

method SizeTest() {
  var list: List<int> := Cons(2, Cons(10, Cons(4, Cons(12, Cons(7, List_Empty)))));
  var size := List_Size(list);
  var expected := 5;
  assert(expected == size);
}
