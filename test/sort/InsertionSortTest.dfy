include "../../src/sort/InsertionSort.dfy"

method Main() {
  InsertionSortTest();
}

method InsertionSortTest() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  InsertionSort(A);
  print A[..];
}
