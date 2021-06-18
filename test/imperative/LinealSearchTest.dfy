include "../../src/imperative/LinealSearch.dfy"

method Main() {
  Test_LinealSearch();
}

method Test_LinealSearch() {
  var a := new int[10];
  a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 2, 4, 6, 8, 10, 12, 14, 16, 18, 20;
  var index := LinealSearch(a, 12);
  print index;
}
