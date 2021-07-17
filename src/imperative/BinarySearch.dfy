include "./sorted.dfy"

// ----------------------------------------- Methods -------------------------------------------- //

method BinarySearch(A:array<int>, key:int) returns (index:int)
  requires sorted(A)
  ensures 0 <= index ==> index < A.Length && A[index] == key
  ensures index < 0 ==> key !in A[..]
{
  var N := A.Length;
  var low := 0;
  var high := N;
  while low < high
    invariant 0 <= low <= high <= N
    invariant key !in A[..low]
    invariant key !in A[high..]
    decreases high - low
  {
    var mid := (low + high) / 2;
    if key < A[mid] {
        high := mid;
    } else if key > A[mid] {
        low := mid + 1;
    } else {
        return mid;
    }
  }
  return -1;
}
