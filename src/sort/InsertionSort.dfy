include "../../src/Sorted.dfy"

method InsertionSort(A:array<int>)
  modifies A
  requires A.Length >= 1
  ensures multiset(A[..]) == multiset(old(A[..]))
  ensures sorted(A)
{
  var N := A.Length;
  var i := 1;
  while i < N
    invariant 1 <= i <= N
    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant sorted_between(A, 0, i-1)
    decreases N-i
  {
    print A[..], "\n";
    var j := i;
    while j > 0 && A[j-1] > A[j] 
      invariant 1 <= i <= N-1
      invariant 0 <= j <= i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant forall m, n :: 0 <= m < n < i+1 && n != j ==> A[m] <= A[n]
      decreases j
    {
      A[j], A[j-1] := A[j-1], A[j];
      j := j-1;
      print A[..], "\n";
    }
    i := i+1;
    print "\n";
  }
}

method Main() {
  var A := new int[10];
  A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
  InsertionSort(A);
  print A[..];
}

/* Explicación:

invariant forall m, n :: 0 <= m < n < i+1 && n != j ==> A[m] <= A[n]
    // A está ordenado para cada par de elementos 
    // excepto para los que el índice del segundo elemento sea igual a j

*/