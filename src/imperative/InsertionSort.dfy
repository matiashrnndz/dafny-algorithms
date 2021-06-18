include "../functional/Sorted.dfy"

/** Explicación:

  invariant forall m, n :: 0 <= m < n < i+1 && n != j ==> A[m] <= A[n]
    A está ordenado para cada par de elementos 
    excepto para los que el índice del segundo elemento sea igual a j

 */
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

