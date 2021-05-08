include "../../src/Sorted.dfy"

method BubbleSort(A:array<int>)
  modifies A
  ensures sorted(A)
  ensures multiset(A[..]) == multiset(old(A[..]))
{
  var N := A.Length;
  var i := N-1;
  while 0 < i
    invariant multiset(A[..]) == multiset(old(A[..]))
    invariant sorted_between(A, i, N-1)
    invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
    decreases i
  {
    print A[..], "\n";
    var j := 0;
    while j < i
      invariant 0 < i < N
      invariant 0 <= j <= i
      invariant multiset(A[..]) == multiset(old(A[..]))
      invariant sorted_between(A, i, N-1)
      invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
      invariant forall n :: 0 <= n <= j ==> A[n] <= A[j]
      decreases i - j
    {
      if A[j] > A[j+1]
      {
          A[j], A[j+1] := A[j+1], A[j];
          print A[..], "\n";
      }
      j := j+1;
    } 
    i := i-1;
    print "\n";
  }
}

/* Explicación:

invariant forall n, m :: 0 <= n <= i < m < N ==> A[n] <= A[m]
    // A está ordenado para cada par de elementos tal que
    // el primer elemento pertenezca a la partición izquierda de i
    // y el segundo elemento pertenezca a la partición derecha de i

invariant forall n :: 0 <= n <= j ==> A[n] <= A[j]
    // Existe un supremo definido por el valor que toma el array en la posición j
    // Por lo tanto, cada valor que toma el array para todos los elementos desde 0 hasta j
    // Son menores o iguales al valor del supremo

*/