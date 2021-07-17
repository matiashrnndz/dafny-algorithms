
/** Explicación:
 *
 *  invariant forall k :: 0 <= k < i ==> A[k] != key
 *    Ningún elemento tal que su índice sea menor al actual puede ser el elemento buscado
 *
 */
method LinealSearch(A:array<int>, key:int) returns (index:int)
  ensures 0 <= index ==> index < A.Length && A[index] == key
  ensures index < 0 ==> key !in A[..]
{
  var N := A.Length;
  var i := 0;
  while i < N
    invariant 0 <= i <= N
    invariant forall k :: 0 <= k < i ==> A[k] != key
    decreases N - i
  {
    if A[i] == key
    {
      return i;
    }
    i := i + 1;
  }
  return -1;
}
