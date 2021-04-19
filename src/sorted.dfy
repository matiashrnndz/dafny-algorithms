
predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: from <= i <= j <= to && 0 <= i <= j < A.Length ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}
