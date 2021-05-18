
predicate sorted_between(A:array<int>, from:int, to:int)
    reads A
{
    forall i, j :: 0 <= i <= j < A.Length && from <= i <= j <= to ==> A[i] <= A[j]
}

predicate sorted(A:array<int>)
    reads A
{
    sorted_between(A, 0, A.Length-1)
}

predicate sorted_seq(s:seq<int>)
{
   forall i, j :: 0 <= i <= j < |s| ==> s[i] <= s[j]
}
