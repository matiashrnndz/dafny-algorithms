include "../../src/Sorted.dfy"
include "../data-types/binary-tree/TreeSet.dfy"

method TreeSort(A:array<int>) returns (sortedSeq:seq<int>)
    requires A.Length > 0
{
    var N := A.Length;
    var searchTree := new TreeSet();

    var i := 0;
    while i < N
        invariant 0 <= i <= N
        decreases N-i
    {
        searchTree.insert(A[i]);
        i := i + 1;
    }

    sortedSeq := searchTree.asSeq();

    return sortedSeq;
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 8, 10, 12, 14, 16, 18, 20;
    var searchTree := new TreeSet();
    searchTree.insert(A[0]);
    searchTree.insert(A[1]);
    searchTree.insert(A[2]);
    searchTree.insert(A[3]);
    searchTree.insert(A[4]);
    searchTree.insert(A[5]);
    searchTree.insert(A[6]);
    searchTree.insert(A[7]);
    searchTree.insert(A[8]);
    searchTree.insert(A[9]);
    var sortedSeq := searchTree.asSeq();
    print sortedSeq;

    var B := new int[10];
    B[0], B[1], B[2], B[3], B[4], B[5], B[6], B[7], B[8], B[9] := 2, 4, 6, 8, 10, 12, 14, 16, 18, 20;
    var sortedSeqB := TreeSort(B);
    print sortedSeqB;
}
