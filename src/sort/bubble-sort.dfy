include "../../src/sorted.dfy"

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
        invariant forall k, k' :: 0 <= k <= i < k' < N ==> A[k] <= A[k']
        decreases i
    {
        print A[..], "\n";
        var j := 0;
        while j < i
            invariant 0 < i < N
            invariant 0 <= j <= i
            invariant multiset(A[..]) == multiset(old(A[..]))
            invariant sorted_between(A, i, N-1)
            invariant forall k, k' :: 0 <= k <= i < k' < N ==> A[k] <= A[k']
            invariant forall k :: 0 <= k <= j ==> A[k] <= A[j]
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

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    BubbleSort(A);
    print A[..];
}