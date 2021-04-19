include "../src/sorted.dfy"

method InsertionSort(A:array<int>)
	modifies A
	ensures sorted(A)
{
    var N := A.Length;
	var i := 0;
	while i < N
		invariant 0 <= i <= N
		invariant sorted_between(A, 0, i-1)
        decreases N - i
	{
        var x := A[i];
        var j := i - 1;
        while j >= 0 && A[j] > x
            invariant sorted_between(A, 0, j)
            invariant sorted_between(A, j+2, i)
            invariant forall k :: j+2 <= k <= i ==> x <= A[k]
            invariant forall k, k' :: 0 <= k <= j && j+2 <= k' <= i ==> A[k] <= A[k']
            decreases j
        {
            A[j+1] := A[j];
            j := j - 1;
        }
        A[j+1] := x;
        i := i + 1;
	}
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    InsertionSort(A);
    print A[..];
}