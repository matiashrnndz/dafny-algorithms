
predicate sorted(S:seq<int>) {
    forall i, j :: 0 <= i <= j < |S| ==> S[i] <= S[j]
}

lemma sortedVoid(S:seq<int>) 
    requires |S| == 0
    ensures sorted(S) == true
{ 
    assert(sorted(S) == true);
}

method InsertionSort(A:array<int>)
	modifies A
	ensures sorted(A[..])
{
	var i := 0;
	while i < A.Length
		invariant 0 <= i <= A.Length
		invariant sorted(A[..i])
        decreases A.Length - i
	{
        var n := A[i];
        var j := i - 1;
        while j >= 0 && A[j] > n
            invariant sorted(A[j+2..i+1])
            invariant sorted(A[..j+1])
            invariant forall k, m :: 0 <= k < j+1 && j+2 <= m < i+1 ==> A[k] <= A[m]
            invariant forall k :: j+2 <= k < i+1 ==> n <= A[k]
            decreases j
        {
            A[j+1] := A[j];
            j := j - 1;
        }
        A[j+1] := n;
        i := i + 1;
	}
}

method Main() {
    var A := new int[10];
    A[0], A[1], A[2], A[3], A[4], A[5], A[6], A[7], A[8], A[9] := 2, 4, 6, 15, 3, 19, 17, 16, 18, 1;
    InsertionSort(A);
    print A[..];
}
