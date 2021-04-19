predicate sorted(S:seq<int>) {
    forall i, j :: 0 <= i <= j < |S| ==> S[i] <= S[j]
}

method BinarySearch(A:array<int>, key:int) returns (index:int)
    requires sorted(A[..])
    ensures 0 <= index ==> index < A.Length && A[index] == key
    ensures index < 0 ==> key !in A[..]
{
    var low :=0;
    var high := A.Length;
    while low < high
        invariant 0 <= low <= high <= A.Length
        invariant key !in A[..low]
        invariant key !in A[high..]
    {
        var mid := (low + high) / 2;
        if key < A[mid] {
            high := mid;
        } else if key > A[mid] {
            low := mid + 1;
        } else {
            return mid;
        }
    }
    return -1;
}

method Main() {
    var a := new int[10];
    a[0], a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9] := 2, 4, 6, 8, 10, 12, 14, 16, 18, 20;
    var index := BinarySearch(a, 12);
    print index;
}