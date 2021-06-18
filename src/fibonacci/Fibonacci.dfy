
// ------------------ Fibonacci :: Recursive ------------------ //

function method FibonacciRecursive(n: nat): nat
  decreases n
{
  if (n == 0) then 0 else
  if (n == 1) then 1 else
  FibonacciRecursive(n-2) + FibonacciRecursive(n-1)
}

// ---------------- Fibonacci :: Tail Recursive ---------------- //

function method FibonacciTailRecursive(n: nat, f: nat, f': nat): nat
  // Initial call should be with f=0 and f'=1
  decreases n
{
  if (n == 0) then f else
  FibonacciTailRecursive(n-1, f', f+f')
}

// --------------- Fibonacci :: Recursive Pair --------------- //

function method FibonacciRecursivePair(n: nat): nat
  // Lemma_FibonacciRecursivePairEqualsFibonacciRecursive(n) ==> ensures FibonacciRecursivePair(n) == FibonacciRecursive(n)
{
  match FibonacciRecursivePairAux(n) {
    case (f, f') => f
  }
}

function method FibonacciRecursivePairAux(n: nat): (nat, nat)
  // Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n) ==> ensures FibonacciRecursivePairAux(n) == (FibonacciRecursive(n), FibonacciRecursive(n+1))
  decreases n
{
  if (n == 0) then (0, 1) else
  match FibonacciRecursivePairAux(n-1) {
    case (f, f') => (f', f+f')
  }
}

// ------------------ Fibonacci :: Iterative ------------------ //

method FibonacciIterative(n: nat) returns (f: nat)
  ensures f == FibonacciRecursive(n)
{
  f := 0;
  var f': nat := 1;
  var i: nat := 0;

  while i < n
    invariant 0 <= i <= n
    invariant f == FibonacciRecursive(i)
    invariant f' == FibonacciRecursive(i+1)
    decreases n-i
  {
    f, f' := f', f+f';
    i := i+1;
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction n} Lemma_FibonacciRecursivePairEqualsFibonacciRecursive(n: nat)
  ensures FibonacciRecursivePair(n) == FibonacciRecursive(n)
{
  calc == {
    FibonacciRecursivePair(n);
    { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n); }
      { assert FibonacciRecursivePairAux(n) == (FibonacciRecursive(n), FibonacciRecursive(n+1)); }
    FibonacciRecursive(n);
  }
}

lemma {:induction n} Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n: nat)
  ensures FibonacciRecursivePairAux(n) == (FibonacciRecursive(n), FibonacciRecursive(n+1))
  decreases n
{
  if (n == 0) {
    calc == {
      FibonacciRecursivePairAux(n);
        { assert n == 0; }
      FibonacciRecursivePairAux(0);
        { assert FibonacciRecursivePairAux(0) == (0, 1); }
      (0, 1);
        { assert FibonacciRecursive(0) == 0; }
        { assert FibonacciRecursive(0+1) == 1; }
        { assert (0, 1) == (FibonacciRecursive(0), FibonacciRecursive(0+1)); }
      (FibonacciRecursive(0), FibonacciRecursive(0+1));
    }
  } else {
    calc == {
      FibonacciRecursivePairAux(n);
        { assert n > 0; }
    }
    match FibonacciRecursivePairAux(n-1) {
      case (f, f') =>
        calc == {
          (f', f+f');
          { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n-1); }
        }
    }
  }
}
