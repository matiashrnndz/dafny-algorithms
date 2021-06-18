
// ------------------ Fibonacci :: Recursive ------------------ //

function method Fibonacci_Recursive(n: nat): nat
  decreases n
{
  if (n == 0) then 0 else
  if (n == 1) then 1 else
  Fibonacci_Recursive(n-2) + Fibonacci_Recursive(n-1)
}

// ---------------- Fibonacci :: Tail Recursive ---------------- //


/** Requirements:

  Initial call should be with f=0 and f'=1

 */
function method Fibonacci_TailRecursive(n: nat, f: nat, f': nat): nat
  decreases n
{
  if (n == 0) then f else
  Fibonacci_TailRecursive(n-1, f', f+f')
}

// --------------- Fibonacci :: Recursive Pair --------------- //

/** Properties:

  Lemma_FibonacciRecursivePairEqualsFibonacciRecursive(n) 
    ==> ensures Fibonacci_RecursivePair(n) == Fibonacci_Recursive(n)

 */
function method Fibonacci_RecursivePair(n: nat): nat
{
  match Fibonacci_RecursivePairAux(n) {
    case (f, f') => f
  }
}

/** Properties:

  Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n) 
    ==> ensures Fibonacci_RecursivePairAux(n) == (Fibonacci_Recursive(n), Fibonacci_Recursive(n+1))

 */
function method Fibonacci_RecursivePairAux(n: nat): (nat, nat)
  decreases n
{
  if (n == 0) then (0, 1) else
  match Fibonacci_RecursivePairAux(n-1) {
    case (f, f') => (f', f+f')
  }
}

// ------------------ Fibonacci :: Iterative ------------------ //

method Fibonacci_Iterative(n: nat) returns (f: nat)
  ensures f == Fibonacci_Recursive(n)
{
  f := 0;
  var f': nat := 1;
  var i: nat := 0;

  while i < n
    invariant 0 <= i <= n
    invariant f == Fibonacci_Recursive(i)
    invariant f' == Fibonacci_Recursive(i+1)
    decreases n-i
  {
    f, f' := f', f+f';
    i := i+1;
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction n} Lemma_FibonacciRecursivePairEqualsFibonacciRecursive(n: nat)
  ensures Fibonacci_RecursivePair(n) == Fibonacci_Recursive(n)
{
  calc == {
    Fibonacci_RecursivePair(n);
    { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n); }
      { assert Fibonacci_RecursivePairAux(n) == (Fibonacci_Recursive(n), Fibonacci_Recursive(n+1)); }
    Fibonacci_Recursive(n);
  }
}

lemma {:induction n} Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n: nat)
  ensures Fibonacci_RecursivePairAux(n) == (Fibonacci_Recursive(n), Fibonacci_Recursive(n+1))
  decreases n
{
  if (n == 0) {
    calc == {
      Fibonacci_RecursivePairAux(n);
        { assert n == 0; }
      Fibonacci_RecursivePairAux(0);
        { assert Fibonacci_RecursivePairAux(0) == (0, 1); }
      (0, 1);
        { assert Fibonacci_Recursive(0) == 0; }
        { assert Fibonacci_Recursive(0+1) == 1; }
        { assert (0, 1) == (Fibonacci_Recursive(0), Fibonacci_Recursive(0+1)); }
      (Fibonacci_Recursive(0), Fibonacci_Recursive(0+1));
    }
  } else {
    calc == {
      Fibonacci_RecursivePairAux(n);
        { assert n > 0; }
    }
    match Fibonacci_RecursivePairAux(n-1) {
      case (f, f') =>
        calc == {
          (f', f+f');
          { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n-1); }
        }
    }
  }
}
