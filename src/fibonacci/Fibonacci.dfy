
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
{
  match FibonacciRecursivePairAux(n) {
    case (f, f') => f
  }
}

function method FibonacciRecursivePairAux(n: nat): (nat, nat)
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
