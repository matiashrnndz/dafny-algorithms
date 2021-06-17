
// ------------------ Fibonacci :: Recursive ------------------ //

function method FibonacciRecursive(n: nat): nat
  decreases n
{
  if (n == 0) then 0 else
  if (n == 1) then 1 else
  FibonacciRecursive(n-2) + FibonacciRecursive(n-1)
}

// ---------------- Fibonacci :: Tail Recursive ---------------- //

function method FibonacciTailRecursive(n: nat, a: nat, b: nat): nat
  // Initial call should be with a=0 and b=1
  decreases n
{
  if (n == 0) then a else
  FibonacciTailRecursive(n-1, b, a+b)
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

method FibonacciIterative(n: nat) returns (y: nat)
  ensures y == FibonacciRecursive(n)
{
  y := 0;
  var x: nat := 1;
  var i: nat := 0;

  while i < n
    invariant 0 <= i <= n
    invariant y == FibonacciRecursive(i)
    invariant x == FibonacciRecursive(i+1)
    decreases n-i
  {
    y, x := x, y + x;
    i := i + 1;
  }
}
