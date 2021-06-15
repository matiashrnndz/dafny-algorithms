
// ------------------ Fibonacci :: Recursive ------------------ //

function method FibonacciRecursive(n: nat) : nat
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
  if (n == 1) then b else
  FibonacciTailRecursive(n-1, b, a+b)
}

// ------------------ Fibonacci :: Iterative ------------------ //

method FibonacciIterative(n: nat) returns (y: nat)
  ensures y == FibonacciRecursive(n)
{
  if n == 0 {
    return 0;
  }

  y := 1;
  var x: nat := 1;
  var i: nat := 1;

  while i < n
    invariant 0 < i <= n
    invariant y == FibonacciRecursive(i)
    invariant x == FibonacciRecursive(i+1)
    decreases n-i
  {
    y, x := x, y + x;
    i := i + 1;
  }
}

// ------------- Fibonacci :: Dynamic Programming ------------- //

method FibonacciDynamicProgramming(n: nat) returns (fib: nat)
{
  var f := new nat[n+2];
  f[0] := 0;
  f[1] := 1;

  var i := 2;
  while i <= n
    decreases n-i
  {
    f[i] := f[i-1] + f[i-2];
    i := i + 1;
  }

  fib := f[n];
}
