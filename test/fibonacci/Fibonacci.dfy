include "../../src/fibonacci/Fibonacci.dfy"

method Main() {
  FibonacciRecursiveTest();
  FibonacciTailRecursiveCallTest();
  FibonacciRecursivePairTest();
  FibonacciIterativeTest();
}

method FibonacciRecursiveTest() {
  assert FibonacciRecursive(0) == 0;
  assert FibonacciRecursive(1) == 1;
  assert FibonacciRecursive(2) == 1;
  assert FibonacciRecursive(3) == 2;
  assert FibonacciRecursive(4) == 3;
  assert FibonacciRecursive(5) == 5;
  assert FibonacciRecursive(6) == 8;
  assert FibonacciRecursive(7) == 13;
  assert FibonacciRecursive(8) == 21;
}

method FibonacciTailRecursiveCallTest() {
  assert FibonacciTailRecursive(0, 0, 1) == 0;
  assert FibonacciTailRecursive(1, 0, 1) == 1;
  assert FibonacciTailRecursive(2, 0, 1) == 1;
  assert FibonacciTailRecursive(3, 0, 1) == 2;
  assert FibonacciTailRecursive(4, 0, 1) == 3;
  assert FibonacciTailRecursive(5, 0, 1) == 5;
  assert FibonacciTailRecursive(6, 0, 1) == 8;
  assert FibonacciTailRecursive(7, 0, 1) == 13;
  assert FibonacciTailRecursive(8, 0, 1) == 21;
}

method FibonacciRecursivePairTest() {
  assert FibonacciRecursivePair(0) == 0;
  assert FibonacciRecursivePair(1) == 1;
  assert FibonacciRecursivePair(2) == 1;
  assert FibonacciRecursivePair(3) == 2;
  assert FibonacciRecursivePair(4) == 3;
  assert FibonacciRecursivePair(5) == 5;
  assert FibonacciRecursivePair(6) == 8;
  assert FibonacciRecursivePair(7) == 13;
  assert FibonacciRecursivePair(8) == 21;
}

method FibonacciIterativeTest() {
  var fib0 := FibonacciIterative(0);
  assert fib0 == 0;
  var fib1 := FibonacciIterative(1);
  assert fib1 == 1;
  var fib2 := FibonacciIterative(2);
  assert fib2 == 1;
  var fib3 := FibonacciIterative(3);
  assert fib3 == 2;
  var fib4 := FibonacciIterative(4);
  assert fib4 == 3;
  var fib5 := FibonacciIterative(5);
  assert fib5 == 5;
  var fib6 := FibonacciIterative(6);
  assert fib6 == 8;
  var fib7 := FibonacciIterative(7);
  assert fib7 == 13;
  var fib8 := FibonacciIterative(8);
  assert fib8 == 21;
}
