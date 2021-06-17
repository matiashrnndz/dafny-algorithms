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
  assert FibonacciRecursive(9) == 34;
  assert FibonacciRecursive(10) == 55;
  assert FibonacciRecursive(11) == 89;
  assert FibonacciRecursive(12) == 144;
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
  assert FibonacciTailRecursive(9, 0, 1) == 34;
  assert FibonacciTailRecursive(10, 0, 1) == 55;
  assert FibonacciTailRecursive(11, 0, 1) == 89;
  assert FibonacciTailRecursive(12, 0 ,1) == 144;
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
  assert FibonacciRecursivePair(9) == 34;
  assert FibonacciRecursivePair(10) == 55;
  assert FibonacciRecursivePair(11) == 89;
  assert FibonacciRecursivePair(12) == 144;
}

method FibonacciIterativeTest() {
  var fib := FibonacciIterative(0);
  assert fib == 0;
  fib := FibonacciIterative(1);
  assert fib == 1;
  fib := FibonacciIterative(2);
  assert fib == 1;
  fib := FibonacciIterative(3);
  assert fib == 2;
  fib := FibonacciIterative(4);
  assert fib == 3;
  fib := FibonacciIterative(5);
  assert fib == 5;
  fib := FibonacciIterative(6);
  assert fib == 8;
  fib := FibonacciIterative(7);
  assert fib == 13;
  fib := FibonacciIterative(8);
  assert fib == 21;
  fib := FibonacciIterative(9);
  assert fib == 34;
  fib := FibonacciIterative(10);
  assert fib == 55;
  fib := FibonacciIterative(11);
  assert fib == 89;
  fib := FibonacciIterative(12);
  assert fib == 144;
}
