include "../../src/fibonacci/Fibonacci.dfy"

method Main() {
  Fibonacci_RecursiveTest();
  Fibonacci_TailRecursiveTest();
  Fibonacci_RecursivePairTest();
  Fibonacci_IterativeTest();
}

method Fibonacci_RecursiveTest() {
  assert Fibonacci_Recursive(0) == 0;
  assert Fibonacci_Recursive(1) == 1;
  assert Fibonacci_Recursive(2) == 1;
  assert Fibonacci_Recursive(3) == 2;
  assert Fibonacci_Recursive(4) == 3;
  assert Fibonacci_Recursive(5) == 5;
  assert Fibonacci_Recursive(6) == 8;
  assert Fibonacci_Recursive(7) == 13;
  assert Fibonacci_Recursive(8) == 21;
  assert Fibonacci_Recursive(9) == 34;
  assert Fibonacci_Recursive(10) == 55;
  assert Fibonacci_Recursive(11) == 89;
  assert Fibonacci_Recursive(12) == 144;
}

method Fibonacci_TailRecursiveTest() {
  assert Fibonacci_TailRecursive(0, 0, 1) == 0;
  assert Fibonacci_TailRecursive(1, 0, 1) == 1;
  assert Fibonacci_TailRecursive(2, 0, 1) == 1;
  assert Fibonacci_TailRecursive(3, 0, 1) == 2;
  assert Fibonacci_TailRecursive(4, 0, 1) == 3;
  assert Fibonacci_TailRecursive(5, 0, 1) == 5;
  assert Fibonacci_TailRecursive(6, 0, 1) == 8;
  assert Fibonacci_TailRecursive(7, 0, 1) == 13;
  assert Fibonacci_TailRecursive(8, 0, 1) == 21;
  assert Fibonacci_TailRecursive(9, 0, 1) == 34;
  assert Fibonacci_TailRecursive(10, 0, 1) == 55;
  assert Fibonacci_TailRecursive(11, 0, 1) == 89;
  assert Fibonacci_TailRecursive(12, 0 ,1) == 144;
}

method Fibonacci_RecursivePairTest() {
  assert Fibonacci_RecursivePair(0) == 0;
  assert Fibonacci_RecursivePair(1) == 1;
  assert Fibonacci_RecursivePair(2) == 1;
  assert Fibonacci_RecursivePair(3) == 2;
  assert Fibonacci_RecursivePair(4) == 3;
  assert Fibonacci_RecursivePair(5) == 5;
  assert Fibonacci_RecursivePair(6) == 8;
  assert Fibonacci_RecursivePair(7) == 13;
  assert Fibonacci_RecursivePair(8) == 21;
  assert Fibonacci_RecursivePair(9) == 34;
  assert Fibonacci_RecursivePair(10) == 55;
  assert Fibonacci_RecursivePair(11) == 89;
  assert Fibonacci_RecursivePair(12) == 144;
}

method Fibonacci_IterativeTest() {
  var fib := Fibonacci_Iterative(0);
  assert fib == 0;
  fib := Fibonacci_Iterative(1);
  assert fib == 1;
  fib := Fibonacci_Iterative(2);
  assert fib == 1;
  fib := Fibonacci_Iterative(3);
  assert fib == 2;
  fib := Fibonacci_Iterative(4);
  assert fib == 3;
  fib := Fibonacci_Iterative(5);
  assert fib == 5;
  fib := Fibonacci_Iterative(6);
  assert fib == 8;
  fib := Fibonacci_Iterative(7);
  assert fib == 13;
  fib := Fibonacci_Iterative(8);
  assert fib == 21;
  fib := Fibonacci_Iterative(9);
  assert fib == 34;
  fib := Fibonacci_Iterative(10);
  assert fib == 55;
  fib := Fibonacci_Iterative(11);
  assert fib == 89;
  fib := Fibonacci_Iterative(12);
  assert fib == 144;
}
