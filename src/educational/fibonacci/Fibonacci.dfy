
// ----------------------------------- Fibonacci_Recursive -------------------------------------- //

function method Fibonacci_Recursive(n: nat): nat
  decreases n
{
  if (n == 0) then 0 else
  if (n == 1) then 1 else
  Fibonacci_Recursive(n-2) + Fibonacci_Recursive(n-1)
}

// --------------------------------- Fibonacci_TailRecursive ------------------------------------ //

/** Nota:
 *
 * La llamada inicial debería ser con a=0 and b=1
 *
 */
function method Fibonacci_TailRecursive(n: nat, a: nat, b: nat): nat
  decreases n
{
  if (n == 0) then a else
  Fibonacci_TailRecursive(n-1, b, a+b)
}

// --------------------------------- Fibonacci_RecursivePair ------------------------------------ //

function method Fibonacci_RecursivePair(n: nat): nat
{
  match Fibonacci_RecursivePairAux(n) {
    case (a, b) => a
  }
}

function method Fibonacci_RecursivePairAux(n: nat): (nat, nat)
  decreases n
{
  if (n == 0) then (0, 1) else
  match Fibonacci_RecursivePairAux(n-1) {
    case (a, b) => (b, a+b)
  }
}

// ----------------------------------- Fibonacci_Iterative -------------------------------------- //

method Fibonacci_Iterative(n: nat) returns (a: nat)
  ensures a == Fibonacci_Recursive(n)
{
  a := 0;
  var b: nat := 1;
  var i: nat := 0;

  while i < n
    invariant 0 <= i <= n
    invariant a == Fibonacci_Recursive(i)
    invariant b == Fibonacci_Recursive(i+1)
    decreases n-i
  {
    a, b := b, a+b;
    i := i+1;
  }
}

// ------------------------------- Fibonacci_TailRecursive Lemmas ------------------------------- //

/** Propiedad:
 *
 * asegurar para todo 'n', que la función Fibonacci_TailRecursive retorna
 * el mismo resultado que la función Fibonacci_Recursive.
 *
 */
lemma {:induction n, i} Lemma_FibonacciTailRecursiveEqualsFibonacciRecursive(n: nat, i: nat)
  requires 0 <= n
  requires 0 <= i <= n
  ensures Fibonacci_TailRecursive(n-i, Fibonacci_Recursive(i), Fibonacci_Recursive(i+1)) == Fibonacci_Recursive(n)
  decreases n-i
{
  if (n-i == 0) {
    calc == {
      Fibonacci_TailRecursive(n-i, Fibonacci_Recursive(i), Fibonacci_Recursive(i+1));
        { assert Fibonacci_TailRecursive(n-i, Fibonacci_Recursive(i), Fibonacci_Recursive(i+1)) 
              == Fibonacci_Recursive(i); }
      Fibonacci_Recursive(n);
    }
  } else {
    calc == {
      Fibonacci_TailRecursive(n-i, Fibonacci_Recursive(i), Fibonacci_Recursive(i+1));
        { assert Fibonacci_TailRecursive(n-i, Fibonacci_Recursive(i), Fibonacci_Recursive(i+1)) 
              == Fibonacci_TailRecursive(n-i-1, Fibonacci_Recursive(i+1), Fibonacci_Recursive(i) + Fibonacci_Recursive(i+1)); }
      Fibonacci_TailRecursive(n-i-1, Fibonacci_Recursive(i+1), Fibonacci_Recursive(i) + Fibonacci_Recursive(i+1));
        { assert Fibonacci_Recursive(i) + Fibonacci_Recursive(i+1) 
              == Fibonacci_Recursive(i+2); }
      Fibonacci_TailRecursive(n-i-1, Fibonacci_Recursive(i+1), Fibonacci_Recursive(i+2));
        { Lemma_FibonacciTailRecursiveEqualsFibonacciRecursive(n, i+1); }
      Fibonacci_Recursive(n);
    }
  }
}

// ------------------------------- Fibonacci_RecursivePair Lemmas ------------------------------- //

/** Propiedad:
 *
 * Asegura para todo 'n', que la función Fibonacci_RecursivePair retorna
 * un resultado equivalente a la función Fibonacci_Recursive.
 *
 */
lemma {:induction n} Lemma_FibonacciRecursivePairEqualsFibonacciRecursive(n: nat)
  ensures Fibonacci_RecursivePair(n) == Fibonacci_Recursive(n)
{
  calc == {
    Fibonacci_RecursivePair(n);
    { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n); }
      { assert Fibonacci_RecursivePairAux(n) 
            == (Fibonacci_Recursive(n), Fibonacci_Recursive(n+1)); }
    Fibonacci_Recursive(n);
  }
}

/** Propiedad:
 *
 * Asegura para todo 'n', que la función Fibonacci_RecursivePairAux retorna como
 * resultado un par ordenado con el primer elemento equivalente a Fibonacci_Recursive
 * de 'n' y el segundo elemento equivalente a Fibonacci_Recursive de 'n+1'.
 *
 */
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
      case (a, b) =>
        calc == {
          (b, a+b);
          { Lemma_FibonacciRecursivePairAuxEqualsFibonacciRecursive(n-1); }
        }
    }
  }
}
