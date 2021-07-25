type T = int

// --------------------------------------- Datatypes -------------------------------------------- //

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

// --------------------------------------- Predicates ------------------------------------------- //

/** Predicado:
 *
 * Retorna verdadero cuando la lista está ordenada de manera creciente.
 *
 */
predicate list_increasing(list:List<T>)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, Nil) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_increasing(Cons(ht, tail))
  }
}

/** Predicado:
 *
 * Retorna verdadero cuando el elemento “d”, es cota superior
 * a todos los elementos de una lista.
 *
 */
predicate list_upper_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d >= head) && list_upper_bound(tail, d)
  }
}

/** Predicado:
 *
 * Retorna verdadero cuando el elemento “d”, es cota inferior
 * a todos los elementos de una lista.
 *
 */
predicate list_lower_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d <= head) && list_lower_bound(tail, d)
  }
}

// ------------------------------------ Function Methods ---------------------------------------- //

/** Funcionalidad:
 *
 * Convertierte los elementos de una lista en un multiset de sus elementos.
 *
 */
function method List_ToMultiset(list:List<T>) : (m:multiset<T>)
  decreases list
{
  match list {
    case Nil => multiset{}
    case Cons(head, tail) => multiset{head} + List_ToMultiset(tail)
  }
}

/** Funcionalidad:
 *
 * Recibe como parámetros dos listas y como resultado concatena al
 * final de la primera lista, toda la segunda lista.
 *
 */
function method List_Concat(a:List<T>, b:List<T>) : List<T>
  decreases a
{
  match a {
    case Nil => b
    case Cons(head, tail) => Cons(head, List_Concat(tail, b))
  }
}

// ------------------------------------ List_Concat Lemmas -------------------------------------- //

/** Propiedad:
 *
 * Asegura que la unión de los elementos de ambas listas que recibe como parámetro
 * List_Concat, sean los mismos que los elementos de las listas concatenadas.
 *
 */
lemma {:induction a} Lemma_ListConcatIntegrity(a:List<T>, b:List<T>)
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  decreases a, b
{ }

/** Propiedad:
 *
 * Dadas dos listas ordenadas y un elemento que sea cota superior de la primera
 * y cota inferior de la segunda, asegura que la concatenación de las dos listas
 * y el elemento en el medio, también esté ordenado.
 *
 */
lemma {:induction a, b} Lemma_ListConcatWithMidElemOrdering(a:List<T>, x:T, b:List<T>)
  requires list_increasing(a)
  requires list_increasing(b)
  requires list_lower_bound(b, x)
  requires list_upper_bound(a, x)
  ensures list_increasing(List_Concat(a, Cons(x, b)))
  decreases a, b
{ }

/** Propiedad:
 *
 * Asegura que si un elemento es cota superior de dos listas,
 * también es cota superior de la concatenación de ambas listas.
 *
 */
lemma {:induction listLeft} Lemma_ListConcatUpperBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_upper_bound(listLeft, d)
  requires list_upper_bound(listRight, d)
  requires d >= x
  ensures list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{ }

/** Propiedad:
 *
 * Asegura que si un elemento es cota inferior de dos listas,
 * también es cota inferior de la concatenación de ambas listas.
 *
 */
lemma {:induction listLeft} Lemma_ListConcatLowerBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_lower_bound(listLeft, d)
  requires list_lower_bound(listRight, d)
  requires d <= x
  ensures list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{ }
