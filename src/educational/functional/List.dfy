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
{
  match a {
    case Nil =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert a == List.Nil; }
        List_ToMultiset(List_Concat(List.Nil, b));
          { assert List_ToMultiset(List_Concat(List.Nil, b)) 
                == List_ToMultiset(List.Nil) + List_ToMultiset(b); }
        List_ToMultiset(List.Nil) + List_ToMultiset(b);
          { assert List_ToMultiset(List.Nil) == multiset{}; }
        multiset{} + List_ToMultiset(b);
          { assert multiset{} == List_ToMultiset(List.Nil); }
        List_ToMultiset(List.Nil) + List_ToMultiset(b);
          { assert List_ToMultiset(List.Nil) == List_ToMultiset(a); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert a == Cons(ha, ta); }
        List_ToMultiset(List_Concat(Cons(ha, ta), b));
          { assert List_ToMultiset(List_Concat(Cons(ha, ta), b))
                == List_ToMultiset(Cons(ha, ta)) + List_ToMultiset(b); }
        List_ToMultiset(Cons(ha, ta)) + List_ToMultiset(b);
          { Lemma_ListConcatIntegrity(ta, b); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
  }
}

/** Propiedad:
 *
 * Asegura que al aplicarse la concatenación de dos listas vacías,
 * el resultado sea una lista vacía.
 *
 */
lemma {:induction a, b} Lemma_ListConcatBothListEmpty(a:List<T>, b:List<T>)
  requires a == List.Nil
  requires b == List.Nil
  ensures List_Concat(a, b) == List.Nil
{
  calc == {
    List_Concat(a, b);
      { assert a == List.Nil; }
    List_Concat(List.Nil, b);
      { assert List_Concat(List.Nil, b) == b; }
    b;
      { assert b == List.Nil; }
    List.Nil;
  }
}

/** Propiedad:
 *
 * Asegura que al aplicarse la concatenación de listas con la primera
 * lista vacía, el resultado sea la segunda lista.
 *
 */
lemma {:induction a} Lemma_ListConcatFirstListEmpty(a:List<T>, b:List<T>)
  requires a == List.Nil
  ensures List_Concat(a, b) == b
{
  calc == {
    List_Concat(a, b);
      { assert a == List.Nil; }
    List_Concat(List.Nil, b);
      { assert List_Concat(List.Nil, b) == b; }
    b;
  }
}

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
{
  match a {
    case Nil =>
      calc == {
        list_increasing(List_Concat(a, Cons(x, b)));
          { assert a == List.Nil; }
        list_increasing(List_Concat(List.Nil, Cons(x, b)));
          { Lemma_ListConcatFirstListEmpty(List.Nil, b); }
        list_increasing(Cons(x, b));
          { assert list_lower_bound(b, x); }
          { assert list_increasing(b); }
        true;
      }
    case Cons(ha, ta) =>
      match ta {
        case Nil =>
          calc == {
            list_increasing(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_increasing(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b)) 
                    == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_increasing(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == List.Nil; }
            list_increasing(Cons(ha, List_Concat(List.Nil, Cons(x, b))));
              { Lemma_ListConcatFirstListEmpty(List.Nil, b); }
            list_increasing(Cons(ha, Cons(x, b)));
              { assert ha <= x; }
              { assert list_lower_bound(b, x); }
              { assert list_increasing(b); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_increasing(List_Concat(a, Cons(x, b)));
              { assert a == Cons(ha, ta); }
            list_increasing(List_Concat(Cons(ha, ta), Cons(x, b)));
              { assert List_Concat(Cons(ha, ta), Cons(x, b))
                    == Cons(ha, List_Concat(ta, Cons(x, b))); }
            list_increasing(Cons(ha, List_Concat(ta, Cons(x, b))));
              { assert ta == Cons(tah, tat); }
            list_increasing(Cons(ha, List_Concat(Cons(tah, tat), Cons(x, b))));
              { assert (ha <= tah && list_increasing(List_Concat(Cons(tah, tat), Cons(x, b)))); }
            ha <= tah && list_increasing(List_Concat(Cons(tah, tat), Cons(x, b)));
              { Lemma_ListConcatWithMidElemOrdering(Cons(tah, tat), x, Cons(x, b)); }
            true;
          }
      }
  }
}

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
{
  match listLeft {
    case Nil =>
      calc == {
        list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List.Nil; }
        list_upper_bound(List_Concat(List.Nil, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
        list_upper_bound(Cons(x, listRight), d);
          { assert list_upper_bound(listRight, d); }
          { assert d >= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case Nil =>
          calc == {
            list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List.Nil); }
            list_upper_bound(List_Concat(Cons(lh, List.Nil), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List.Nil), Cons(x, listRight))
                    == Cons(lh, List_Concat(List.Nil, Cons(x, listRight))); }
            list_upper_bound(Cons(lh, List_Concat(List.Nil, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
            list_upper_bound(Cons(lh, Cons(x, listRight)), d);
              { assert d >= x; }
              { assert list_upper_bound(listRight, d); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, lt); }
            list_upper_bound(List_Concat(Cons(lh, lt), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight))
                    == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
            list_upper_bound(Cons(lh, List_Concat(lt, Cons(x, listRight))), d);
              { assert lt == Cons(tah, tat); }
            list_upper_bound(Cons(lh, List_Concat(Cons(tah, tat), Cons(x, listRight))), d);
              { assert (d >= lh && list_upper_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d)); }
            d >= x && list_upper_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d);
              { Lemma_ListConcatUpperBound(Cons(tah, tat), Cons(x, listRight), d, x); }
            true;
          }
      }
  }
}

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
{
  match listLeft {
    case Nil =>
      calc == {
        list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
          { assert listLeft == List.Nil; }
        list_lower_bound(List_Concat(List.Nil, Cons(x, listRight)), d);
          { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
        list_lower_bound(Cons(x, listRight), d);
          { assert list_lower_bound(listRight, d); }
          { assert d <= x; }
        true;
      }
    case Cons(lh, lt) =>
      match lt {
        case Nil =>
          calc == {
            list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, List.Nil); }
            list_lower_bound(List_Concat(Cons(lh, List.Nil), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, List.Nil), Cons(x, listRight))
                    == Cons(lh, List_Concat(List.Nil, Cons(x, listRight))); }
            list_lower_bound(Cons(lh, List_Concat(List.Nil, Cons(x, listRight))), d);
              { Lemma_ListConcatFirstListEmpty(List.Nil, Cons(x, listRight)); }
            list_lower_bound(Cons(lh, Cons(x, listRight)), d);
              { assert d <= x; }
              { assert list_lower_bound(listRight, d); }
            true;
          }
        case Cons(tah, tat) =>
          calc ==> {
            list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d);
              { assert listLeft == Cons(lh, lt); }
            list_lower_bound(List_Concat(Cons(lh, lt), Cons(x, listRight)), d);
              { assert List_Concat(Cons(lh, lt), Cons(x, listRight))
                    == Cons(lh, List_Concat(lt, Cons(x, listRight))); }
            list_lower_bound(Cons(lh, List_Concat(lt, Cons(x, listRight))), d);
              { assert lt == Cons(tah, tat); }
            list_lower_bound(Cons(lh, List_Concat(Cons(tah, tat), Cons(x, listRight))), d);
              { assert (d <= lh && list_lower_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d)); }
            d <= lh && list_lower_bound(List_Concat(Cons(tah, tat), Cons(x, listRight)), d);
              { Lemma_ListConcatLowerBound(Cons(tah, tat), Cons(x, listRight), d, x); }
            true;
          }
      }
  }
}
