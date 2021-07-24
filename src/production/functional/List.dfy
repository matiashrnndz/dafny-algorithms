type T = int

// --------------------------------------- Datatypes -------------------------------------------- //

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

// --------------------------------------- Predicates ------------------------------------------- //

predicate list_increasing(list:List<T>)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, Nil) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_increasing(Cons(ht, tail))
  }
}

predicate list_lower_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d <= head) && list_lower_bound(tail, d)
  }
}

predicate list_upper_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case Nil => true
    case Cons(head, tail) => (d >= head) && list_upper_bound(tail, d)
  }
}

// ------------------------------------ Function Methods ---------------------------------------- //

function method List_ToMultiset(list:List<T>) : (m:multiset<T>)
  decreases list
{
  match list {
    case Nil => multiset{}
    case Cons(head, tail) => multiset{head} + List_ToMultiset(tail)
  }
}

/** Properties:
 *
 *  Lemma_ListConcatIntegrity(a, b)
 *    ==> ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
 *
 *  Lemma_ListConcatWithMidElemOrdering(a, x, b)
 *    ==> ensures list_increasing(List_Concat(a, Cons(x, b)))
 *
 *  Lemma_ListConcatUpperBound(a, b, d, x)
 *    ==> ensures list_upper_bound(List_Concat(a, Cons(x, b)), d)
 *
 *  Lemma_ListConcatLowerBound(a, b, d, x)
 *    ==> ensures list_lower_bound(List_Concat(a, Cons(x, b)), d)
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

lemma {:induction a} Lemma_ListConcatIntegrity(a:List<T>, b:List<T>)
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  decreases a, b
{ }

lemma {:induction a, b} Lemma_ListConcatWithMidElemOrdering(a:List<T>, x:T, b:List<T>)
  requires list_increasing(a)
  requires list_increasing(b)
  requires list_lower_bound(b, x)
  requires list_upper_bound(a, x)
  ensures list_increasing(List_Concat(a, Cons(x, b)))
  decreases a, b
{ }

lemma {:induction listLeft} Lemma_ListConcatUpperBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_upper_bound(listLeft, d)
  requires list_upper_bound(listRight, d)
  requires d >= x
  ensures list_upper_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{ }

lemma {:induction listLeft} Lemma_ListConcatLowerBound(listLeft:List<T>, listRight:List<T>, d:T, x:T)
  requires list_lower_bound(listLeft, d)
  requires list_lower_bound(listRight, d)
  requires d <= x
  ensures list_lower_bound(List_Concat(listLeft, Cons(x, listRight)), d)
  decreases listLeft
{ }
