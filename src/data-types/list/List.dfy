type T = int

// -------------------------- Datatype -------------------------- //

datatype List_Empty = Nil
datatype List<T> = List_Empty | Cons(head:T, tail:List<T>)

// ------------------------- Functions -------------------------- //

function List_Init(): List<T>
{
  List_Empty
}

// ---------------------- Function Methods ---------------------- //

function method List_Size(list:List<T>) : int
  decreases list
{
  match list {
    case List_Empty => 0
    case Cons(head, tail) => 1 + List_Size(tail)
  }
}

function method List_Insert(list:List<T>, x:T) : List<T>
  decreases list
{
  match list {
    case List_Empty => Cons(x, List_Empty)
    case Cons(head, tail) => Cons(head, List_Insert(tail, x))
  }
}

function method List_Concat(a:List<T>, b:List<T>) : List<T>
  decreases a
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
{
  match a {
    case List_Empty => b
    case Cons(head, tail) => Cons(head, List_Concat(tail, b))
  }
}

function method List_Head(list:List<T>) : (head:T)
  requires list != List_Empty
{
  match list
    case Cons(head, tail) => head
}

function method List_Tail(list:List<T>) : (tail:List<T>)
  ensures if list != List_Empty then List_Size(tail) == List_Size(list) - 1 else List_Size(tail) == 0
{
  match list
    case List_Empty => List_Empty
    case Cons(head, tail) => tail
}

function method List_Last(list:List<T>) : (last:T)
  requires list != List_Empty
  decreases list
{
  match list {
    case Cons(last, List_Empty) => last
    case Cons(head, tail) => List_Last(tail)
  }
}

function List_Contains(list:List<T>, x:T) : bool
  decreases list
{
  match list {
    case List_Empty => false
    case Cons(head, tail) => head == x || List_Contains(tail, x) 
  }
}

function method List_ToMultiset(list:List<T>) : (m:multiset<T>)
  decreases list
{
  match list {
    case List_Empty => multiset{}
    case Cons(head, tail) => multiset{head} + List_ToMultiset(tail)
  }
}

// ------------------------- Methods -------------------------- //

method List_Print(list:List<T>) 
  decreases list
{
  match list {
    case List_Empty => {
      return;
    }
    case Cons(head, List_Empty) => {
      print head, "\n";
      return;
    }
    case Cons(head, tail) => {
      print head, ", ";
      List_Print(tail);
    }
  }
}

// ---------------------- Predicates ---------------------- //

predicate list_low_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, tail) => (d <= head) && list_low_bound(tail, d)
  }
}

predicate list_high_bound(list:List<T>, d:T)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, tail) => (d >= head) && list_high_bound(tail, head)
  }
}

predicate list_is_ordered(list:List<T>)
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, List_Empty) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_is_ordered(Cons(ht, tail))
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction a, b} Lemma_SortedConcatWithMiddleElement(a:List<T>, x:T, b:List<T>)
  requires list_is_ordered(a)
  requires list_is_ordered(b)
  requires list_low_bound(b, x)
  requires list_high_bound(a, x)
  ensures list_is_ordered(List_Concat(a, List_Concat(Cons(x, List_Empty), b)))
  decreases a, b
{
  match a {
    case List_Empty =>
      match b {
        case List_Empty =>
          calc == {
            list_is_ordered(List_Concat(a, List_Concat(Cons(x, List_Empty), b)));
              { Lemma_ConcatOfEmptyLists(a, b); }
            list_is_ordered(List_Empty);
              { assert list_is_ordered(List_Empty) == true; }
            true;
          }
        case Cons(hb, tb) =>
          calc == {
            list_is_ordered(List_Concat(a, List_Concat(Cons(x, List_Empty), b)));
              { Lemma_ConcatFirstListEmpty(a, b); }
            list_is_ordered(List_Concat(Cons(x, List_Empty), b));
              { assert List_Concat(Cons(x, List_Empty), b) == Cons(x, List_Concat(List_Empty, b)); }
            list_is_ordered(Cons(x, List_Concat(List_Empty, b)));
              { Lemma_ConcatFirstListEmpty(a, b); }
            list_is_ordered(Cons(x, b));
              { assert list_low_bound(b, x); }
              { assert list_is_ordered(b); }
            true;
          }
      }
    case Cons(ha, ta) =>
  }
}

lemma {:induction a} Lemma_ConcatFirstListEmpty(a:List<T>, b:List<T>)
  requires a == List_Empty
  ensures List_Concat(a, b) == b
{
  calc == {
    List_Concat(a, b);
      { assert a == List_Empty; }
    List_Concat(List_Empty, b);
      { assert List_Concat(List_Empty, b) == b; }
    b;
  }
}

lemma {:induction a} Lemma_ConcatSecondListEmpty(a:List<T>, b:List<T>)
  requires b == List_Empty
  ensures List_Concat(a, b) == a
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_Concat(a, b);
          { assert (a == List_Empty); }
        List_Concat(List_Empty, b);
          { assert List_Concat(List_Empty, b) == b; }
        b;
          { assert b == List_Empty; }
        List_Empty;
          { assert List_Empty == a; }
        a;
      }
    case Cons(ha, ta) =>
      calc == {
        List_Concat(a, b);
          { assert b == List_Empty; }
        List_Concat(a, List_Empty);
          { assert List_Concat(a, List_Empty) == Cons(ha, List_Concat(ta, List_Empty)); }
        Cons(ha, List_Concat(ta, List_Empty));
          { Lemma_ConcatSecondListEmpty(ta, List_Empty); }
        a;
      }
  }
}

lemma {:induction a, b} Lemma_ConcatOfEmptyLists(a:List<T>, b:List<T>)
  requires a == List_Empty
  requires b == List_Empty
  ensures List_Concat(a, b) == List_Empty
{
  calc == {
    List_Concat(a, b);
      { assert a == List_Empty; }
    List_Concat(List_Empty, b);
      { assert List_Concat(List_Empty, b) == b; }
    b;
      { assert b == List_Empty; }
    List_Empty;
  }
}

lemma {:induction a} Lemma_ConcatSameElems(a:List<T>, b:List<T>)
  ensures List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(a) + List_ToMultiset(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert List_ToMultiset(a) + List_ToMultiset(b) == List_ToMultiset(b); }
        multiset{} + List_ToMultiset(b);
          { assert List_ToMultiset(a) == multiset{}; }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_ToMultiset(List_Concat(a, b));
          { assert List_ToMultiset(List_Concat(a, b)) == List_ToMultiset(Cons(ha, List_Empty)) + List_ToMultiset(List_Concat(ta, b)); }
        List_ToMultiset(Cons(ha, List_Empty)) + List_ToMultiset(List_Concat(ta, b));
          { Lemma_ConcatSameElems(ta, b); }
        List_ToMultiset(a) + List_ToMultiset(b);
      }
  }
}

lemma {:induction a} Lemma_ConcatSameSize(a:List<T>, b:List<T>)
  ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_Size(List_Concat(a, b));
          { assert List_Size(a) + List_Size(b) == List_Size(b); }
        0 + List_Size(b);
          { assert List_Size(a) == 0; }
        List_Size(a) + List_Size(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_Size(List_Concat(a, b));
          { assert List_Size(List_Concat(a, b)) == List_Size(Cons(ha, List_Empty)) + List_Size(List_Concat(ta, b)); }
        List_Size(Cons(ha, List_Empty)) + List_Size(List_Concat(ta, b));
          { Lemma_ConcatSameSize(ta, b); }
        List_Size(a) + List_Size(b);
      }
  }
}
