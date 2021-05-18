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

function method {:tailrecursion true} List_Size(list:List<T>) : int
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
  ensures List_ToSeq(List_Concat(a, b)) == List_ToSeq(a) + List_ToSeq(b)
  ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
{
  match a {
    case List_Empty => b
    case Cons(head, tail) =>  Cons(head, List_Concat(tail, b))
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

function List_Contains(list:List<T>, x:T) : bool
  decreases list
{
  match list {
    case List_Empty => false
    case Cons(head, tail) => head == x || List_Contains(tail, x) 
  }
}

// ------------------------- Methods -------------------------- //

method {:tailrecursion true} List_Print(list:List<T>) 
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

function method List_ToSeq(list:List<T>) : (s:seq<T>)
  // Ensures que tengan los mismos elementos la lista y la seq
  decreases list
{
  match list {
    case List_Empty => []
    case Cons(head, tail) => [head] + List_ToSeq(tail)
  }
}

function method List_ToSet(list:List<T>) : (s:set<T>)
  // Ensures que tengan los mismos elementos la lista y el set
  decreases list
{
  match list {
    case List_Empty => {}
    case Cons(head, tail) => {head} + List_ToSet(tail)
  }
}

// ---------------------- Predicates ---------------------- //

predicate list_ascending_order(list:List<T>) 
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(head, List_Empty) => true
    case Cons(head, Cons(ht, tail)) => head <= ht && list_ascending_order(tail)
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction false} Lemma_ConcatElems(a:List<T>, b:List<T>)
  ensures List_ToSeq(List_Concat(a, b)) == List_ToSeq(a) + List_ToSeq(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_ToSeq(List_Concat(a, b));
          { assert List_ToSeq(a) + List_ToSeq(b) == List_ToSeq(b); }
        [] + List_ToSeq(b);
          { assert List_ToSeq(a) == []; }
        List_ToSeq(a) + List_ToSeq(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_ToSeq(List_Concat(a, b));
          { assert List_ToSeq(List_Concat(a, b)) == List_ToSeq(Cons(ha, List_Empty)) + List_ToSeq(List_Concat(ta, b)); }
        List_ToSeq(Cons(ha, List_Empty)) + List_ToSeq(List_Concat(ta, b));
          { Lemma_ConcatElems(ta, b); }
        List_ToSeq(a) + List_ToSeq(b);
      }
  }
}

lemma {:induction false} Lemma_ConcatSize(a:List<T>, b:List<T>)
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
          { Lemma_ConcatSize(ta, b); }
        List_Size(a) + List_Size(b);
      }
  }
}
