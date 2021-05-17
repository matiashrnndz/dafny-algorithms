type T = int

datatype List_Empty = Nil
datatype List<T> = List_Empty | Cons(head:T, tail:List<T>)

// ------------------------- Functions -------------------------- //

function create(): List<T>
{
  List_Empty
}

// ---------------------- Function Methods ---------------------- //

function method {:tailrecursion true} List_Size(list:List<T>) : int
  decreases list
{
  match list {
    case List_Empty => 0
    case Cons(h, t) => List_Size(t) + 1
  }
}

function method List_Insert(list:List<T>, x:T) : List<T>
  decreases list
{
  match list {
    case List_Empty => Cons(x, List_Empty)
    case Cons(h, t) => Cons(h, List_Insert(t, x))
  }
}

function method List_Concat(a:List<T>, b:List<T>) : List<T>
  decreases a
  ensures List_Elems(List_Concat(a, b)) == List_Elems(a) + List_Elems(b)
  ensures List_Size(List_Concat(a, b)) == List_Size(a) + List_Size(b)
{
  match a {
    case List_Empty => b
    case Cons(h, t) =>
      match b {
        case List_Empty => a
        case Cons(hb, tb) => Cons(h, List_Concat(t, Cons(hb, tb)))
    }
  }
}

function method List_Head(xs:List<T>): T
  requires xs != List_Empty
{
  match xs
    case Cons(y, ys) => y
}

function method List_Tail(xs:List<T>): List<T>
{
  match xs
    case List_Empty => List_Empty
    case Cons(y, ys) => ys
}

// ------------------------- Methods -------------------------- //

method {:tailrecursion true} List_Print(a:List<T>) 
  decreases a
{
  match a {
    case List_Empty => {
      return;
    }
    case Cons(h, List_Empty) => {
      print h, "\n";
      return;
    }
    case Cons(h, t) => {
      print h, ", ";
      List_Print(t);
    }
  }
}

function method List_Elems(a:List<T>): seq<T>
  decreases a
{
  match a {
    case List_Empty => []
    case Cons(h, t) => [h] + List_Elems(t)
  }
}

// ---------------------- Predicates ---------------------- //

predicate list_ascending_order(list:List<T>) 
  decreases list
{
  match list {
    case List_Empty => true
    case Cons(h, List_Empty) => true
    case Cons(h, Cons(ht, t)) => h <= ht && list_ascending_order(t)
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction false} ConcatElemsLemma(a:List<T>, b:List<T>)
  ensures List_Elems(List_Concat(a, b)) == List_Elems(a) + List_Elems(b)
  decreases a, b
{
  match a {
    case List_Empty =>
      calc == {
        List_Elems(List_Concat(a, b));
          { assert List_Elems(a) + List_Elems(b) == List_Elems(b); }
        [] + List_Elems(b);
          { assert List_Elems(a) == []; }
        List_Elems(a) + List_Elems(b);
      }
    case Cons(ha, ta) =>
      calc == {
        List_Elems(List_Concat(a, b));
          { assert List_Elems(List_Concat(a, b)) == List_Elems(Cons(ha, List_Empty)) + List_Elems(List_Concat(ta, b)); }
        List_Elems(Cons(ha, List_Empty)) + List_Elems(List_Concat(ta, b));
          { ConcatElemsLemma(ta, b); }
        List_Elems(a) + List_Elems(b);
      }
  }
}

lemma {:induction false} ConcatSizeLemma(a:List<T>, b:List<T>)
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
          { ConcatSizeLemma(ta, b); }
        List_Size(a) + List_Size(b);
      }
  }
}
