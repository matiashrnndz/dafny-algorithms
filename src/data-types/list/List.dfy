type T = int

datatype List_Empty = Nil
datatype List<T> = List_Empty | Cons(head:T, tail:List<T>)

function create(): List<T>
{
  List_Empty
}

function method List_Size(list:List<T>) : int
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
{
  match a {
    case List_Empty => b
    case Cons(h, t) => Cons(h, List_Concat(t, b))
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

method List_Print(a:List<T>) 
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
