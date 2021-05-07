type T = int

datatype List<T> = Nil | Cons(head:T, tail:List<T>)

function create(): List<T>
{
  Nil
}

function method List_Insert(a:List<T>, x:T) : List<T>
  decreases a
{
  match a {
    case Nil => Cons(x, Nil)
    case Cons(h, t) => Cons(h, List_Insert(t, x))
  }
}

function method List_Concat(a:List<T>, b:List<T>) : List<T>
  decreases a
{
  match a {
    case Nil => b
    case Cons(h, t) => Cons(h, List_Concat(t, b))
  }
}

method List_Print(a:List<T>) {
  match a {
    case Nil => {
      return;
    }
    case Cons(h, Nil) => {
      print h, "\n";
      return;
    }
    case Cons(h, t) => {
      print h, ", ";
      List_Print(t);
    }
  }
}
