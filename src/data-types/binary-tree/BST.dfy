include "../list/List.dfy"

// -------------------------- Datatype -------------------------- //

datatype Leaf = Nil
datatype BST<T> = Leaf | Node(left:BST<T>, data:T, right:BST<T>)

// ---------------------- Function Methods ---------------------- //

function method BST_Init() : (tree:BST<T>)
  ensures bst_is_ordered(tree)
{
  Leaf
}

function method BST_Size(tree:BST<T>) : (n:int)
  decreases tree
{
    match tree {
      case Leaf => 0
      case Node(left, x, right) => BST_Size(left) + 1 + BST_Size(right)
    }
}

function method BST_Insert(tree:BST<T>, d:T) : (result:BST<T>)
  decreases tree
  requires bst_is_ordered(tree)
  // Ensures que Result esté ordenado
{
  match tree {
    case Leaf => Node(Leaf, d, Leaf)
    case Node(left, x, right) => 
      if (d < x) 
        then Node(BST_Insert(left, d), x, right)
      else Node(left, x, BST_Insert(right, d))
  }
}

function method BST_InOrder(tree:BST<T>) : (result:List<T>)
  decreases tree
  requires bst_is_ordered(tree)
  ensures BST_InOrder(tree) == result
  // Ensures que Result esté ordenado
  // Ensures que el tree tenga los mismos elementos que el result
{
  match tree {
    case Leaf => List_Empty
    case Node(left, x, right) => List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))
  }
}

function method BST_ToSeq(tree:BST<T>) : seq<T>
  decreases tree
{
  match tree {
    case Leaf => []
    case Node(left, x, right) => BST_ToSeq(left) + [x] + BST_ToSeq(right)
  }
}

function method BST_ToSet(tree:BST<T>) : set<T>
  decreases tree
{
  match tree {
    case Leaf => {}
    case Node(left, x, right) => BST_ToSet(left) + {x} + BST_ToSet(right)
  }
}

function method BST_Contains(tree:BST<T>, d:T) : bool
  decreases tree
{
  match tree {
    case Leaf => false
    case Node(left, x, rigth) => BST_Contains(left, d) || BST_Contains(rigth, d)
  }
}

function method BST_Mirror(tree:BST<T>) : BST<T>
  decreases tree
{
  match tree {
    case Leaf => Leaf
    case Node(left, x, right) => Node(BST_Mirror(right), x, BST_Mirror(left))
  }
}


// ---------------------- Predicates ---------------------- //

predicate bst_is_ordered(tree:BST<T>)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(left, x, right) => 
      bst_is_ordered(left) &&
      bst_is_ordered(right) &&
      (forall y :: y in BST_ToSet(left) ==> y < x) &&
      (forall y :: y in BST_ToSet(right) ==> y >= x)
  }
}

// ------------------------ Lemmas ------------------------ //

/*
lemma {:induction false} InOrderElemsSameThanTreeElemsLemma(tree:BST<T>, result:List<T>)
  ensures List_ToSeq(BST_InOrder(tree)) == List_ToSeq(result)
{
  match tree {
    case Leaf =>
      calc == {
        List_ToSeq(BST_InOrder(tree));
          { assert BST_InOrder(tree) == List_Empty; }
        List_ToSeq(List_Empty);
          { assert List_Empty == result; }
        List_ToSeq(result);
      }
    case Node(left, x, right) =>
      calc == {
        List_ToSeq(BST_InOrder(tree));
          { assert List_ToSeq(BST_InOrder(tree)) == List_ToSeq(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))); }
        List_ToSeq(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right))));
          { assert List_ToSeq(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))) == List_ToSeq(BST_InOrder(left)) + List_ToSeq(List_Concat(Cons(x, List_Empty), BST_InOrder(right))); }
        List_ToSeq(BST_InOrder(left)) + List_ToSeq(List_Concat(Cons(x, List_Empty), BST_InOrder(right)));
          { assert List_ToSeq(List_Concat(Cons(x, List_Empty), BST_InOrder(right))) == List_ToSeq(Cons(x, List_Empty)) + List_ToSeq(BST_InOrder(right)); }
        List_ToSeq(BST_InOrder(left)) + List_ToSeq(Cons(x, List_Empty)) + List_ToSeq(BST_InOrder(right));
          { assert List_ToSeq(BST_InOrder(left)) + List_ToSeq(Cons(x, List_Empty)) + List_ToSeq(BST_InOrder(right)) == List_ToSeq(BST_InOrder(left)) + [x] + List_ToSeq(BST_InOrder(right)); }
        List_ToSeq(BST_InOrder(left)) + [x] + List_ToSeq(BST_InOrder(right));
          { InOrderElemsSameThanTreeElemsLemma(left, result); }
          { InOrderElemsSameThanTreeElemsLemma(right, result); }
      }
  }
}
*/