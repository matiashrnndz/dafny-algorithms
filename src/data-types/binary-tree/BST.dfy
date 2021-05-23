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
  // ensures bst_is_ordered (result)
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
  ensures BST_ToMultiset(tree) == List_ToMultiset(BST_InOrder(tree))
  ensures list_is_ordered(BST_InOrder(tree))
{
  match tree {
    case Leaf => List_Empty
    case Node(left, x, right) => List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))
  }
}

lemma {:induction tree} Lemma_IfBSTIsOrderedThenInOrderListIsOrdered(tree:BST<T>)
  requires bst_is_ordered(tree)
  ensures list_is_ordered(BST_InOrder(tree))
{
  match tree {
    case Leaf => // N/A
    case Node(left, x, right) => Lemma_SortedConcatWithMiddleElement(BST_InOrder(left), x, BST_InOrder(right));
  }
}

function method BST_ToMultiset(tree:BST<T>) : multiset<T>
  decreases tree
{
  match tree {
    case Leaf => multiset{}
    case Node(left, x, right) => multiset{x} + BST_ToMultiset(left) + BST_ToMultiset(right)
  }
}

function method BST_Contains(tree:BST<T>, d:T) : bool
  requires bst_is_ordered(tree)
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
      bst_high_bound(left, x) &&
      bst_low_bound(right, x)
  }
}

predicate bst_low_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(left, x, right) => d <= x && bst_low_bound(left, d) && bst_low_bound(right, d)
  }
}

predicate bst_high_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(left, x, right) => d > x && bst_high_bound(left, d) && bst_high_bound(right, d)
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction tree} Lemma_BSTSameElementsThanInOrder(tree:BST<T>)
  requires bst_is_ordered(tree)
  ensures BST_ToMultiset(tree) == List_ToMultiset(BST_InOrder(tree))
  decreases tree
{
  match tree {
    case Leaf =>
      calc == {
        BST_ToMultiset(tree);
          { assert tree == Leaf; }
        BST_ToMultiset(Leaf);
          { assert BST_ToMultiset(Leaf) == multiset{}; }
        multiset{};
          { assert multiset{} == List_ToMultiset(List_Empty); }
        List_ToMultiset(List_Empty);
          { assert List_Empty == BST_InOrder(Leaf); }
        List_ToMultiset(BST_InOrder(Leaf));
          { assert Leaf == tree; }
        List_ToMultiset(BST_InOrder(tree));
      }
    case Node(left, x, right) =>
      calc == {
        List_ToMultiset(BST_InOrder(tree));
          { assert List_ToMultiset(BST_InOrder(tree)) == List_ToMultiset(BST_InOrder(Node(left, x, right))); }
        List_ToMultiset(BST_InOrder(Node(left, x, right)));
          { assert List_ToMultiset(BST_InOrder(Node(left, x, right))) == List_ToMultiset(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))); }
        List_ToMultiset(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right))));
          { assert List_ToMultiset(List_Concat(BST_InOrder(left), List_Concat(Cons(x, List_Empty), BST_InOrder(right)))) == List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(List_Concat(Cons(x, List_Empty), BST_InOrder(right))); }
        List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(List_Concat(Cons(x, List_Empty), BST_InOrder(right)));
          { assert List_ToMultiset(List_Concat(Cons(x, List_Empty), BST_InOrder(right))) == List_ToMultiset(Cons(x, List_Empty)) + List_ToMultiset(BST_InOrder(right)); }
        List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(Cons(x, List_Empty)) + List_ToMultiset(BST_InOrder(right));
          { assert List_ToMultiset(Cons(x, List_Empty)) == multiset{x} + List_ToMultiset(List_Empty); }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + List_ToMultiset(List_Empty) + List_ToMultiset(BST_InOrder(right));
          { assert List_ToMultiset(List_Empty) == multiset{}; }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + multiset{} + List_ToMultiset(BST_InOrder(right));
          { assert multiset{x} + multiset{} == multiset{x}; }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + List_ToMultiset(BST_InOrder(right));
          { Lemma_BSTSameElementsThanInOrder(left); }
          { Lemma_BSTSameElementsThanInOrder(right); }
        BST_ToMultiset(tree);
      }
  }
}
