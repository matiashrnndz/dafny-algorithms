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
  requires bst_is_ordered(tree)
  ensures bst_is_ordered(BST_Insert(tree, d)) // Postcondition that might not hold
  decreases tree
{
  match tree {
    case Leaf => Node(Leaf, d, Leaf)
    case Node(left, x, right) => 
      if (d < x)
        then Node(BST_Insert(left, d), x , right)
      else Node(left, x, BST_Insert(right, d))
  }
}

function method BST_InOrder(tree:BST<T>) : (result:List<T>)
  requires bst_is_ordered(tree)
  ensures BST_ToMultiset(tree) == List_ToMultiset(BST_InOrder(tree))
  ensures list_is_ordered(BST_InOrder(tree)) // Postcondition that might not hold
  decreases tree
{
  match tree {
    case Leaf => List_Empty
    case Node(left, x, right) => List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))
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
      bst_upper_bound(left, x) &&
      bst_lower_bound(right, x)
  }
}

predicate bst_lower_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(left, x, right) => d <= x && bst_lower_bound(left, d) && bst_lower_bound(right, d)
  }
}

predicate bst_upper_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(left, x, right) => d >= x && bst_upper_bound(left, d) && bst_upper_bound(right, d)
  }
}

// ------------------------ Lemmas ------------------------ //

lemma {:induction tree} Lemma_InsertOrdered(tree:BST<T>, d:T)
  requires bst_is_ordered(tree)
  ensures bst_is_ordered(BST_Insert(tree, d))
  decreases tree
{
  match tree {
    case Leaf =>
      calc == {
        bst_is_ordered(BST_Insert(tree, d));
          { assert tree == Leaf; }
        bst_is_ordered(BST_Insert(Leaf, d));
          { assert BST_Insert(Leaf, d) == Node(Leaf, d, Leaf); }
        bst_is_ordered(Node(Leaf, d, Leaf));
        true;
      }
    case Node(left, x, right) =>
      calc == {
        bst_is_ordered(BST_Insert(tree, d));
          { assert tree == Node(left, x, right); }
        bst_is_ordered(BST_Insert(Node(left, x, right), d));
        { if (d < x) {
          calc == {
            bst_is_ordered(Node(BST_Insert(left, d), x, right));
              { Lemma_InsertUpperBound(left, d, x); }
              { assert bst_upper_bound(BST_Insert(left, d), x); }
              { Lemma_InsertOrdered(left, d); }
            bst_is_ordered(Node(Leaf, d, Leaf));
          }
        } else {
          calc == {
            bst_is_ordered(Node(left, x, BST_Insert(right, d)));
              { Lemma_InsertLowerBound(right, d, x); }
              { assert bst_lower_bound(BST_Insert(right, d), x); }
              { Lemma_InsertOrdered(right, d); }
            bst_is_ordered(Node(Leaf, d, Leaf));
          }
        } }
        true;
      }
  }
}

lemma {:induction tree} Lemma_InsertUpperBound(tree:BST<T>, d:T, b:T)
  requires bst_is_ordered(tree)
  requires bst_upper_bound(tree, b)
  requires b > d
  ensures bst_upper_bound(BST_Insert(tree, d), b)
  decreases tree
{
  match tree {
    case Leaf =>
      calc == {
        bst_upper_bound(BST_Insert(tree, d), b);
          { assert tree == Leaf; }
        bst_upper_bound(BST_Insert(Leaf, d), b);
          { assert bst_upper_bound(BST_Insert(Leaf, d), b) == bst_upper_bound(Node(Leaf, d, Leaf), b); }
        bst_upper_bound(Node(Leaf, d, Leaf), b);
          { assert bst_upper_bound(Node(Leaf, d, Leaf), b) == (b >= d && bst_upper_bound(Leaf, b) && bst_upper_bound(Leaf, b)); }
        (b >= d && bst_upper_bound(Leaf, b) && bst_upper_bound(Leaf, b));
          { assert bst_upper_bound(Leaf, b) == true; }
        (b >= d && true && true);
          { assert (b >= d && true && true) == (b >= d); }
        (b >= d);
          { assert b > d; }
        true;
      }
    case Node(left, x, right) =>
      calc == {
        bst_upper_bound(BST_Insert(tree, d), b);
          { assert tree == Node(left, x, right); }
        bst_upper_bound(BST_Insert(Node(left, x, right), d), b);
          { Lemma_InsertUpperBound(left, d, b); }
          { Lemma_InsertUpperBound(right, d, b); }
        true;
      }
  }
}

lemma {:induction tree} Lemma_InsertLowerBound(tree:BST<T>, d:T, b:T)
  requires bst_is_ordered(tree)
  requires bst_lower_bound(tree, b)
  requires b <= d
  ensures bst_lower_bound(BST_Insert(tree, d), b)
  decreases tree
{
  match tree {
    case Leaf =>
      calc == {
        bst_lower_bound(BST_Insert(tree, d), b);
          { assert tree == Leaf; }
        bst_lower_bound(BST_Insert(Leaf, d), b);
          { assert bst_lower_bound(BST_Insert(Leaf, d), b) == bst_lower_bound(Node(Leaf, d, Leaf), b); }
        bst_lower_bound(Node(Leaf, d, Leaf), b);
          { assert bst_lower_bound(Node(Leaf, d, Leaf), b) == (b <= d && bst_lower_bound(Leaf, b) && bst_lower_bound(Leaf, b)); }
        (b <= d && bst_lower_bound(Leaf, b) && bst_lower_bound(Leaf, b));
          { assert bst_lower_bound(Leaf, b) == true; }
        (b <= d && true && true);
          { assert (b <= d && true && true) == (b <= d); }
        (b <= d);
          { assert b <= d; }
        true;
      }
    case Node(left, x, right) =>
      calc == {
        bst_lower_bound(BST_Insert(tree, d), b);
          { assert tree == Node(left, x, right); }
        bst_lower_bound(BST_Insert(Node(left, x, right), d), b);
          { Lemma_InsertLowerBound(left, d, b); }
          { Lemma_InsertLowerBound(right, d, b); }
        true;
      }
  }
}

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
          { assert List_ToMultiset(BST_InOrder(Node(left, x, right))) == List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))); }
        List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))));
          { assert List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))) == List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(Cons(x, BST_InOrder(right))); }
        List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(Cons(x, BST_InOrder(right)));
          { assert List_ToMultiset(Cons(x, BST_InOrder(right))) == List_ToMultiset(Cons(x, List_Empty)) + List_ToMultiset(BST_InOrder(right)); }
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

lemma {:induction tree} Lemma_BSTOrderedThenInOrderOrdered(tree:BST<T>)
  requires bst_is_ordered(tree)
  ensures list_is_ordered(BST_InOrder(tree))
{
  match tree {
    case Leaf =>
      calc == {
        list_is_ordered(BST_InOrder(tree));
          { assert tree == Leaf; }
        list_is_ordered(BST_InOrder(Leaf));
          { assert BST_InOrder(Leaf) == List_Empty; }
        list_is_ordered(List_Empty);
        true;
      }
    case Node(left, x, right) =>
      calc == {
        list_is_ordered(BST_InOrder(tree));
          { assert tree == Node(left, x, right); }
        list_is_ordered(BST_InOrder(Node(left, x, right)));
          { assert BST_InOrder(Node(left, x, right)) ==  List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
        list_is_ordered(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))));
          { assert bst_lower_bound(right, x); }
          { Lemma_BSTLowerBoundThenInOrderLowerBound(right, x); }
          { assert bst_upper_bound(left, x); }
          { Lemma_BSTUpperBoundThenInOrderUpperBound(left, x); }
          { Lemma_ConcatSortedWithMiddleElement(BST_InOrder(left), x, BST_InOrder(right)); }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTUpperBoundThenInOrderUpperBound(tree:BST<T>, d:T)
  requires bst_is_ordered(tree)
  requires bst_upper_bound(tree, d)
  ensures list_upper_bound(BST_InOrder(tree), d)
{
  match tree {
    case Leaf =>
      calc == {
        list_upper_bound(BST_InOrder(tree), d);
          { assert tree == Leaf; }
        list_upper_bound(BST_InOrder(Leaf), d);
          { assert BST_InOrder(Leaf) == List_Empty; }
        list_upper_bound(List_Empty, d);
        true;
      }
      case Node(left, x, right) =>
        calc == {
          list_upper_bound(BST_InOrder(tree), d);
            { assert tree == Node(left, x, right); }
          list_upper_bound(BST_InOrder(Node(left, x, right)), d);
            { assert BST_InOrder(Node(left, x, right)) == List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
          list_upper_bound(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))), d);
            { assert list_upper_bound(BST_InOrder(left), d); }
            { assert list_upper_bound(BST_InOrder(right), d); }
            { assert d >= x; }
            { Lemma_IfElemUpperBoundOfTwoListsThenIsUpperBoundOfConcat(BST_InOrder(left), BST_InOrder(right), d, x); }
          true;
        }
  }
}

lemma {:induction tree} Lemma_BSTLowerBoundThenInOrderLowerBound(tree:BST<T>, d:T)
  requires bst_is_ordered(tree)
  requires bst_lower_bound(tree, d)
  ensures list_lower_bound(BST_InOrder(tree), d) == true
{
  match tree {
    case Leaf =>
      calc == {
        list_lower_bound(BST_InOrder(tree), d);
          { assert tree == Leaf; }
        list_lower_bound(BST_InOrder(Leaf), d);
          { assert BST_InOrder(Leaf) == List_Empty; }
        list_lower_bound(List_Empty, d);
        true;
      }
      case Node(left, x, right) =>
        calc == {
          list_lower_bound(BST_InOrder(tree), d);
            { assert tree == Node(left, x, right); }
          list_lower_bound(BST_InOrder(Node(left, x, right)), d);
            { assert BST_InOrder(Node(left, x, right)) == List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
          list_lower_bound(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))), d);
            { assert list_lower_bound(BST_InOrder(left), d); }
            { assert list_lower_bound(BST_InOrder(right), d); }
            { assert d <= x; }
            { Lemma_IfElemLowerBoundOfTwoListsThenIsLowerBoundOfConcat(BST_InOrder(left), BST_InOrder(right), d, x); }
          true;
        }
  }
}

/*
function method BST_Load(list:List<T>): (result:BST<T>)
  ensures bst_is_ordered(result)
  ensures BST_ToMultiset(result) == List_ToMultiset(input)
{

}

lemma Lemma_MultisetLoadSameElementsThanList(input:List<T>)
  ensures BST_ToMultiset(BST_Load(input)) == List_ToMultiset(input)
{

}

lemma Lemma_LoadOrdered(input:List<T>)
  ensures bst_is_ordered(BST_Load(input))
{

}
*/
