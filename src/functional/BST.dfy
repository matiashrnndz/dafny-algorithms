include "./List.dfy"

// -------------------------- Datatype -------------------------- //

datatype Leaf = Nil
datatype BST<T> = Leaf | Node(left:BST<T>, data:T, right:BST<T>)

// ---------------------- Function Methods ---------------------- //

function method BST_Insert(tree:BST<T>, d:T) : (result:BST<T>)
  // Lemma_BSTInsertOrdered(tree, d) ==> ensures bst_is_ordered(BST_Insert(tree, d))
  // Lemma_BSTInsertUpperBound(tree, d, b) ==> ensures bst_upper_bound(BST_Insert(tree, d), b)
  // Lemma_BSTInsertLowerBound(tree, d, b) ==> ensures bst_lower_bound(BST_Insert(tree, d), b)
  // Lemma_BSTInsertSameElemsPlusInserted(tree, d) ==> ensures BST_ToMultiset(tree) + multiset{d} == BST_ToMultiset(BST_Insert(tree, d)) 
  decreases tree
{
  match tree {
    case Leaf => Node(Leaf, d, Leaf)
    case Node(left, x, right) =>
      if (d < x) then
        Node(BST_Insert(left, d), x , right)
      else
        Node(left, x, BST_Insert(right, d))
  }
}

function method BST_InOrder(tree:BST<T>) : (result:List<T>)
  // Lemma_BSTSameElementsThanInOrder(tree) ==> ensures List_ToMultiset(BST_InOrder(tree)) == BST_ToMultiset(tree)
  // Lemma_BSTOrderedThenInOrderOrdered(tree) ==> ensures list_is_ordered(BST_InOrder(tree))
  // Lemma_BSTUpperBoundThenInOrderUpperBound(tree, d) ==> ensures list_upper_bound(BST_InOrder(tree), d)
  // Lemma_BSTLowerBoundThenInOrderLowerBound(tree, d) ==> ensures list_lower_bound(BST_InOrder(tree), d)
  decreases tree
{
  match tree {
    case Leaf => List_Empty
    case Node(left, x, right) => 
      List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))
  }
}

function method BST_Load(list:List<T>) : (tree:BST<T>)
  // Lemma_BSTLoadIsOrdered(list) ==> ensures bst_is_ordered(BST_Load(list))
  // Lemma_BSTLoadTreeElemsSameThanList(list:List<T>) ==> ensures List_ToMultiset(list) == BST_ToMultiset(BST_Load(list))
  decreases list
{
  match list {
    case List_Empty => Leaf
    case Cons(head, tail) => BST_Insert(BST_Load(tail), head)
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

function method BST_Size(tree:BST<T>) : (n:int)
  decreases tree
{
    match tree {
      case Leaf => 0
      case Node(left, x, right) => BST_Size(left) + 1 + BST_Size(right)
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

lemma {:induction tree} Lemma_BSTInsertOrdered(tree:BST<T>, d:T)
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
              { Lemma_BSTInsertUpperBound(left, d, x); }
              { assert bst_upper_bound(BST_Insert(left, d), x); }
              { Lemma_BSTInsertOrdered(left, d); }
            bst_is_ordered(Node(Leaf, d, Leaf));
          }
        } else {
          calc == {
            bst_is_ordered(Node(left, x, BST_Insert(right, d)));
              { Lemma_BSTInsertLowerBound(right, d, x); }
              { assert bst_lower_bound(BST_Insert(right, d), x); }
              { Lemma_BSTInsertOrdered(right, d); }
            bst_is_ordered(Node(Leaf, d, Leaf));
          }
        } }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTInsertUpperBound(tree:BST<T>, d:T, b:T)
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
          { Lemma_BSTInsertUpperBound(left, d, b); }
          { Lemma_BSTInsertUpperBound(right, d, b); }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTInsertLowerBound(tree:BST<T>, d:T, b:T)
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
          { Lemma_BSTInsertLowerBound(left, d, b); }
          { Lemma_BSTInsertLowerBound(right, d, b); }
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
          { assert tree == Node(left, x, right); }
        List_ToMultiset(BST_InOrder(Node(left, x, right)));
          { assert List_ToMultiset(BST_InOrder(Node(left, x, right))) == List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))); }
        List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))));
          { Lemma_ListConcatSameElems(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
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
          { Lemma_ListConcatSortedWithMiddleElement(BST_InOrder(left), x, BST_InOrder(right)); }
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
  ensures list_lower_bound(BST_InOrder(tree), d)
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

lemma {:induction tree} Lemma_BSTInsertSameElemsPlusInserted(tree:BST<T>, d:T)
  ensures BST_ToMultiset(BST_Insert(tree, d)) == BST_ToMultiset(tree) + multiset{d}
  decreases tree
{
  match tree {
    case Leaf => 
      calc == {
        BST_ToMultiset(BST_Insert(tree, d));
          { assert tree == Leaf; }
        BST_ToMultiset(BST_Insert(Leaf, d));
          { assert BST_Insert(Leaf, d) == Node(Leaf, d, Leaf); }
        BST_ToMultiset(Node(Leaf, d, Leaf));
          { assert BST_ToMultiset(Node(Leaf, d, Leaf)) == BST_ToMultiset(Leaf) + multiset{d} + BST_ToMultiset(Leaf); }
        BST_ToMultiset(Leaf) + multiset{d} + BST_ToMultiset(Leaf);
          { assert BST_ToMultiset(Leaf) == multiset{}; }
        BST_ToMultiset(Leaf) + multiset{d} + multiset{};
          { assert multiset{d} + multiset{} == multiset{d}; }
        BST_ToMultiset(Leaf) + multiset{d}; 
          { assert Leaf == tree; }
        BST_ToMultiset(tree) + multiset{d};
      }
    case Node(left, x, right) =>
      calc == {
        BST_ToMultiset(BST_Insert(tree, d));
          { assert tree == Node(left, x, right); }
        BST_ToMultiset(BST_Insert(Node(left, x, right), d));
        { if (d < x) {
          calc == {
            BST_ToMultiset(BST_Insert(Node(left, x, right), d));
              { assert BST_Insert(Node(left, x, right), d) == Node(BST_Insert(left, d), x , right); }
            BST_ToMultiset(Node(BST_Insert(left, d), x , right));
              { assert BST_ToMultiset(Node(BST_Insert(left, d), x , right)) == BST_ToMultiset(BST_Insert(left, d)) + multiset{x} + BST_ToMultiset(right); }
            BST_ToMultiset(BST_Insert(left, d)) + multiset{x} + BST_ToMultiset(right);
              { Lemma_BSTInsertSameElemsPlusInserted(left, d); }
          }
        } else {
          calc == {
            BST_ToMultiset(BST_Insert(Node(left, x, right), d));
              { assert BST_Insert(Node(left, x, right), d) == Node(left, x, BST_Insert(right, d)); }
            BST_ToMultiset(Node(left, x, BST_Insert(right, d)));
              { assert BST_ToMultiset(Node(BST_Insert(left, d), x , right)) == BST_ToMultiset(left) + multiset{x} + BST_ToMultiset(BST_Insert(right, d)); }
            BST_ToMultiset(left) + multiset{x} + BST_ToMultiset(BST_Insert(right, d));
              { Lemma_BSTInsertSameElemsPlusInserted(right, d); }
          }
        } }
        BST_ToMultiset(tree) + multiset{d};
      }
  }
}

lemma {:induction list} Lemma_BSTLoadIsOrdered(list:List<T>)
  ensures bst_is_ordered(BST_Load(list))
  decreases list
{
  match list {
    case List_Empty =>
      calc == {
        bst_is_ordered(BST_Load(list));
          { assert list == List_Empty; }
        bst_is_ordered(BST_Load(List_Empty));
          { assert BST_Load(List_Empty) == Leaf; }
        bst_is_ordered(Leaf);
          { assert bst_is_ordered(Leaf) == true; }
        true;
      }
    case Cons(head, tail) =>
      calc == {
        bst_is_ordered(BST_Load(list));
          { assert list == Cons(head, tail); }
        bst_is_ordered(BST_Load(Cons(head, tail)));
          { assert BST_Load(Cons(head, tail)) == BST_Insert(BST_Load(tail), head); }
        bst_is_ordered(BST_Insert(BST_Load(tail), head));
          { Lemma_BSTInsertOrdered(BST_Load(tail), head); }
        true;
      }
  }
}

lemma {:induction list} Lemma_BSTLoadTreeElemsSameThanList(list:List<T>)
  ensures BST_ToMultiset(BST_Load(list)) == List_ToMultiset(list)
  decreases list
{
  match list {
    case List_Empty =>
      calc == {
        BST_ToMultiset(BST_Load(list));
          { assert list == List_Empty; }
        BST_ToMultiset(BST_Load(List_Empty));
          { assert BST_Load(List_Empty) == Leaf; }
        BST_ToMultiset(Leaf);
          { assert BST_ToMultiset(Leaf) == multiset{}; }
        multiset{};
          { assert multiset{} == List_ToMultiset(List_Empty); }
        List_ToMultiset(List_Empty);
          { assert List_Empty == list; }
        List_ToMultiset(list);
      }
    case Cons(head, tail) =>
      calc == {
        BST_ToMultiset(BST_Load(list));
          { assert list == Cons(head, tail); }
        BST_ToMultiset(BST_Load(Cons(head, tail)));
          { assert BST_Load(Cons(head, tail)) == BST_Insert(BST_Load(tail), head); }
        BST_ToMultiset(BST_Insert(BST_Load(tail), head));
          { Lemma_BSTInsertSameElemsPlusInserted(BST_Load(tail), head); }
        BST_ToMultiset(BST_Load(tail)) + multiset{head};
          { Lemma_BSTLoadTreeElemsSameThanList(tail); }
        List_ToMultiset(list);
      }
  }
}

// ------------------ Dafny Automatic Lemmas ------------------ //

lemma {:induction list} Lemma_BSTLoadIsOrderedAuto(list:List<T>)
  ensures bst_is_ordered(BST_Load(list))
{
  match list {
    case List_Empty => 
      // AUTOMATIC
    case Cons(head, tail) =>
      calc == {
        bst_is_ordered(BST_Load(list));
          { assert list == Cons(head, tail); }
        bst_is_ordered(BST_Load(Cons(head, tail)));
          { assert BST_Load(Cons(head, tail)) == BST_Insert(BST_Load(tail), head); }
          { Lemma_BSTInsertOrdered(BST_Load(tail), head); }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTInsertSameElemsPlusInsertedAuto(tree:BST<T>, d:T)
  ensures BST_ToMultiset(BST_Insert(tree, d)) == BST_ToMultiset(tree) + multiset{d}
{
  // AUTOMATIC
}

// Faltan agregar más automáticos, hay que revisar los lemmas anteriores