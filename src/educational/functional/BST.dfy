include "./List.dfy"

// --------------------------------------- Datatypes -------------------------------------------- //

datatype BST<T> = Nil | Node(left:BST<T>, data:T, right:BST<T>)

// --------------------------------------- Predicates ------------------------------------------- //

predicate bst_ordered(tree:BST<T>)
  decreases tree
{
  match tree {
    case Nil => true
    case Node(left, x, right) =>
      bst_ordered(left) &&
      bst_ordered(right) &&
      bst_upper_bound(left, x) &&
      bst_lower_bound(right, x)
  }
}

predicate bst_lower_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Nil => true
    case Node(left, x, right) => d <= x && bst_lower_bound(left, d) && bst_lower_bound(right, d)
  }
}

predicate bst_upper_bound(tree:BST<T>, d:T)
  decreases tree
{
  match tree {
    case Nil => true
    case Node(left, x, right) => d >= x && bst_upper_bound(left, d) && bst_upper_bound(right, d)
  }
}

// ------------------------------------ Function Methods ---------------------------------------- //

function method BST_ToMultiset(tree:BST<T>) : multiset<T>
  decreases tree
{
  match tree {
    case Nil => multiset{}
    case Node(left, x, right) => multiset{x} + BST_ToMultiset(left) + BST_ToMultiset(right)
  }
}

/** Properties:
 *
 *  Lemma_BSTInsertIntegrity(tree, d)
 *    ==> ensures BST_ToMultiset(tree) + multiset{d} == BST_ToMultiset(BST_Insert(tree, d))
 *
 *  Lemma_BSTInsertOrdering(tree, d)
 *    ==> ensures bst_ordered(BST_Insert(tree, d))
 *
 *  Lemma_BSTInsertUpperBound(tree, d, b)
 *    ==> ensures bst_upper_bound(BST_Insert(tree, d), b)
 *
 *  Lemma_BSTInsertLowerBound(tree, d, b)
 *    ==> ensures bst_lower_bound(BST_Insert(tree, d), b)
 *
 */
function method BST_Insert(tree:BST<T>, d:T) : (result:BST<T>)
  decreases tree
{
  match tree {
    case Nil => Node(BST.Nil, d, BST.Nil)
    case Node(left, x, right) =>
      if (d < x) then
        Node(BST_Insert(left, d), x , right)
      else
        Node(left, x, BST_Insert(right, d))
  }
}

/** Properties:
 *
 *  Lemma_BSTLoadIntegrity(list:List<T>)
 *    ==> ensures List_ToMultiset(list) == BST_ToMultiset(BST_Load(list))
 *
*  Lemma_BSTLoadOrdering(list)
 *    ==> ensures bst_ordered(BST_Load(list))
 *
 */
function method BST_Load(list:List<T>) : (tree:BST<T>)
  decreases list
{
  match list {
    case Nil => BST.Nil
    case Cons(head, tail) => BST_Insert(BST_Load(tail), head)
  }
}

/** Properties:
 *
 *  Lemma_BSTInOrderIntegrity(tree)
 *    ==> ensures List_ToMultiset(BST_InOrder(tree)) == BST_ToMultiset(tree)
 *
 *  Lemma_BSTInOrderOrdering(tree)
 *    ==> ensures list_increasing(BST_InOrder(tree))
 *
 *  Lemma_BSTInOrderUpperBound(tree, d)
 *    ==> ensures list_upper_bound(BST_InOrder(tree), d)
 *
 *  Lemma_BSTInOrderLowerBound(tree, d)
 *    ==> ensures list_lower_bound(BST_InOrder(tree), d)
 *
 */
function method BST_InOrder(tree:BST<T>) : (result:List<T>)
  decreases tree
{
  match tree {
    case Nil => List.Nil
    case Node(left, x, right) => List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))
  }
}

// ------------------------------------ BST_Insert Lemmas --------------------------------------- //

lemma {:induction tree} Lemma_BSTInsertIntegrity(tree:BST<T>, d:T)
  ensures BST_ToMultiset(BST_Insert(tree, d)) == BST_ToMultiset(tree) + multiset{d}
  decreases tree
{
  match tree {
    case Nil => 
      calc == {
        BST_ToMultiset(BST_Insert(tree, d));
          { assert tree == BST.Nil; }
        BST_ToMultiset(BST_Insert(BST.Nil, d));
          { assert BST_Insert(BST.Nil, d) == Node(BST.Nil, d, BST.Nil); }
        BST_ToMultiset(Node(BST.Nil, d, BST.Nil));
          { assert BST_ToMultiset(Node(BST.Nil, d, BST.Nil))
                == BST_ToMultiset(BST.Nil) + multiset{d} + BST_ToMultiset(BST.Nil); }
        BST_ToMultiset(BST.Nil) + multiset{d} + BST_ToMultiset(BST.Nil);
          { assert BST_ToMultiset(BST.Nil) == multiset{}; }
        BST_ToMultiset(BST.Nil) + multiset{d} + multiset{};
          { assert multiset{d} + multiset{} == multiset{d}; }
        BST_ToMultiset(BST.Nil) + multiset{d}; 
          { assert BST.Nil == tree; }
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
              { assert BST_Insert(Node(left, x, right), d)
                    == Node(BST_Insert(left, d), x , right); }
            BST_ToMultiset(Node(BST_Insert(left, d), x , right));
              { assert BST_ToMultiset(Node(BST_Insert(left, d), x , right))
                    == BST_ToMultiset(BST_Insert(left, d)) + multiset{x} + BST_ToMultiset(right); }
            BST_ToMultiset(BST_Insert(left, d)) + multiset{x} + BST_ToMultiset(right);
              { Lemma_BSTInsertIntegrity(left, d); }
          }
        } else {
          calc == {
            BST_ToMultiset(BST_Insert(Node(left, x, right), d));
              { assert BST_Insert(Node(left, x, right), d)
                    == Node(left, x, BST_Insert(right, d)); }
            BST_ToMultiset(Node(left, x, BST_Insert(right, d)));
              { assert BST_ToMultiset(Node(BST_Insert(left, d), x , right))
                    == BST_ToMultiset(left) + multiset{x} + BST_ToMultiset(BST_Insert(right, d)); }
            BST_ToMultiset(left) + multiset{x} + BST_ToMultiset(BST_Insert(right, d));
              { Lemma_BSTInsertIntegrity(right, d); }
          }
        } }
        BST_ToMultiset(tree) + multiset{d};
      }
  }
}

lemma {:induction tree} Lemma_BSTInsertOrdering(tree:BST<T>, d:T)
  requires bst_ordered(tree)
  ensures bst_ordered(BST_Insert(tree, d))
  decreases tree
{
  match tree {
    case Nil =>
      calc == {
        bst_ordered(BST_Insert(tree, d));
          { assert tree == BST.Nil; }
        bst_ordered(BST_Insert(BST.Nil, d));
          { assert BST_Insert(BST.Nil, d) == Node(BST.Nil, d, BST.Nil); }
        bst_ordered(Node(BST.Nil, d, BST.Nil));
        true;
      }
    case Node(left, x, right) =>
      calc == {
        bst_ordered(BST_Insert(tree, d));
          { assert tree == Node(left, x, right); }
        bst_ordered(BST_Insert(Node(left, x, right), d));
        { if (d < x) {
          calc == {
            bst_ordered(Node(BST_Insert(left, d), x, right));
              { Lemma_BSTInsertUpperBound(left, d, x); }
              { assert bst_upper_bound(BST_Insert(left, d), x); }
              { Lemma_BSTInsertOrdering(left, d); }
            bst_ordered(Node(BST.Nil, d, BST.Nil));
          }
        } else {
          calc == {
            bst_ordered(Node(left, x, BST_Insert(right, d)));
              { Lemma_BSTInsertLowerBound(right, d, x); }
              { assert bst_lower_bound(BST_Insert(right, d), x); }
              { Lemma_BSTInsertOrdering(right, d); }
            bst_ordered(Node(BST.Nil, d, BST.Nil));
          }
        } }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTInsertUpperBound(tree:BST<T>, d:T, b:T)
  requires bst_ordered(tree)
  requires bst_upper_bound(tree, b)
  requires b > d
  ensures bst_upper_bound(BST_Insert(tree, d), b)
  decreases tree
{
  match tree {
    case Nil =>
      calc == {
        bst_upper_bound(BST_Insert(tree, d), b);
          { assert tree == BST.Nil; }
        bst_upper_bound(BST_Insert(BST.Nil, d), b);
          { assert bst_upper_bound(BST_Insert(BST.Nil, d), b)
                == bst_upper_bound(Node(BST.Nil, d, BST.Nil), b); }
        bst_upper_bound(Node(BST.Nil, d, BST.Nil), b);
          { assert bst_upper_bound(Node(BST.Nil, d, BST.Nil), b)
                == (b >= d && bst_upper_bound(BST.Nil, b) && bst_upper_bound(BST.Nil, b)); }
        (b >= d && bst_upper_bound(BST.Nil, b) && bst_upper_bound(BST.Nil, b));
          { assert bst_upper_bound(BST.Nil, b) == true; }
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
  requires bst_ordered(tree)
  requires bst_lower_bound(tree, b)
  requires b <= d
  ensures bst_lower_bound(BST_Insert(tree, d), b)
  decreases tree
{
  match tree {
    case Nil =>
      calc == {
        bst_lower_bound(BST_Insert(tree, d), b);
          { assert tree == BST.Nil; }
        bst_lower_bound(BST_Insert(BST.Nil, d), b);
          { assert bst_lower_bound(BST_Insert(BST.Nil, d), b)
                == bst_lower_bound(Node(BST.Nil, d, BST.Nil), b); }
        bst_lower_bound(Node(BST.Nil, d, BST.Nil), b);
          { assert bst_lower_bound(Node(BST.Nil, d, BST.Nil), b)
                == (b <= d && bst_lower_bound(BST.Nil, b) && bst_lower_bound(BST.Nil, b)); }
        (b <= d && bst_lower_bound(BST.Nil, b) && bst_lower_bound(BST.Nil, b));
          { assert bst_lower_bound(BST.Nil, b) == true; }
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

// ------------------------------------- BST_Load Lemmas ---------------------------------------- //

lemma {:induction list} Lemma_BSTLoadIntegrity(list:List<T>)
  ensures BST_ToMultiset(BST_Load(list)) == List_ToMultiset(list)
  decreases list
{
  match list {
    case Nil =>
      calc == {
        BST_ToMultiset(BST_Load(list));
          { assert list == List.Nil; }
        BST_ToMultiset(BST_Load(List.Nil));
          { assert BST_Load(List.Nil) == BST.Nil; }
        BST_ToMultiset(BST.Nil);
          { assert BST_ToMultiset(BST.Nil) == multiset{}; }
        multiset{};
          { assert multiset{} == List_ToMultiset(List.Nil); }
        List_ToMultiset(List.Nil);
          { assert List.Nil == list; }
        List_ToMultiset(list);
      }
    case Cons(head, tail) =>
      calc == {
        BST_ToMultiset(BST_Load(list));
          { assert list == Cons(head, tail); }
        BST_ToMultiset(BST_Load(Cons(head, tail)));
          { assert BST_Load(Cons(head, tail)) == BST_Insert(BST_Load(tail), head); }
        BST_ToMultiset(BST_Insert(BST_Load(tail), head));
          { Lemma_BSTInsertIntegrity(BST_Load(tail), head); }
        BST_ToMultiset(BST_Load(tail)) + multiset{head};
          { Lemma_BSTLoadIntegrity(tail); }
        List_ToMultiset(list);
      }
  }
}

lemma {:induction list} Lemma_BSTLoadOrdering(list:List<T>)
  ensures bst_ordered(BST_Load(list))
  decreases list
{
  match list {
    case Nil =>
      calc == {
        bst_ordered(BST_Load(list));
          { assert list == List.Nil; }
        bst_ordered(BST_Load(List.Nil));
          { assert BST_Load(List.Nil) == BST.Nil; }
        bst_ordered(BST.Nil);
          { assert bst_ordered(BST.Nil) == true; }
        true;
      }
    case Cons(head, tail) =>
      calc == {
        bst_ordered(BST_Load(list));
          { assert list == Cons(head, tail); }
        bst_ordered(BST_Load(Cons(head, tail)));
          { assert BST_Load(Cons(head, tail)) 
                == BST_Insert(BST_Load(tail), head); }
        bst_ordered(BST_Insert(BST_Load(tail), head));
          { Lemma_BSTInsertOrdering(BST_Load(tail), head); }
        true;
      }
  }
}

// ----------------------------------- BST_InOrder Lemmas --------------------------------------- //

lemma {:induction tree} Lemma_BSTInOrderIntegrity(tree:BST<T>)
  ensures BST_ToMultiset(tree) == List_ToMultiset(BST_InOrder(tree))
  decreases tree
{
  match tree {
    case Nil =>
      calc == {
        BST_ToMultiset(tree);
          { assert tree == BST.Nil; }
        BST_ToMultiset(BST.Nil);
          { assert BST_ToMultiset(BST.Nil) == multiset{}; }
        multiset{};
          { assert multiset{} == List_ToMultiset(List.Nil); }
        List_ToMultiset(List.Nil);
          { assert List.Nil == BST_InOrder(BST.Nil); }
        List_ToMultiset(BST_InOrder(BST.Nil));
          { assert BST.Nil == tree; }
        List_ToMultiset(BST_InOrder(tree));
      }
    case Node(left, x, right) =>
      calc == {
        List_ToMultiset(BST_InOrder(tree));
          { assert tree == Node(left, x, right); }
        List_ToMultiset(BST_InOrder(Node(left, x, right)));
          { assert List_ToMultiset(BST_InOrder(Node(left, x, right)))
                == List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right)))); }
        List_ToMultiset(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))));
          { Lemma_ListConcatIntegrity(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
        List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(Cons(x, BST_InOrder(right)));
          { assert List_ToMultiset(Cons(x, BST_InOrder(right)))
                == List_ToMultiset(Cons(x, List.Nil)) + List_ToMultiset(BST_InOrder(right)); }
        List_ToMultiset(BST_InOrder(left)) + List_ToMultiset(Cons(x, List.Nil)) + List_ToMultiset(BST_InOrder(right));
          { assert List_ToMultiset(Cons(x, List.Nil))
                == multiset{x} + List_ToMultiset(List.Nil); }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + List_ToMultiset(List.Nil) + List_ToMultiset(BST_InOrder(right));
          { assert List_ToMultiset(List.Nil) == multiset{}; }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + multiset{} + List_ToMultiset(BST_InOrder(right));
          { assert multiset{x} + multiset{} == multiset{x}; }
        List_ToMultiset(BST_InOrder(left)) + multiset{x} + List_ToMultiset(BST_InOrder(right));
          { Lemma_BSTInOrderIntegrity(left); }
          { Lemma_BSTInOrderIntegrity(right); }
        BST_ToMultiset(tree);
      }
  }
}

lemma {:induction tree} Lemma_BSTInOrderOrdering(tree:BST<T>)
  requires bst_ordered(tree)
  ensures list_increasing(BST_InOrder(tree))
{
  match tree {
    case Nil =>
      calc == {
        list_increasing(BST_InOrder(tree));
          { assert tree == BST.Nil; }
        list_increasing(BST_InOrder(BST.Nil));
          { assert BST_InOrder(BST.Nil) == List.Nil; }
        list_increasing(List.Nil);
        true;
      }
    case Node(left, x, right) =>
      calc == {
        list_increasing(BST_InOrder(tree));
          { assert tree == Node(left, x, right); }
        list_increasing(BST_InOrder(Node(left, x, right)));
          { assert BST_InOrder(Node(left, x, right))
                == List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
        list_increasing(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))));
          { assert bst_lower_bound(right, x); }
          { Lemma_BSTInOrderLowerBound(right, x); }
          { assert bst_upper_bound(left, x); }
          { Lemma_BSTInOrderUpperBound(left, x); }
          { Lemma_ListConcatWithMidElemOrdering(BST_InOrder(left), x, BST_InOrder(right)); }
        true;
      }
  }
}

lemma {:induction tree} Lemma_BSTInOrderUpperBound(tree:BST<T>, d:T)
  requires bst_ordered(tree)
  requires bst_upper_bound(tree, d)
  ensures list_upper_bound(BST_InOrder(tree), d)
{
  match tree {
    case Nil =>
      calc == {
        list_upper_bound(BST_InOrder(tree), d);
          { assert tree == BST.Nil; }
        list_upper_bound(BST_InOrder(BST.Nil), d);
          { assert BST_InOrder(BST.Nil) == List.Nil; }
        list_upper_bound(List.Nil, d);
        true;
      }
      case Node(left, x, right) =>
        calc == {
          list_upper_bound(BST_InOrder(tree), d);
            { assert tree == Node(left, x, right); }
          list_upper_bound(BST_InOrder(Node(left, x, right)), d);
            { assert BST_InOrder(Node(left, x, right))
                  == List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
          list_upper_bound(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))), d);
            { assert list_upper_bound(BST_InOrder(left), d); }
            { assert list_upper_bound(BST_InOrder(right), d); }
            { assert d >= x; }
            { Lemma_ListConcatUpperBound(BST_InOrder(left), BST_InOrder(right), d, x); }
          true;
        }
  }
}

lemma {:induction tree} Lemma_BSTInOrderLowerBound(tree:BST<T>, d:T)
  requires bst_ordered(tree)
  requires bst_lower_bound(tree, d)
  ensures list_lower_bound(BST_InOrder(tree), d)
{
  match tree {
    case Nil =>
      calc == {
        list_lower_bound(BST_InOrder(tree), d);
          { assert tree == BST.Nil; }
        list_lower_bound(BST_InOrder(BST.Nil), d);
          { assert BST_InOrder(BST.Nil) == List.Nil; }
        list_lower_bound(List.Nil, d);
        true;
      }
      case Node(left, x, right) =>
        calc == {
          list_lower_bound(BST_InOrder(tree), d);
            { assert tree == Node(left, x, right); }
          list_lower_bound(BST_InOrder(Node(left, x, right)), d);
            { assert BST_InOrder(Node(left, x, right))
                  == List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))); }
          list_lower_bound(List_Concat(BST_InOrder(left), Cons(x, BST_InOrder(right))), d);
            { assert list_lower_bound(BST_InOrder(left), d); }
            { assert list_lower_bound(BST_InOrder(right), d); }
            { assert d <= x; }
            { Lemma_ListConcatLowerBound(BST_InOrder(left), BST_InOrder(right), d, x); }
          true;
        }
  }
}
