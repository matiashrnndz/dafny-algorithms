include "./BST.dfy"
include "./List.dfy"

function method TreeSort(list:List<int>, tree:BST<T>) : (sortedList:List<int>)
  // Lemma_TreeSortListIsOrdered(list, tree) ==> ensures list_is_ordered(TreeSort(list, Leaf))
  decreases list
{
  match list {
    case Cons(head, tail) => TreeSort(tail, BST_Insert(tree, head))
    case List_Empty => BST_InOrder(tree)
  }
}

/*
lemma {:induction list} Lemma_TreeSortListIsOrdered(list:List<T>, tree:BST<T>)
  ensures list_is_ordered(TreeSort(list, tree))
{
  match list {
    case List_Empty =>
      calc == {
        list_is_ordered(TreeSort(list, Leaf));
          { assert list == List_Empty; }
        list_is_ordered(TreeSort(List_Empty, Leaf));
          { assert TreeSort(List_Empty, Leaf) == BST_InOrder(Leaf); }
        list_is_ordered(BST_InOrder(Leaf));
          { assert BST_InOrder(Leaf) == List_Empty; }
        list_is_ordered(List_Empty);
          { assert list_is_ordered(List_Empty) == true; }
        true;
      }
    case Cons(head, tail) =>
      calc == {
        list_is_ordered(TreeSort(list, Leaf));
          { assert list == Cons(head, tail); }
        list_is_ordered(TreeSort(Cons(head, tail), Leaf));
          { assert TreeSort(Cons(head, tail), Leaf) == TreeSort(tail, BST_Insert(Leaf, head)); }
        list_is_ordered(TreeSort(tail, BST_Insert(Leaf, head)));
          { Lemma_InsertOrdered(tree, head); }
          { assert BST_Insert(Leaf, head) == Node(Leaf, head, Leaf); }
        list_is_ordered(TreeSort(tail, Node(Leaf, head, Leaf)));
        match tail {
          case List_Empty =>
            calc == {
              list_is_ordered(TreeSort(tail, Node(Leaf, head, Leaf)));
                { assert tail == List_Empty; }
              list_is_ordered(TreeSort(List_Empty, Node(Leaf, head, Leaf)));
                { assert TreeSort(List_Empty, Node(Leaf, head, Leaf)) == BST_InOrder(Node(Leaf, head, Leaf)); }
              list_is_ordered(BST_InOrder(Node(Leaf, head, Leaf)));
                { assert BST_InOrder(Node(Leaf, head, Leaf)) == List_Concat(BST_InOrder(Leaf), Cons(head, BST_InOrder(Leaf))); }
              list_is_ordered(List_Concat(BST_InOrder(Leaf), Cons(head, BST_InOrder(Leaf))));
                { assert BST_InOrder(Leaf) == List_Empty; }
              list_is_ordered(List_Concat(List_Empty, Cons(head, List_Empty)));
                { Lemma_ConcatFirstListEmpty(List_Empty, Cons(head, List_Empty)); }
              list_is_ordered(Cons(head, List_Empty));
                { assert list_is_ordered(Cons(head, List_Empty)) == true; }
              true;
            }
          case Cons(tah, tat) =>
            calc == {
              list_is_ordered(TreeSort(tail, Node(Leaf, head, Leaf)));
                { assert tail == Cons(tah, tat); }
              list_is_ordered(TreeSort(Cons(tah, tat), Node(Leaf, head, Leaf)));
                { assert TreeSort(Cons(tah, tat), Node(Leaf, head, Leaf)) == TreeSort(tat, BST_Insert(Node(Leaf, head, Leaf), tah)); }
              list_is_ordered(TreeSort(tat, BST_Insert(Node(Leaf, head, Leaf), tah)));
                { Lemma_TreeSortListIsOrdered(tat, BST_Insert(Node(Leaf, head, Leaf), tah)); }
              true;
            }
        }
        true;
      }
  }
}
*/
