include "./BST.dfy"
include "./List.dfy"

function method TreeSort(list:List<int>, tree:BST<T>) : (sortedList:List<int>)
  // Lemma_TreeSortListIsOrdered(list) ==> ensures list_is_ordered(TreeSort(list, Leaf))
  decreases list
{
  match list {
    case Cons(head, tail) => TreeSort(tail, BST_Insert(tree, head))
    case List_Empty => BST_InOrder(tree)
  }
}
