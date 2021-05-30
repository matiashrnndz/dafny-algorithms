include "./BST.dfy"
include "./List.dfy"

function method TreeSort(list:List<int>, tree:BST<T>) : (sortedList:List<int>)
  requires bst_is_ordered(tree)
  ensures list_is_ordered(sortedList)
  decreases list
{
  match list {
    case Cons(head, tail) => TreeSort(tail, BST_Insert(tree, head))
    case List_Empty => BST_InOrder(tree)
  }
}