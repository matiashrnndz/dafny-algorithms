include "../../src/Sorted.dfy"
include "../data-types/binary-tree/BST.dfy"

method TreeSort(L:List<int>) returns (sortedList:List<int>)
  ensures list_ascending_order(sortedList)
{
  var tree: BST<int> := BST_Init();
  var list := L;

  while list != List_Empty
    invariant bst_is_ordered(tree)
    decreases list
  {
    tree := BST_Insert(tree, List_Head(list));
    list := List_Tail(list);
  }

  sortedList := BST_InOrder(tree);

  return sortedList;
}
