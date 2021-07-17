include "../functional/Sorted.dfy"
include "../functional/BST.dfy"
include "../functional/List.dfy"

method TreeSort(L:List<int>) returns (sortedList:List<int>)
  ensures list_ordered(sortedList)
{
  var tree: BST<int> := Leaf;
  var list := L;

  while list != List_Empty
    invariant bst_ordered(tree)
    decreases list
  {
    var elem := List_Head(list);
    Lemma_BSTInsertOrdering(tree, elem);
    tree := BST_Insert(tree, elem);
    list := List_Tail(list);
  }

  Lemma_BSTInOrderOrdering(tree);
  sortedList := BST_InOrder(tree);

  return sortedList;
}
