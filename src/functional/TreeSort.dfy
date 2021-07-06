include "./BST.dfy"

/** Properties:
 *
 *  Lemma_TreeSortListIsOrdered(list)
 *    ==> ensures list_is_ordered(TreeSort(list))
 *
 *  Lemma_TreeSortSameElemsThanList
 *    ==> ensures List_ToMultiset(TreeSort(list)) == List_ToMultiset(list)
 *
 */
function method TreeSort(list:List<int>) : (sortedList:List<int>)
  decreases list
{
  BST_InOrder(BST_Load(list))
}

lemma {:induction list} Lemma_TreeSortListIsOrdered(list:List<T>)
  ensures list_is_ordered(TreeSort(list))
{
  calc == {
    list_is_ordered(TreeSort(list));
      { assert TreeSort(list) == BST_InOrder(BST_Load(list)); }
    list_is_ordered(BST_InOrder(BST_Load(list)));
      { Lemma_BSTLoadIsOrdered(list); }
      { assert bst_is_ordered(BST_Load(list)); }
      { Lemma_BSTOrderedThenInOrderOrdered(BST_Load(list)); }
    true;
  }
}

lemma {:induction list} Lemma_TreeSortSameElemsThanList(list:List<T>)
  ensures List_ToMultiset(TreeSort(list)) == List_ToMultiset(list)
{
  calc == {
    List_ToMultiset(TreeSort(list));
      { assert TreeSort(list) == BST_InOrder(BST_Load(list)); }
    List_ToMultiset(BST_InOrder(BST_Load(list)));
      { Lemma_BSTLoadIsOrdered(list); }
      { assert bst_is_ordered(BST_Load(list)); }
      { Lemma_BSTSameElementsThanInOrder(BST_Load(list)); }
    BST_ToMultiset(BST_Load(list));
      { Lemma_BSTLoadTreeElemsSameThanList(list); }
    List_ToMultiset(list);
  }
}