include "./BST.dfy"

// ------------------------------------ Function Methods ---------------------------------------- //

/** Properties:
 *
 *  Lemma_TreeSortIntegrity
 *    ==> ensures List_ToMultiset(TreeSort(list)) == List_ToMultiset(list)
 *
 *  Lemma_TreeSortOrdering(list)
 *    ==> ensures list_ordered(TreeSort(list))
 *
 */
function method TreeSort(list:List<int>) : (sortedList:List<int>)
  decreases list
{
  BST_InOrder(BST_Load(list))
}

// ------------------------------------- TreeSort Lemmas ---------------------------------------- //

lemma Lemma_TreeSortIntegrity(list:List<T>)
  ensures List_ToMultiset(TreeSort(list)) == List_ToMultiset(list)
{
  calc == {
    List_ToMultiset(TreeSort(list));
      { assert TreeSort(list) == BST_InOrder(BST_Load(list)); }
    List_ToMultiset(BST_InOrder(BST_Load(list)));
      { Lemma_BSTInOrderIntegrity(BST_Load(list)); }
    BST_ToMultiset(BST_Load(list));
      { Lemma_BSTLoadIntegrity(list); }
    List_ToMultiset(list);
  }
}

lemma Lemma_TreeSortOrdering(list:List<T>)
  ensures list_ordered(TreeSort(list))
{
  calc == {
    list_ordered(TreeSort(list));
      { assert TreeSort(list) == BST_InOrder(BST_Load(list)); }
    list_ordered(BST_InOrder(BST_Load(list)));
      { Lemma_BSTLoadOrdering(list); }
      { assert bst_ordered(BST_Load(list)); }
      { Lemma_BSTInOrderOrdering(BST_Load(list)); }
    true;
  }
}
