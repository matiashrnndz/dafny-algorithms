include "./BST.dfy"

// ------------------------------------ Function Methods ---------------------------------------- //

/** Properties:
 *
 *  Lemma_TreeSortIntegrity
 *    ==> ensures List_ToMultiset(TreeSort(list)) == List_ToMultiset(list)
 *
 *  Lemma_TreeSortOrdering(list)
 *    ==> ensures list_increasing(TreeSort(list))
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
      { Lemma_BSTInOrderIntegrity(BST_Load(list)); }
      { Lemma_BSTLoadIntegrity(list); }
    List_ToMultiset(list);
  }
}

lemma Lemma_TreeSortOrdering(list:List<T>)
  ensures list_increasing(TreeSort(list))
{
  calc == {
    list_increasing(TreeSort(list));
      { Lemma_BSTLoadOrdering(list); }
      { Lemma_BSTInOrderOrdering(BST_Load(list)); }
    true;
  }
}
