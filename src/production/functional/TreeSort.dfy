include "./BST.dfy"

// ------------------------------------ Function Methods ---------------------------------------- //

/** Funcionalidad:
 *
 * Es un algoritmo de ordenamiento basado en la estructura de datos
 * BST, que recibe como parámetro una lista y luego de haber
 * cargado un BST con sus elementos y haber obtenido una lista
 * in order de dichos elementos, la retorna como resultado.
 *
 */
function method TreeSort(list:List<int>) : (sortedList:List<int>)
  decreases list
{
  BST_InOrder(BST_Load(list))
}

// ------------------------------------- TreeSort Lemmas ---------------------------------------- //

/** Propiedad:
 *
 * Asegura que se mantenga la integridad de los elementos luego de
 * haber sido aplicada la función TreeSort a una lista.
 *
 */
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

/** Propiedad:
 *
 * Asegura que el resultado de haber sido aplicada la función
 * TreeSort a una lista, sea una lista ordenada.
 *
 */
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
