include "../../src/Sorted.dfy"
include "../data-types/binary-tree/BinaryTree.dfy"

method TreeSort(L:List<int>) returns (sorted:List<int>)
  requires List_Size(L) > 0 // verificar si puedo sacarlo
  // agregar un predicado ensures que diga cuando el tree está ordenado
{
  var N := List_Size(L);
  var list := L; // averiguar si es referencia o valor
  var tree: BinaryTree<int> := Leaf;

  while list != List_Empty
    decreases list
  {
    var head: int := List_Head(list);
    tree := BinaryTree_Insert(tree, head);
    list := List_Tail(list);
  }

  sorted := BinaryTree_InOrderElems(tree);

  return sorted;
}

// predicado que toma un tree y diga cuando un arbol está ordenado
