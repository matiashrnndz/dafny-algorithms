include "../../src/functional/BST.dfy"

method Main() {
  Test_Size();
  Test_Insert();
  Test_InOrder();
  Test_InsertWorstCase();
  Test_ToMultiset();
}

method Test_Size() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var size: int := BST_Size(tree);
  var expected: int := 5;
  assert size == expected;
}

method Test_InOrder() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var list := BST_InOrder(tree);
  var expected := Cons(1, Cons(3, Cons(4, Cons(5, Cons(7, List_Empty)))));
  assert list == expected;
}

method Test_Insert() {
  var tree: BST<int> := Leaf;
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 7);
  tree := BST_Insert(tree, 5);
  var expected := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  assert tree == expected;
}

method Test_InsertWorstCase() {
  var tree := Leaf;
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 5);
  tree := BST_Insert(tree, 7);
  var expected := Node(Leaf, 1, Node(Leaf, 3, Node(Leaf, 4, Node(Leaf, 5, Node(Leaf, 7, Leaf)))));
  assert tree == expected;
}

method Test_ToMultiset() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var bstMultiset: multiset<int> := BST_ToMultiset(tree);
  var expected: multiset<int> := multiset{1, 3, 4, 5, 7};
  assert bstMultiset == expected;
}
