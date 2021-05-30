include "../../src/functional/BST.dfy"

method Main() {
  InitTest();
  SizeTest();
  InsertTest();
  InOrderTest();
  InsertWorstCaseTest();
  ToMultisetTest();
  ContainsTest();
  NotContainsTest();
  MirrorTest();
}

method InitTest() {
  var tree: BST<int> := BST_Init();
  var expected := Leaf;
  assert bst_is_ordered(tree);
  assert tree == expected;
}

method SizeTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var size: int := BST_Size(tree);
  var expected: int := 5;
  assert size == expected;
}

method InOrderTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var list := BST_InOrder(tree);
  var expected := Cons(1, Cons(3, Cons(4, Cons(5, Cons(7, List_Empty)))));
  assert list == expected;
}

method InsertTest() {
  var tree: BST<int> := BST_Init();
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 7);
  tree := BST_Insert(tree, 5);
  var expected := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  assert tree == expected;
}

method InsertWorstCaseTest() {
  var tree := BST_Init();
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 5);
  tree := BST_Insert(tree, 7);
  var expected := Node(Leaf, 1, Node(Leaf, 3, Node(Leaf, 4, Node(Leaf, 5, Node(Leaf, 7, Leaf)))));
  assert tree == expected;
}

method ToMultisetTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var bstMultiset: multiset<int> := BST_ToMultiset(tree);
  var expected: multiset<int> := multiset{1, 3, 4, 5, 7};
  assert bstMultiset == expected;
}

method ContainsTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var contains: bool := BST_Contains(tree, 3);
  var expected: bool := true;
  assert contains == contains;
}

method NotContainsTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var notContains: bool := BST_Contains(tree, 9);
  var expected: bool := false;
  assert notContains == expected;
}

method MirrorTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var mirroredTree := BST_Mirror(tree);
  var expected := Node(Node(Leaf, 7, Node(Leaf, 5, Leaf)), 4, Node(Leaf, 3, Node(Leaf, 1, Leaf)));
  assert mirroredTree == expected;
}
