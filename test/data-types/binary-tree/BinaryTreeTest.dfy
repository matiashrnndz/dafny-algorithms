include "../../../src/data-types/binary-tree/BST.dfy"

method Main() {
  InOrderTest();
  InsertTest();
  InsertWorstCaseTest();
  MirrorTest();
}

method InOrderTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var list := BST_InOrder(tree);
  var expected := Cons(1, Cons(3, Cons(4, Cons(5, Cons(7, List_Empty)))));
  assert(list == expected);
}

method InsertTest() {
  var tree: BST<int> := Leaf;
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 7);
  tree := BST_Insert(tree, 5);
  var expected := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  assert(tree == expected);
}

method InsertWorstCaseTest() {
  var tree := BST_Init();
  tree := BST_Insert(tree, 1);
  tree := BST_Insert(tree, 3);
  tree := BST_Insert(tree, 4);
  tree := BST_Insert(tree, 5);
  tree := BST_Insert(tree, 7);
  var expected := Node(Leaf, 1, Node(Leaf, 3, Node(Leaf, 4, Node(Leaf, 5, Node(Leaf, 7, Leaf)))));
  assert(tree == expected);
}

method MirrorTest() {
  var tree: BST<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var mirroredTree := BST_Mirror(tree);
  var expected := Node(Node(Leaf, 7, Node(Leaf, 5, Leaf)), 4, Node(Leaf, 3, Node(Leaf, 1, Leaf)));
  assert(mirroredTree == expected);
}
