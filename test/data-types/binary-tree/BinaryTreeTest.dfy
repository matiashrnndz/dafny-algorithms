include "../../../src/data-types/binary-tree/BinaryTree.dfy"

method Main() {
  InOrderElemsTest();
  InsertTest();
  InsertWorstCaseTest();
  MirrorTest();
}

method InOrderElemsTest() {
  var tree: BinaryTree<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var list := BinaryTree_InOrderElems(tree);
  var expected := Cons(1, Cons(3, Cons(4, Cons(5, Cons(7, List_Empty)))));
  assert(list == expected);
}

method InsertTest() {
  var tree: BinaryTree<int> := Leaf;
  tree := BinaryTree_Insert(tree, 4);
  tree := BinaryTree_Insert(tree, 3);
  tree := BinaryTree_Insert(tree, 1);
  tree := BinaryTree_Insert(tree, 7);
  tree := BinaryTree_Insert(tree, 5);
  var expected := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  assert(tree == expected);
}

method InsertWorstCaseTest() {
  var tree: BinaryTree<int> := Leaf;
  tree := BinaryTree_Insert(tree, 1);
  tree := BinaryTree_Insert(tree, 3);
  tree := BinaryTree_Insert(tree, 4);
  tree := BinaryTree_Insert(tree, 5);
  tree := BinaryTree_Insert(tree, 7);
  var expected := Node(Leaf, 1, Node(Leaf, 3, Node(Leaf, 4, Node(Leaf, 5, Node(Leaf, 7, Leaf)))));
  assert(tree == expected);
}

method MirrorTest() {
  var tree: BinaryTree<int> := Node(Node(Node(Leaf,1,Leaf),3,Leaf),4,Node(Node(Leaf, 5, Leaf),7,Leaf));
  var mirroredTree := BinaryTree_Mirror(tree);
  var expected := Node(Node(Leaf, 7, Node(Leaf, 5, Leaf)), 4, Node(Leaf, 3, Node(Leaf, 1, Leaf)));
  assert(mirroredTree == expected);
}
