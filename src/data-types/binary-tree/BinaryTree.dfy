include "../list/List.dfy"

datatype Leaf = Nil
datatype BinaryTree<T> = Leaf | Node(left:BinaryTree<T>, data:T, right:BinaryTree<T>)

function method BinaryTree_InOrderElems(tree:BinaryTree<T>) : List<T>
  decreases tree
{
  match tree {
    case Leaf => List_Empty
    case Node(l, d, r) => List_Concat(BinaryTree_InOrderElems(l), List_Concat(Cons(d, List_Empty), BinaryTree_InOrderElems(r)))
  }
}

function method BinaryTree_Insert(tree:BinaryTree<T>, x:int): BinaryTree<T>
  decreases tree
{
  match tree {
    case Leaf => Node(Leaf, x, Leaf)
    case Node(l, d, r) => 
      if (x < d) then Node(BinaryTree_Insert(l, x), d, r)
      else if (x > d) then Node(l, d, BinaryTree_Insert(r, x))
      else tree
  }
}

function method BinaryTree_Mirror(tree:BinaryTree<T>): BinaryTree<T>
  decreases tree
{
  match tree {
    case Leaf => Leaf
    case Node(l, d, r) => Node(BinaryTree_Mirror(r), d, BinaryTree_Mirror(l))
  }
}