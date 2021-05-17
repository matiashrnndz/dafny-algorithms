include "../list/List.dfy"

datatype Leaf = Nil
datatype BinaryTree<T> = Leaf | Node(left:BinaryTree<T>, data:T, right:BinaryTree<T>)

// ---------------------- Function Methods ---------------------- //

function method BinaryTree_InOrderElems(tree:BinaryTree<T>) : (result:List<T>)
  decreases tree
  requires binarytree_ordered(tree)
  // Mismos elementos el tree que el result
  // Result esté ordenado
{
  match tree {
    case Leaf => List_Empty
    case Node(l, d, r) => List_Concat(BinaryTree_InOrderElems(l), List_Concat(Cons(d, List_Empty), BinaryTree_InOrderElems(r)))
  }
}

function method BinaryTree_Elems(tree:BinaryTree<T>): seq<T>
  decreases tree
{
  match tree {
    case Leaf => []
    case Node(l, d, r) => BinaryTree_Elems(l) + [d] + BinaryTree_Elems(r)
  }
}

function method BinaryTree_Insert(tree:BinaryTree<T>, x:T): (result:BinaryTree<T>)
  decreases tree
  requires binarytree_ordered(tree)
  ensures binarytree_ordered(result)
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

// ---------------------- Predicates ---------------------- //

predicate binarytree_ordered(tree:BinaryTree<T>) 
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(l, d, r) => 
      binarytree_value_is_greater_than_root(l, d) &&
      binarytree_value_is_lesser_than_root(r, d) &&
      binarytree_ordered(l) &&
      binarytree_ordered(r)
  }
}

predicate binarytree_value_is_greater_than_root(tree:BinaryTree<T>, value:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(l, root, r) => value > root
  }
}

predicate binarytree_value_is_lesser_than_root(tree:BinaryTree<T>, value:T)
  decreases tree
{
  match tree {
    case Leaf => true
    case Node(l, root, r) => value < root
  }
}

// ------------------------ Lemmas ------------------------ //
