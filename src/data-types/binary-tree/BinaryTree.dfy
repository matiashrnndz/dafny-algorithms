type T = int

datatype BinaryTree<T> = Leaf(data:T) | Node(left:BinaryTree<T>, data:T, right:BinaryTree<T>)

function elems(tree: BinaryTree<T>): set<T>
    decreases tree
{
    match tree
        case Leaf => {}
        case Node(left, data, right) => elems(left) + {data} + elems(right)
}

function descendants(tree: BinaryTree<T>) : set<BinaryTree<T>>
    decreases tree
{
    match tree {
        case Leaf => {}
        case Node(left, _, right) => descendants(left) + descendants(right)
    }
}