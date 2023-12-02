datatype AVLnode = Leaf  |  Node (leftNode: AVLnode, height: nat, number: int, rightNode: AVLnode)

/* Ensure the AVL tree is a binary search tree */
predicate BST(left:AVLnode, x:int, right:AVLnode) 
{
    (forall i :: i in get_numbers(left) ==> i < x) && 
    (forall j :: j in get_numbers(right) ==> x < j)
}

/* Function that returns the numbers in an AVL tree in order */
function get_numbers(t:AVLnode): set<int>
decreases t
{
    if t == Leaf then
        {}
    else
        get_numbers(t.leftNode) + {t.number} + get_numbers(t.rightNode)
}

function get_node_height(node:AVLnode): nat
{
    if(node == Leaf) then
            0
    else
        node.height
}

function max (x:int, y:int): int
{
    if x >= y then 
        x
    else
        y
}		