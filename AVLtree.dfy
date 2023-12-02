datatype AVLnode = Leaf  |  Node (leftNode: AVLnode, height: nat, number: int, rightNode: AVLnode)

/* Ensure the AVL tree is a binary search tree */
predicate BST(leftTree:AVLnode, number:int, rightTree:AVLnode)
{
    var leftNumbers := get_numbers(leftTree);
    var rightNumbers := get_numbers(rightTree);
    (forall i: int :: i in leftNumbers ==> i < number) && 
    (forall j: int :: j in rightNumbers ==> number < j)
}

/* Function that returns the numbers in an AVL tree in order */
function get_numbers(currNode:AVLnode): set<int>
decreases currNode
{
    if currNode == Leaf then
        {}
    else
        get_numbers(currNode.leftNode) + get_numbers(currNode.rightNode) + {currNode.number}
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