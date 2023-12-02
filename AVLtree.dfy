
datatype AVLnode = Leaf  |  Node(leftNode: AVLnode, rightNode: AVLnode, height: nat, number: int)

/* Ensure the AVL tree is a binary search tree */
predicate BST(leftTree:AVLnode, number:int, rightTree:AVLnode, repr: set<AVLnode>)
{
    var leftNumbers := get_numbers(leftTree);
    var rightNumbers := get_numbers(rightTree);
    (forall i: int :: i in leftNumbers ==> i < number) && 
    (forall j: int :: j in rightNumbers ==> number < j) &&
    (leftTree == Leaf || (leftTree in repr && BST(leftTree.leftNode, leftTree.number, leftTree.rightNode, repr))) &&
    (rightTree == Leaf || (rightTree in repr))
}

/* Function that returns the numbers in an AVL tree in order */
function get_numbers(currNode:AVLnode): set<int>
decreases currNode
{
    if currNode == Leaf
    then
        {}
    else
        get_numbers(currNode.leftNode) + get_numbers(currNode.rightNode) + {currNode.number}
}

/* Function that returns all the nodes in an AVL tree in order */
function get_nodes(currNode:AVLnode): set<AVLnode>
decreases currNode
{
    if currNode == Leaf
    then
        {}
    else
        get_nodes(currNode.leftNode) + get_nodes(currNode.rightNode) + {currNode}
}

function get_node_height(node:AVLnode): nat
{
    if(node == Leaf)
    then
        0
    else
        node.height
}

function max (x:int, y:int): int
{
    if x >= y
    then 
        x
    else
        y
}

function check_balance(node:AVLnode): bool
requires node != Leaf
{
  var balance_factor := get_node_height(node.leftNode) - get_node_height(node.rightNode);
  if -1 <= balance_factor <=1 
  then
    true
  else 
    false
}

/* Ensures the AVL tree is correct */
predicate isAVL (root: AVLnode)
ensures   root.Node? ==> root.number in get_numbers(root);
decreases root
{
    if(root == Leaf)
    then
        true
    else
        get_node_height(root) == 1 + max(get_node_height(root.rightNode), get_node_height(root.leftNode)) && 
        isAVL(root.leftNode) &&
        isAVL(root.rightNode) && 
        BST(root.leftNode, root.number, root.rightNode, get_nodes(root)) &&
        check_balance(root)
}