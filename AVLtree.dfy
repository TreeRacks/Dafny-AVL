
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

/* Verifies that the root number is in the AVLtree */
predicate check_root(root: AVLnode)
{
    if(root == Leaf)
        then
            true
        else
            root.number in get_numbers(root)
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

/* Verifies that the AVL tree is balanced and the balance factor of any node is never greater than 1 or less than -1 */
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

/* Verifies that the height of the root of the tree is correct */
function verify_height(root: AVLnode): bool
requires root != Leaf
{
    var root_height := get_node_height(root);
    var computed_height := 1 + max(get_node_height(root.rightNode), get_node_height(root.leftNode));
    root_height == computed_height
}

/* Ensures the AVL tree is correct */
predicate isValidAndBalanced (root: AVLnode)
ensures check_root(root)
decreases root
{
    if(root == Leaf)
    then
        true
    else
        isValidAndBalanced(root.leftNode) &&
        isValidAndBalanced(root.rightNode) && 
        check_balance(root) &&
        verify_height(root) && 
        BST(root.leftNode, root.number, root.rightNode, get_nodes(root))
}