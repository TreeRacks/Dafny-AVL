
datatype AVLnode = Null | Node(leftNode: AVLnode, rightNode: AVLnode, height: nat, number: int)

// Ensure the AVL tree is a binary search tree
predicate BST(leftTree:AVLnode, number:int, rightTree:AVLnode, allNodes: set<AVLnode>)
{
    var leftNumbers := get_numbers(leftTree);
    var rightNumbers := get_numbers(rightTree);
    (forall i: int :: i in leftNumbers ==> i < number) && 
    (forall j: int :: j in rightNumbers ==> number < j) &&
    (leftTree == Null || (leftTree in allNodes)) &&
    (rightTree == Null || (rightTree in allNodes))
}

// Verifies that the root number is in the AVLtree
predicate check_root(root: AVLnode)
{
    if(root == Null)
    then
        true
    else
        root.number in get_numbers(root)
}

// Function that returns the numbers in an AVL tree in order
function get_numbers(currNode:AVLnode) : set<int>
decreases currNode
{
    if currNode == Null
    then
        {}
    else
        get_numbers(currNode.leftNode) + get_numbers(currNode.rightNode) + {currNode.number}
}

// Function that returns all the nodes in an AVL tree in order
function get_nodes(currNode:AVLnode) : set<AVLnode>
decreases currNode
{
    if currNode == Null
    then
        {}
    else
        get_nodes(currNode.leftNode) + get_nodes(currNode.rightNode) + {currNode}
}

// Gets the height of a node
function get_node_height(node:AVLnode) : nat
{
    if(node == Null)
    then
        0
    else
        node.height
}

// Gets the maxium of 2 integers
function max (x:int, y:int) : int
{
    if x >= y
    then 
        x
    else
        y
}

// Searches an AVL tree and checks if a number is present within it
function search(findNumber: int, root: AVLnode) : (results: bool)
    requires isValidAndBalanced(root)
    //Making sure the number that you are searching is in the AVL tree then make sure post condition result equals to the number
    ensures (findNumber in get_numbers(root)) == results
    decreases root
{
    if(root == Null) then //empty
        false
    else 
        if (findNumber < root.number) then
            search(findNumber, root.leftNode)
        else if (findNumber > root.number) then
            search(findNumber, root.rightNode)
        else //found number in node
            true
}


// Verifies that the AVL tree is balanced and the balance factor of any node is never greater than 1 or less than -1
function check_balance(node:AVLnode) : bool
requires node != Null
{
  var balance_factor := get_node_height(node.leftNode) - get_node_height(node.rightNode);
  if -1 <= balance_factor <=1 
  then
    true
  else 
    false
}

// Verifies that the height of the root of the tree is correct
function verify_height(root: AVLnode) : bool
requires root != Null
{
    var root_height := get_node_height(root);
    var computed_height := 1 + max(get_node_height(root.rightNode), get_node_height(root.leftNode));
    root_height == computed_height
}

// Ensures the AVL tree is correct
predicate isValidAndBalanced (root: AVLnode)
ensures check_root(root)
decreases root
{
    if(root == Null)
    then
        true
    else
        isValidAndBalanced(root.leftNode) &&
        isValidAndBalanced(root.rightNode) && 
        check_balance(root) &&
        verify_height(root) && 
        BST(root.leftNode, root.number, root.rightNode, get_nodes(root))
}

predicate setOfNumbersIsValid(leftTree: AVLnode, newNum: int, rightTree: AVLnode, combinedTree: AVLnode)
{
    get_numbers(leftTree) + get_numbers(rightTree) + {newNum} == get_numbers(combinedTree)
}

// Creates a new tree given 2 valid AVL trees and a new number
function createAVLTree(leftTree: AVLnode, newNum: int, rightTree: AVLnode) : (result:AVLnode)
requires isValidAndBalanced(leftTree)
requires isValidAndBalanced(rightTree)
requires -1 <= get_node_height(leftTree) - get_node_height(rightTree) <= 1
requires BST(leftTree, newNum, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
ensures setOfNumbersIsValid(leftTree, newNum, rightTree, result)
{
    Node(leftTree, rightTree, 1 + max (get_node_height(leftTree), get_node_height(rightTree)), newNum)
}

// Does a right right rotation on a given node
function rotateRight(leftTree: AVLnode, numberToRotate: int, rightTree: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(leftTree)
requires isValidAndBalanced(rightTree)
requires get_node_height(leftTree) == get_node_height(rightTree) + 2
requires get_node_height(leftTree.leftNode) >= get_node_height(leftTree.rightNode)
requires BST(leftTree, numberToRotate, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
requires isValidAndBalanced(leftTree.rightNode)
requires isValidAndBalanced(leftTree.leftNode)
requires verify_height(leftTree.leftNode)
ensures verify_height(leftTree.leftNode)
ensures isValidAndBalanced(result)
ensures setOfNumbersIsValid(leftTree, numberToRotate, rightTree, result)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) <= get_node_height(result)
ensures get_node_height(result) <= max(get_node_height(leftTree), get_node_height(rightTree)) + 1
{
    createAVLTree(leftTree.leftNode, leftTree.number, createAVLTree(leftTree.rightNode, numberToRotate, rightTree))
}

// Does a right left rotation on a given node
function rotateRightThenLeft(leftTree: AVLnode, numberToRotate: int, rightTree: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(leftTree)
requires isValidAndBalanced(rightTree)
requires get_node_height(leftTree) == get_node_height(rightTree) + 2
requires BST(leftTree, numberToRotate, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
requires isValidAndBalanced(leftTree.rightNode)
requires isValidAndBalanced(leftTree.leftNode)
requires get_node_height(leftTree.leftNode) < get_node_height(leftTree.rightNode)
requires verify_height(leftTree.rightNode)
ensures verify_height(leftTree.rightNode)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) <= get_node_height(result)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) + 1 > get_node_height(result)
ensures isValidAndBalanced(result)
ensures setOfNumbersIsValid(leftTree, numberToRotate, rightTree, result)
{
    createAVLTree(createAVLTree(leftTree.leftNode, leftTree.number, leftTree.rightNode.leftNode),
                 leftTree.rightNode.number, createAVLTree(leftTree.rightNode.rightNode, numberToRotate, rightTree))
}

// Does a left left rotation on a given node
function rotateLeft(leftTree: AVLnode, numberToRotate: int, rightTree: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(leftTree)
requires isValidAndBalanced(rightTree)
requires get_node_height(rightTree) == get_node_height(leftTree) + 2
requires get_node_height(rightTree.rightNode) >= get_node_height(rightTree.leftNode)
requires BST(leftTree, numberToRotate, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
requires isValidAndBalanced(rightTree.rightNode)
requires isValidAndBalanced(rightTree.leftNode)
requires verify_height(rightTree.rightNode)
ensures verify_height(rightTree.rightNode)
ensures isValidAndBalanced(result)
ensures setOfNumbersIsValid(leftTree, numberToRotate, rightTree, result)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) <= get_node_height(result)
ensures get_node_height(result) <= max(get_node_height(leftTree), get_node_height(rightTree)) + 1
{
    createAVLTree(createAVLTree(leftTree, numberToRotate, rightTree.leftNode), rightTree.number, rightTree.rightNode)
}

// Does a left Right rotation on a given node
function rotateLeftThenRight(leftTree: AVLnode, numberToRotate: int, rightTree: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(leftTree)
requires isValidAndBalanced(rightTree)
requires get_node_height(rightTree) == get_node_height(leftTree) + 2
requires BST(leftTree, numberToRotate, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
requires isValidAndBalanced(rightTree.rightNode)
requires isValidAndBalanced(rightTree.leftNode)
requires get_node_height(rightTree.rightNode) < get_node_height(rightTree.leftNode)
requires verify_height(rightTree.leftNode)
ensures verify_height(rightTree.leftNode)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) <= get_node_height(result)
ensures max(get_node_height(leftTree), get_node_height(rightTree)) + 1 > get_node_height(result)
ensures isValidAndBalanced(result)
ensures setOfNumbersIsValid(leftTree, numberToRotate, rightTree, result)
{
    createAVLTree(createAVLTree(leftTree, numberToRotate, rightTree.leftNode.leftNode),
                 rightTree.leftNode.number, createAVLTree(rightTree.leftNode.rightNode, rightTree.number, rightTree.rightNode))
}

// This function rebalances the given AVL tree
function rebalance(leftTree: AVLnode, numberToRotate: int, rightTree: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(rightTree)
requires isValidAndBalanced(leftTree)
requires -2 <= (get_node_height(leftTree)-get_node_height(rightTree)) <= 2
requires BST(leftTree, numberToRotate, rightTree, get_nodes(leftTree) + get_nodes(rightTree))
ensures setOfNumbersIsValid(leftTree, numberToRotate, rightTree, result)
ensures isValidAndBalanced(rebalance(leftTree, numberToRotate, rightTree))
ensures get_node_height(rebalance(leftTree, numberToRotate, rightTree)) <= max(get_node_height(leftTree), get_node_height(rightTree)) + 1	
ensures max(get_node_height(leftTree), get_node_height(rightTree)) <= get_node_height(rebalance(leftTree, numberToRotate, rightTree))  	
{    
   if -1 <= (get_node_height(leftTree)-get_node_height(rightTree)) <= 1 
   then
        createAVLTree(leftTree, numberToRotate, rightTree)
   else
        if get_node_height(leftTree) == get_node_height(rightTree) + 2 
        then
            if get_node_height(leftTree.leftNode) >= get_node_height(leftTree.rightNode)
            then
                rotateRight(leftTree, numberToRotate, rightTree)
            else
                rotateRightThenLeft(leftTree, numberToRotate, rightTree)
        else
            if get_node_height(rightTree.rightNode) >= get_node_height(rightTree.leftNode)
            then
                rotateLeft(leftTree, numberToRotate, rightTree)
            else
                rotateLeftThenRight(leftTree, numberToRotate, rightTree)
}

// This function inserts a new node into an AVL tree
function insert(number: int, root: AVLnode) : (result: AVLnode)
requires isValidAndBalanced(root)
ensures isValidAndBalanced(result)
ensures get_numbers(result) == (get_numbers(root) + {number})
ensures 0 <= (get_node_height(result) - get_node_height(root)) <= 1
decreases root
{
    if(root == Null)
    then
        createAVLTree(Null, number, Null)
    else 
        if (number > root.number)
        then
            rebalance(root.leftNode, root.number, insert(number, root.rightNode))
        else if (number < root.number)
        then
            rebalance(insert(number, root.leftNode), root.number, root.rightNode)
        else 
            root
}

datatype deletedNodePair = deletedNodePair(deletedNumber:int, newRoot:AVLnode)

// Finds the minimum number in an AVL tree and deletes it, returns the number and the new tree
function deleteMostLeftChild(root: AVLnode) : (result: deletedNodePair)
decreases root
requires root != Null
requires isValidAndBalanced(root)
ensures result.deletedNumber in get_numbers(root)
ensures get_numbers(root) - {result.deletedNumber} == get_numbers(result.newRoot)
ensures 0 <= get_node_height(root) - get_node_height(result.newRoot) <= 1
ensures forall i: int | i in get_numbers(root) :: result.deletedNumber <= i
{
    if(root.leftNode == Null )
    then
        deletedNodePair(root.number, root.rightNode)
    else
        var deletionResult := deleteMostLeftChild(root.leftNode);
        deletedNodePair(deletionResult.deletedNumber, rebalance(deletionResult.newRoot, root.number, root.rightNode))
}

// Deletes a specific number from an AVL tree
function delete(number: int, root: AVLnode) : (result: AVLnode)
decreases root
requires isValidAndBalanced(root)
ensures isValidAndBalanced(result)                                                
ensures 0 <= get_node_height(root) - get_node_height(result) <= 1              
ensures get_numbers(result) == get_numbers(root) - {number}			 
{
    if (root == Null)
    then
        root
    else
        if (number > root.number)
        then
            rebalance(root.leftNode, root.number, delete(number, root.rightNode))
        else if (number < root.number)
        then
            rebalance(delete(number,root.leftNode), root.number, root.rightNode)
        else
            if(root.rightNode != Null)
            then
                var deletionResult := deleteMostLeftChild(root.rightNode);
                rebalance(root.leftNode, deletionResult.deletedNumber, deletionResult.newRoot)
            else
                root.leftNode
}