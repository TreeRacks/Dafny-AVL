include "AVLnode.dfy"

class AVLtree{

    var root: AVLnode?;

    /* Ensure the AVL tree is a binary search tree */
    predicate BST(l:AVLnode, x:int, r:AVLnode) 
    reads l
    reads r
    {
        (forall z :: z in get_numbers(l) ==> z < x) && 
        (forall z :: z in get_numbers(r) ==> x < z)
    }

    /* Function that returns the numbers in an AVL tree in order */
    function get_numbers(t:AVLnode?): set<int>
    decreases t
    reads t
    {
        if t == null then
            {}
        else
            get_numbers(t.left) + {t.number} + get_numbers(t.right)
    }

    function get_node_height(node:AVLnode?): nat
    reads node
    {
        if(node == null) then
             0
         else
            node.height
    }

    function method max (x:int, y:int): int
    {
        if x >= y then 
            x
        else
            y
    }		
}