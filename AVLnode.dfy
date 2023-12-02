class AVLnode {
    //Height of the subtree
    var height: nat
    var number: int
    var leftNode: AVLnode?
    var rightNode: AVLnode?

    constructor Create(x: int)
    {
        height := 0;
        number := x;
        rightNode := null;
        leftNode := null;
    }
}