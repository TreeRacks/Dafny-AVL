class AVLnode {
    //Height of the subtree
    var height: nat
    var number: int
    var left: AVLnode?
    var right: AVLnode?

    constructor Create(x: int)
    {
        height := 0;
        number := x;
        right := null;
        left := null;
    }
}