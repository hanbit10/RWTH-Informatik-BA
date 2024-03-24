/**
  *   Verify binary search tree and also
  *   Translate the code as possible to verify in Caesar.
  *   Create a new List with all the needed definitions in Dafny,
  **/
datatype Tree = Null | Node(left: Tree, value: int, right: Tree)

/**
  *   Ensure Tree t contains the value val
  *
  *   @param  t:    a tree
  *   @param  val:  Lower bound of the array
  *   @returns a boolean if Tree t contains the element val 
  *
  **/
function contains(t: Tree, val: int) : bool
  ensures t == Null ==> contains(t, val) == false
  decreases t
{
  if(t.Null?) then false
  else if (t.Node?) then
    var l : Tree := t.left;
    var v : int := t.value;
    var r : Tree := t.right;
    if (val < v) then contains(l, val)
    else if (val > v) then contains(r, val)
    else  true
  else true
}

/**
  *   Ensure Tree t is a binary search tree
  *
  *   @param    t:  a tree
  *   @returns  a boolean if Tree t is a binary search tree
  *
  **/
ghost function BST (t: Tree) : bool
{
  if(t.Null?) then true
  else if (t.Node?) then
    var l : Tree := t.left;
    var v : int := t.value;
    var r : Tree := t.right;
    (forall z:: contains(l, z) ==> z < v) &&
    (forall z:: contains(r, z) ==> v < z) && BST(l) && BST(r)
  else true
}

/**
  *   Insert function
  *
  *   @param    t:    a binary search tree
  *   @param    val:  the value to Insert in the tree t
  *   @returns  res:  a tree with containing value val
  *
  **/
method Insert(t: Tree, val: int) returns (res:Tree)
  requires BST(t)
  ensures forall x: int:: contains(t, x) && x < val ==> contains(res, x)
  ensures forall x: int:: contains(t, x) && x > val ==> contains(res, x)
  ensures  forall v: int :: contains(res, v) == contains(t,v) || v == val
  ensures BST(res)
  decreases t
{
  if (t.Null?) {
    res :=  Node(Null, val, Null);
  } else if(t.Node?) {
    var l : Tree := t.left;
    var v : int := t.value;
    var r : Tree := t.right;
    if (val < v) {
      var temp := Insert(l, val);
      res := (Node(temp, v, r));
    } else if (val > v) {
      var temp := Insert(r, val);
      res := (Node(l, v, temp));
    } else {
      res := t;
    }
  }
}

/**
  *   Get minmum value of the tree
  *
  *   @param    t:     a binary search tree
  *   @returns  minV:  the minimum value of the tree
  *
  **/
function getMin(t: Tree) : int
  requires BST(t)
  requires t != Null
  ensures contains(t, getMin(t))
  ensures forall v: int :: (contains(t, v) && v != getMin(t)) ==> getMin(t) < v
  decreases t
{
  if(t.Node?) then
    var l : Tree := t.left;
    var v : int := t.value;
    var r : Tree := t.right;
    if (l != Null) then getMin(l)
    else v
  else 0
}

/**
  *   Delete function
  *
  *   @param    t:    a bianry search tree
  *   @param    val:  the value to Delete in the tree t
  *   @returns  res:  a tree without containing value val
  *
  **/
method Delete(t: Tree, val: int) returns (res: Tree)
  requires BST(t)
  ensures forall x: int:: contains(t, x) && x < val ==> contains(res, x)
  ensures forall x: int:: contains(t, x) && x > val ==> contains(res, x)
  ensures  forall v: int :: contains(res, v) == (contains(t,v) && (v != val))
  ensures BST(res)
  decreases t
{
  if (t.Null?) {
    res := t;
  } else if (t.Node?) {
    var l : Tree := t.left;
    var v : int := t.value;
    var r : Tree := t.right;
    if (val < v) {
      var ll := Delete(l, val);
      res := Node(ll, v, r);
    } else if (val > v) {
      var rr := Delete(r, val);
      res := Node(l, v, rr);
    } else if (val == v) {
      if (l == Null && r == Null) {res := Null;}
      else if (l == Null) {res := r;}
      else if (r == Null) {res := l;}
      else {
        var minV := getMin(r);
        var rm := Delete(r, minV);
        res := Node(l, minV, rm);
      }

    }
  }
}

method Main () {

  var t := Node(Node(Null, 2, Null), 4, Node(Null, 5,Null));
  assert BST(t);
  var t2 := Node(Node(Null, 5, Null), 4,  Node(Null, 8, Null));
  //assert BST(t2);
  var t3 := Insert(t, 4);
  t3 := Insert(t3, 7);
  t3 := Insert(t3, 7);
  t3 := Insert(t3, 6);

  t3 := Delete(t3, 4);
  t3 := Delete(t3, 4);
  assert BST(t3);
}