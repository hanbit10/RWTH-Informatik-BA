/**
  *   Verify Binary Search Tree and also
  *   Translate the code as possible to verify in Caesar.
  *   Create a new List with all the needed definitions in Dafny,
  **/
datatype Tree = Null | Node(left: Tree, value: int, right: Tree)

/**
  *   Set of the tree
  *
  *   @param    t:  A tree
  *   @returns  A set of an integer containing elements of the tree t
  *
  **/
function treeSet(t: Tree): set<int>
{
  if(t.Null?) then {}
  else if(t.Node?) then
    var l:Tree := t.left;
    var v:int := t.value;
    var r:Tree := t.right;
    treeSet(l) + {v} + treeSet(r)
  else {}
}

/**
  *   Ensure Tree t is a Binary Search Tree
  *
  *   @param    t:  A tree
  *
  **/
predicate BST (t: Tree)
{
  if(t.Null?) then
    true
  else if (t.Node?) then
    var l:Tree := t.left;
    var v:int := t.value;
    var r:Tree := t.right;
    (forall z:: z in treeSet(l) ==> z < v) &&
    (forall z:: z in treeSet(r) ==> v < z) && BST(l) && BST(r)
  else true
}

/**
  *   Insert function
  *
  *   @param    t:    A Binary Search Tree
  *   @param    val:  The value to insert in the tree t
  *   @returns  res:  A tree with containing value val
  *
  **/
method Insert(t:Tree, val:int) returns (res:Tree)
  requires BST(t)
  ensures forall x :: x in treeSet(t) && x < val ==> x in treeSet(res)
  ensures forall x :: x in treeSet(t) && x > val ==> x in treeSet(res)
  ensures  treeSet(res) == treeSet(t) + {val}
  ensures  BST(res)
  decreases t
{
  if (t.Null?) {
    res :=  Node(Null, val, Null);
  } else if (t.Node?) {
    var l:Tree := t.left;
    var v:int := t.value;
    var r:Tree := t.right;
    if (val < v) {
      var ll:Tree := Insert(l, val);
      res := (Node(ll, v, r));
    } else if (val > v) {
      var rr:Tree := Insert(r, val);
      res := (Node(l, v, rr));
    } else {
      res := t;
    }
  }
}

/**
  *   Get minmum value of the tree
  *
  *   @param    t:     A Binary Search Tree
  *   @returns  minV:  The minimum value of the tree
  *
  **/
function getMin(t: Tree) : int
  requires BST(t)
  requires t != Null
  ensures  getMin(t) in treeSet(t)
  ensures  forall x:int :: (x in treeSet(t) && x != getMin(t)) ==> getMin(t) < x
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
  *   @param    t:    A bianry search tree
  *   @param    val:  The value to Delete in the tree t
  *   @returns  res:  A tree without containing value val
  *
  **/
method Delete(t:Tree, val:int) returns (res:Tree)
  requires BST(t)
  ensures forall x :: x in treeSet(t) && x < val ==> x in treeSet(res)
  ensures forall x :: x in treeSet(t) && x > val ==> x in treeSet(res)
  ensures  treeSet(res) == treeSet(t) - {val}
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
  var t := Node(Node(Null, 2, Null), 4, Node(Null, 8, Null));
  assert BST(t);
  var t2 := Node(Node(Null, 5, Null), 4, Node(Null, 8, Null));
  //assert BST(t2);

  var t3 := Insert(t, 4);
  t3 := Insert(t3, 6);
  t3 := Delete(t3, 2);
  assert BST(t3);
}