/**
  *   Translate the code to verify Left Pad in Caesar.
  *   Create a new List with all the needed definitions in Dafny,
  **/

datatype List	 = Null | Cons(head: int, tail: List)

/**
  *   Get maximal value between x and y
  *
  *   @param  x:  An integer value
  *   @param  y:  An integer value
  *   @returns The maximal value
  *
  **/
function max(x: int, y: int): int
{
  if x < y then y else x
}

/**
  *   Get the Length of the List
  *
  *   @param    ls: A datatype List
  *   @returns  The Length of the List
  *
  **/
function Length(ls: List): nat
  ensures 0 <= Length(ls)
{
  if(ls.Null?) then 0
  else if (ls.Cons?) then
    var t := ls.tail;
    1 + Length(t)
  else 0
}

/**
  *   Get the element of the List in desired index
  *
  *   @param    ls: A datatype List
  *   @param    i:  The desired index
  *   @returns  The element of the List in index i
  *
  **/
function Select(ls: List, i: int): int
  requires i < Length(ls)
  ensures ls == Null ==> Select(ls, i) == 0
  ensures forall h: int, t: List:: ls == Cons(h, t) && (i == 0) ==> Select(ls, i) == h
  ensures forall h: int, t: List:: ls == Cons(h, t) && (i != 0) ==> Select(ls, i) == Select(t, i-1)
{
  if (ls.Cons?) then
    var h := ls.head;
    var t := ls.tail;
    if (i != 0) then Select(t, i-1)
    else h
  else 0
}

/**
  *   Verify the extensionality of two Lists
  *
  *   @param    ls: A datatype List
  *   @param    ts: A datatype List
  *   @returns  The Lists ls == ts by verifying extensionatity
  *
  **/
function Extensionality(ls: List, ts: List) : bool
  requires Length(ls) == Length(ts)
  requires forall k: nat :: k < Length(ls) ==> Select(ls, k) == Select(ts, k)
  ensures ls == ts
{
  if (ls.Null?) then
    //if the List ls is null, it implies that its Length is 0, which also implies the Length of ts must be 0 as well.
    assert true;
    assert Length(ls) == Length(ts);
    assert 0 == Length(ts);
    assert Null == ts;
    assert ls == ts;
    true == (ls == ts)

  else if (ls.Cons? && ts.Cons?) then
    var h := ls.head;
    var t := ls.tail;
    var g := ts.head;
    var u := ts.tail;

    //To begin with, it is necessary to show the first element at index 0 of both Lists ls and ts are identical.
    assert ls == Cons(h, t);
    assert h == Select(ls, 0);
    assert Select(ls, 0) == Select(ts, 0);
    assert Select(ts, 0) == g;
    assert h == g;
    assert Cons(h, t) == Cons(g, t);

    //Then show the for all  k, that the next elment in index k both Lists ls and ts are identical
    assert forall k : nat :: k < Length(t) ==>
                               Select(t, k) == Select(ls, k+1) &&
                               Select(ls, k+1) == Select(ts, k+1) &&
                               Select(ts, k+1) == Select(u, k) &&
                               Select(t, k) == Select(u, k);
    //this asserts the Extensionality for tail of Lists are equal
    assert Extensionality(t, u);
    assert Cons(g, t) == Cons(g, u);
    assert Cons(g, u) == ts;

    //after showing all the elments in ls and ts are same, ls and ts must have identical listed list
    assert ls == ts;
    Extensionality(t, u) &&
    true == (ls == ts)
  else false
}

/**
  *   The method to ensure Left Pad
  *
  *   @param  str:    A datatype List
  *   @param  ln:     The desired Length of the return value
  *   @param  c:      The added pad
  *   @returns  res:  The return List that has correct Left Pad in desired Length
  *   
  *   note:   Instead using the while loop use recursion to add pads on the left
  *           The annotations are analogous as the those used in the sequence
  **/
method LeftPad(str: List, ln: nat, c: int) returns (res: List)
  requires 0 <= Length(str) <= ln
  ensures Length(res) == max(ln, Length(str))
  ensures forall k: nat :: k < ln-Length(str) ==> Select(res, k) == c
  ensures forall k: nat :: max(ln - Length(str), 0) <= k < Length(res) ==> Select(res, k) == Select(str, k-max(ln-Length(str), 0))
  decreases ln - Length(str)
{
  if (ln <= Length(str)){
    res := str;
  }
  else if (Length(str) <= ln) {
    res := LeftPad(Cons(c, str), ln, c);
  }
}

/**
  *   The main method to test the verification of Left Pad
  *   
  **/
method Main () {
  var ls := Cons(0, Cons(0, Cons(0, Cons(1, Cons(2, Null)))));
  var res := LeftPad(Cons(1, Cons(2, Null)), 5, 0);
  assert Extensionality(ls, res);
  assert res == ls;
}