/**
  *   Translate the code to verify BubbleSort in Caesar. 
  *   First create a new List with all the needed definitions in Dafny
  **/

datatype List	 = Null | Cons(head: nat, tail: List)

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
function Select(ls: List, i: nat): nat
  requires i < Length(ls)
{
  if (ls.Cons?) then
    var h := ls.head;
    var t := ls.tail;
    if (i != 0) then Select(t, i-1)
    else h
  else 0
}

/**
  *   The fuction to store elements
  *
  *   @param  ls:     A datatype List
  *   @param  i:      Index 
  *   @param  el:     The stored element
  *   @returns    Return List that stores el in i
  *   
  **/
function Store(ls: List, i: nat, el: nat) : List
  requires i < Length(ls)
  //ensures after changing the value the length is still the same
  ensures Length(Store(ls, i, el)) == Length(ls)
  //make sure what element is stored in the index i
  ensures forall k: nat :: k < Length(Store(ls, i, el)) && k < Length(ls) && (k != i) ==> Select(Store(ls, i, el), k) == Select(ls, k)
  ensures Select(Store(ls, i, el), i) == el
{
  if(ls.Null?) then ls
  else if (ls.Cons?) then
    var t := ls.tail;
    var h := ls.head;
    if(i == 0) then
      Cons(el, t)
    else
      var ind1 := Store(t, i-1, el);
      Cons(h, ind1)
  else Null
}

/**
  *   It counts the multiplicity of the array
  *   
  *   @param    ls:   An nat array
  *   @param    el:   The multiplicity of el
  *   @returns  Multiplicity of the array
  *   
  *   note:     This shows that multiplicity can be implemented in Dafny but not in Caesar
  **/
function multiplicity(ls: List, el: nat) : nat
  requires 0 <= Length(ls)
  ensures ls == Null ==> multiplicity(ls, el) == 0
  ensures forall h: nat, t: List:: ls == Cons(h, t) && h == el ==> multiplicity(ls, el) == 1 + multiplicity(t, el)
  ensures forall h: nat, t: List:: ls == Cons(h, t) && h != el ==> multiplicity(ls, el) == multiplicity(t, el)
{
  if (ls.Null?) then 0
  else if (ls.Cons?) then
    var h := ls.head;
    var t := ls.tail;
    if (h == el) then 1 + multiplicity(t, el)
    else multiplicity(t, el)
  else 0
}

method BubbleSort(arr: List) returns (res: List)
  requires arr != Null
  requires 0 <= Length(arr)
  ensures 0 <= Length(res)
  ensures Length(arr) == Length(res)
  ensures forall p, q :: 0  <= p <= q < Length(res) ==> Select(res, p) <= Select(res, q)
{
  res := arr;
  var i :nat := 0;
  var n := Length(res) - 1;
  while(0 < n-i)
    invariant (0 <= i <= n) || (n == n - 1)
    invariant Length(arr) == Length(res)
    invariant 0 <= n-i
    invariant i < Length(res)
    invariant forall p, q :: n-i <= p <= q <= n < Length(res) ==> Select(res, p) <= Select(res, q)
    invariant forall p, q :: 0 <= p <= n-i < q < Length(res) ==> Select(res, p) <= Select(res, q)
  {
    var j :nat := 0;
    while (j < n-i)
      invariant 0 <= j <= n-i || (n == n - 1)
      invariant Length(arr) == Length(res)
      invariant forall p, q :: n-i <= p <= q <= n < Length(res) ==> Select(res, p) <= Select(res, q)
      invariant forall p, q :: 0 <= p <= n-i < q < Length(res) ==> Select(res, p) <= Select(res, q)
      invariant forall k:: 0 <= k <= j ==> Select(res, k) <= Select(res, j)
    {
      if(Select(res, j) > Select(res, j+1))
      {
        var ind1 := Select(res, j);
        var ind2 := Select(res, j+1);
        res := Store(res, j, ind2);
        res := Store(res, j+1, ind1);
      }
      j := j+1;
    }
    i := i+1;
  }
}

method Main ()
{
  var ls : List := Cons(3, Cons(1, Cons(5, Cons(4, Cons(3, Cons(5, Null))))));
  var res : List := BubbleSort(ls);
  assert forall p, q :: 0 <= p < q < Length(res) ==> Select(res, p) <= Select(res, q);
}
