datatype List	 = Null | Cons(head: int, tail: List)

method Main() {
  var ls: List := Cons(1, Cons(2, Null));
  print "ls: ", ls, "\n";

  //Create new array length of 3
  var arr: array<int>:= new int[3];
  arr[0], arr[1], arr[2] := 7,5,4;

  //Get element in index 2
  var res := arr[2];

  //Get length of the array
  var res1 := arr.Length;

  //Store element in index 1
  arr[1] := 2;

  var st_1 : set<int> := {1,1,1,1,2};
  var st_2 : set<int> := {1,2};

  // Sets are equal.
  assert st_1 == st_2;

  var ms_1 : multiset<int> :=  multiset([1, 1, 1, 2]);
  var ms_2 : multiset<int> :=  multiset([1, 2]);

  // Multisets are not equal.
  assert ms_1 != ms_2;

  var sq : seq<int> := [1, 2, 3, 4];

  // Seq<char>
  assert "test" == ['t','e','s','t'];
}

method assign_x(x: int) returns (y: int)
{
  y := x;
}

function even(x: int) : bool
{
  if (x%2 == 0) then true else false
}

method AA()
{
  var x: int := 1;
  assume 0 > x;
  assert 0 > x;
}

method Min(x:int, y:int) returns (res:int)
{
  if (x < y) {
    res := x;
  } else {
    res := y;
  }
}

method Mul(b: int, e: int) returns (x: int)
  requires 0 <= e
  ensures x == b*e
{
  x := 0;
  var i := e;
  while (0 < i)
    invariant x == b * (e-i)
  {
    x := x + b;
    i := i - 1;
  }
}

predicate odd(x: int)
{
  (x%2) == 1
}

function P(x: int): bool
function Q(y: int): bool

method TriggerQ()
  requires forall i {:trigger Q(i) /*&& P(i)*/}::
             P(i) ==> P(i-1) && Q(i)
{
  assume P(0);
  assert Q(0);
  assert P(-1);
  assert P(-2);
}