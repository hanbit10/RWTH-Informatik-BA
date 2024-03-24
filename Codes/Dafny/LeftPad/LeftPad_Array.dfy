//Leftpad with char array with 2 while loops to compare with Caesar

//max function
function max(x: int, y: int): int
{
  if x < y then y else x
}

//function prefix verifies if the pad is correctly allocated
predicate prefix(str: array?<char>, ln: int, c:char, res: array?<char>)
  reads res, str
  requires res != null && str != null
  requires ln-str.Length <= res.Length
{
  forall k :: 0 <= k < ln-str.Length ==> res[k] == c
}

//predicate suffix verifies if the chararacter array are correctly allocated
predicate suffix(str: array?<char>, ln: int, res: array?<char>)
  reads res, str
  requires res != null && str != null
  requires max(ln, str.Length) == res.Length
{
  forall k :: max(ln - str.Length, 0) <= k < res.Length ==> str[k-max(ln-str.Length, 0)] == res[k]
}

//method verifies Left Pad function in type array
method Leftpad(str: array<char>, ln: int, c: char) returns (res: array<char>)
  requires 0 <= ln
  requires 0 <= str.Length
  ensures max(ln, str.Length) == res.Length
  ensures prefix(str, ln, c, res)
  ensures suffix(str, ln, res)
  //ensures forall k:: max(ln-str.Length, 0) <= k < res.Length ==> str[k-max(ln-str.Length, 0)] == res[k]
{
  res := new char[max(ln, str.Length)];
  if (ln <= str.Length) {
    res := str;
  } else if (str.Length < ln) {
    var i := 0;
    var pads := ln-str.Length;
    // prefix with char c
    while (i < pads)
      invariant 0 <= ln && 0 <= i <= pads
      invariant ln == res.Length
      invariant prefix(str, i+str.Length, c, res)
    {
      res[i] := c;
      i := i+1;
    }
    var j := 0;
    //allocate characters of array in str[k] == res[max(ln-str.Length, 0)+k]
    while (j < str.Length)
      invariant 0 <= j <= str.Length
      invariant res.Length == ln
      invariant prefix(str, i+str.Length, c, res)
      invariant forall k :: 0 <= k < j ==> str[k] == res[max(ln - str.Length, 0)+k]
      //invariant forall k :: max(ln-str.Length, 0) <= k < j ==> str[k-max(ln - str.Length, 0)] == res[k]
    {
      res[ln-str.Length+j]:= str[j];
      j := j+1;
    }
  }
}


//Main tests functionality of the Leftpad
method Main() {
  var str : array<char> := new char[4];
  str[0], str[1], str[2], str[3] := 't','e','s','t';

  var res := Leftpad(str, 5, '0');
  assert res[..] == ['0','t','e','s','t'];
}