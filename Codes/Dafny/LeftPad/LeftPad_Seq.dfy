/**
  * Verification of Left Pad in sequence
  **/

/**
  *   get maximal value between x and y
  *
  *   @param  x:  An integer value
  *   @param  y:  An integer value
  *   @returns the maximal value
  *
  **/
function max(x: int, y: int): int
{
  if x < y then y else x
}

/**
  *   The predicate to ensure padding of Left Pad
  *
  *   @param  str:  A string value
  *   @param  ln:   The desired length of the return value
  *   @param  c:    The added pad
  *   @param  res:  The return string that has correct padding in desired length
  *
  **/
predicate prefix(str: string, ln: int, c: char, res: string)
  requires ln-|str| <= |res|
{
  forall k :: 0 <= k < ln-|str| ==> c == res[k]
}

/**
  *   The predicate to ensure string of Left Pad
  *
  *   @param  str:  A string value
  *   @param  ln:   The desired length of the return value
  *   @param  res:  The return string that has correct string in desired length
  *   
  *   note:   Correct the quantifier so that str[k-max(ln-|str|, 0)] == res[k]
  **/
predicate suffix(str: string, ln: int, res: string)
  requires max(ln, |str|) == |res|
{
  //forall k :: 0 <= k < |str| ==> str[k] == res[max(ln-|str|, 0)+k]
  forall k :: max(ln-|str|, 0) <= k < |res| ==> str[k-max(ln-|str|, 0)] == res[k]
}

/**
  *   The method to ensure Left Pad
  *
  *   @param  str:    A string value
  *   @param  ln:     The desired length of the return value
  *   @param  c:      The added pad
  *   @returns  res:  The return string that has correct Left Pad in desired length
  *   
  **/
method LeftPad(str: string, ln: int, c: char) returns (res: string)
  requires 0 <= |str| && 0 <= ln
  ensures max(ln, |str|) == |res|
  ensures prefix(str, ln, c, res)
  ensures suffix(str, ln, res)
  decreases ln
{
  if (ln <= |str|) {
    res := str;
  } else if (|str| < ln) {
    var i := 0;
    var pads := ln - |str|;
    res := str;
    while(i < pads)
      invariant 0 <= i <= pads
      invariant |str| + i == |res|
      invariant prefix(str, i+|str|, c, res)
      invariant suffix(str, i+|str|, res)
    {
      res := [c] + res;
      i := i + 1;
    }
  }
}

/**
  *   The main method to test the verification of Left Pad
  *   
  *   note: After correcting the suffix, it verifies var a is padded string
  **/
method Main() {
  var a: string := LeftPad("test", 7, '0');
  assert a == "000test";
  assert a[..] == ['0','0','0','t','e','s','t'];
}