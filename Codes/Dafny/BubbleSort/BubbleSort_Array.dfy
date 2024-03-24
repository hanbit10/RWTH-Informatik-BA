/**
  * Verification of bubble sort in array
  **/

/**
  *   Ensure that array is sorted bewteen its lower bound and upper bound
  *
  *   @param  arr:  An integer array which must be sorted
  *   @param  low:  Lower bound of the array
  *   @param  up:   Upper bound of the array
  *
  **/
predicate arraySorted(arr: array?<int>, low: int, up: int)
  requires arr != null
  reads arr
{
  forall p, q :: low <= p < q <= up && 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
}

/**
  *   Predicate that verifies bubblesort evethough, the quantifier is incorrect
  *
  *   @param    arr:  An integer array which must be sorted
  *   @param    low:  Lower bound of the array
  *   @param    up:   Upper bound of the array
  *
  **/
predicate arraySortedWrong(arr: array?<int>, low: int, up: int)
  requires arr != null
  reads arr
{
  forall p, q :: low >= p >= q >= up ==> 0 >= p >= q > arr.Length ==> arr[p] <= arr[q]
}

/**
  *   Predicate that verifies the array is sorted by each iterations
  *
  *   @param    arr:    An integer array which must be sorted
  *   @param    index:  The index of the array
  *
  **/
predicate bubblesSorted(arr: array?<int>, index: int)
  requires arr != null
  reads arr
{
  forall p, q :: p < index < q && 0 <= p < q < arr.Length ==> arr[p] <= arr[q]
}

predicate bubbleStepFinish(arr: array?<int>, up: int)
  requires arr != null
  reads arr
{
  forall k :: 0 <= k < up < arr.Length ==> arr[k] <= arr[up]
}

/**
  *   The method to verify bubble sort
  *
  *   @param    arr:  An integer array which must be sorted
  *   @returns  arr:  The sorted array 
  *
  **/
method BubbleSort(arr: array?<int>)
  requires arr != null
  ensures arr != null
  ensures |arr[..]| == old(|arr[..]|)
  ensures arraySorted(arr, 0, arr.Length-1)
  ensures multiset(arr[..]) == multiset(old(arr[..]))
  modifies arr
{
  var i := 0;
  var n := arr.Length-1;
  while (0 < n-i)
    //Even though the invariants are correct, the loop will not be executed Then the invariants must be adjusted.
    //However, finding the right invariants is not intuitive
    invariant 0 <= i <= n || n == -1
    //check if the array is sorted inbound of n-i to n for each loop
    invariant arraySorted(arr,n-i,n)
    invariant bubblesSorted(arr,n-i)
    invariant multiset(arr[..]) == multiset(old(arr[..]))
    decreases n-i
  {
    var j := 0;
    while (j < n-i)
      invariant 0 <= j <= n-i
      invariant arraySorted(arr, n-i, n)
      //the verifier check for all possible index of n-i to n which is wrong so annotate bubblesSorted
      invariant bubblesSorted(arr, n-i)
      //check j when the bubblestep is finished
      invariant bubbleStepFinish(arr, j)
      invariant multiset(arr[..]) == multiset(old(arr[..]))
      decreases n-j
    {
      if(arr[j] > arr[j+1]) {
        //Sort the array
        var ind1 := arr[j];
        var ind2 := arr[j+1];
        arr[j] := ind2;
        arr[j+1] := ind1;
      }
      j := j+1;
    }
    i := i+1;
  }
}

/**
  *   It counts the multiplicity of the array
  *   
  *   @param    n:    Index
  *   @param    arr:  An integer array
  *   @param    el:   The multiplicity of el
  *   @returns  Multiplicity of the array
  *   
  *   note:     This shows that multiplicity can be implemented in Dafny but not in Caesar
  **/
function multiplicity(n: nat, arr: array?<int>, el: int) : nat
  requires arr != null
  ensures (0 < n <= arr.Length) && (arr[n-1] != el) ==> multiplicity(n, arr, el) == multiplicity(n-1, arr, el)
  ensures (0 < n <= arr.Length) && (arr[n-1] == el) ==> multiplicity(n, arr, el) == 1 + multiplicity(n-1, arr, el)
  ensures (0 == n) ==> multiplicity(n, arr, el) == 0
  reads arr
{
  if (0 < n <= arr.Length) then
    if (arr[n-1] != el) then
      multiplicity(n-1, arr, el)
    else if (arr[n-1] == el) then
      1 + multiplicity(n-1, arr, el)
    else 0
  else 0
}

/**
  *   The main method to test the verification of bubble sort
  *   
  **/
method Main() {

  var arr : array<int> := new int[5];
  arr[0], arr[1], arr[2], arr[3], arr[4] := 1, 6, 3, 4, 5;

  var arr2 : array<int> := new int[5];
  arr2[0], arr2[1], arr2[2], arr2[3], arr2[4] := 3, 1, 4, 6, 5;

  assert forall k:: multiplicity(arr.Length, arr, k) == multiplicity(arr2.Length, arr2, k);

  //assert arraySorted(arr,0,arr.Length-1);
  BubbleSort(arr);
  assert arraySorted(arr, 0, arr.Length-1);
  assert arraySortedWrong(arr, 0, arr.Length-1);
}


