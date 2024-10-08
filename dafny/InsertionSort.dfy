predicate sorted(a:array<int>, min:int, max:int)
    requires 0 <= min <= max <= a.Length 
    reads a
{
  forall i,j | min <= i < j < max :: a[i] <= a[j] 
}

method InsertionSort(target : array<int>)
  modifies target
{
  var i := target.Length - 1;
  while (i > 2)
    invariant i <= target.Length - 1
    decreases i
  {
    var key := target[i];
    var j := i - 1;
    while (j > 0 && target[j] > key)
      invariant j < i
      decreases j
    {
      target[j + 1] := target[j];
      j := j - 1;
    }
    target[j] := key;
    i := i - 1;
  }
}
