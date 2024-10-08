predicate sorted(a:array<int>, min:int, max:int)
    requires 0 <= min <= max <= a.Length 
    reads a
{
  forall i,j | min <= i < j < max :: a[i] <= a[j] 
}

method InsertionSort(target : array<int>)
  modifies target
{
  var i := 1;
  while (i < target.Length - 1)
    invariant 1 <= i
  {
    var key := target[i];
    var j := i - 1;
    while (j > 0 && target[j] > key)
    {
      target[j + 1] := target[j];
      j := j - 1;
    }
    target[j+1] := key;
    i := i + 1;
  }
}

method InsertionSortBackward(target : array<int>)
  modifies target
{
  var i := target.Length - 1;
  while (i > 1)
    invariant i <= target.Length - 1
    decreases i
  {
    var key := target[i];
    var j := i + 1;
    while (j < target.Length - 1 && target[j] < key)
      invariant i + 1 <= j <= target.Length - 1
    {
      target[j - 1] := target[j];
      j := j + 1;
    }
    target[j-1] := key;
    i := i - 1;
  }
}
