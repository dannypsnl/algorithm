predicate sorted(a:array<int>, min:int, max:int)
    requires 0 <= min <= max <= a.Length 
    reads a
{
  forall i,j | min <= i < j < max :: a[i] <= a[j] 
}

method InsertionSort(target : array<int>)
  modifies target
  ensures forall i,j :: 0 <= i < j < target.Length ==> target[i] <= target[j]
  ensures multiset(target[..]) == old(multiset(target[..]))
{
  assert multiset(target[..]) == old(multiset(target[..]));
  var i := 1;
  while (i < target.Length - 1)
    invariant 1 <= i <= target.Length+1
  {
    var key := target[i];
    var j := i - 1;
    while (0 < j && key < target[j])
      invariant 0 <= j <= i - 1
      decreases j
    {
      target[j + 1] := target[j];
      assert key < target[j];
      j := j - 1;
    }
    target[j+1] := key;
    assert forall k :: j+1 < k <= i ==> key < target[k];
    i := i + 1;
  }
}

method InsertionSortBackward(target : array<int>)
  modifies target
{
  // [...-2-1]
  // Thus, the length - 2 is the position we want
  var i := target.Length - 2;
  while (i > 1)
    invariant i <= target.Length - 2
    decreases i
  {
    var key := target[i];
    var j := i + 1;
    while (j < target.Length - 1 && target[j] < key)
      invariant i + 1 <= j <= target.Length
    {
      target[j - 1] := target[j];
      j := j + 1;
    }
    target[j-1] := key;
    i := i - 1;
  }
}
