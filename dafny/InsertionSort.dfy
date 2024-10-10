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
  if target.Length == 1 || target.Length == 0 {
    return;
  }
  assert target.Length >= 2;
  var i := 1;
  while (i < target.Length - 1)
    invariant 1 <= i <= target.Length
  {
    var key := target[i];
    var j := i - 1;
    while (0 <= j && key < target[j])
      invariant i - 1 >= j >= -1
      decreases j
    {
      assert key < target[j];
      target[j + 1] := target[j];
      assert key < target[j+1];
      j := j - 1;
    }
    assert !(0 <= j && key < target[j]);
    assert (0 > j || key >= target[j]);
    assert (-1 == j || key >= target[j]);
    target[j+1] := key;
    if (j == -1) {
      assert -1 == j;
      assert key == target[j+1];
      assert key == target[0];
      // assert forall k :: 1 <= k <= i ==> key < target[k];
    } else {
      assert key >= target[j];
      assert key == target[j+1];
      assert target[j+1] >= target[j];
      assert key < target[j+1];
      // assert forall k :: j+2 <= k <= i ==> key < target[k];
    }
    i := i + 1;
  }
  assert i >= target.Length - 1;
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
