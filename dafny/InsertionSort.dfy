predicate sorted(a:array<int>, min:int, max:int)
    requires 0 <= min <= max <= a.Length 
    reads a
{
  forall i,j | min <= i < j < max :: a[i] <= a[j] 
}

method Exchange(target : array<int>, j : int)
  modifies target
  requires 0 <= j <= target.Length - 2
  requires target[j+1] < target[j]
  ensures multiset(target[..]) == old(multiset(target[..]))
  ensures target[j] < target[j+1]
{
  var k := target[j + 1];
  target[j + 1] := target[j];
  target[j] := k;
}
method Move(target : array<int>, i : int)
  modifies target
  requires 1 <= i <= target.Length - 1
  ensures multiset(target[..]) == old(multiset(target[..]))
{
  var j := i - 1;
  while (0 <= j && target[j+1] < target[j])
    invariant -1 <= j <= i-1 <= target.Length - 2
    invariant multiset(target[..]) == old(multiset(target[..]))
    decreases j
  {
    Exchange(target, j);
    assert target[j] < target[j+1];
    j := j - 1;
  }
  assert !(0 <= j && target[j+1] < target[j]);
  assert (0 > j || target[j+1] >= target[j]);
  assert (-1 == j || target[j+1] >= target[j]);
  if j == -1 {
    assert forall k :: 0 <= k <= i ==> target[0] <= target[k];
  } else {
    assert target[j+1] >= target[j];
    assert forall k :: j + 2 <= k <= i ==> target[j+1] <= target[k];
  }
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
    invariant multiset(target[..]) == old(multiset(target[..]))
  {
    Move(target, i);
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
