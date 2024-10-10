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
// idea: The 0..k-1 is sorted array, now insert i to proper position,
// and at the end of this method 0..k is sorted
method Insert(target : array<int>, k : int)
  modifies target
  requires 2 <= k <= target.Length - 1
  requires forall i,j :: 0 <= i < j <= k-1 ==> target[i] <= target[j]
  ensures multiset(target[..]) == old(multiset(target[..]))
  ensures forall i,j :: 0 <= i < j <= k ==> target[i] <= target[j]
{
  var j := k-1;
  while (j > 0)
    invariant multiset(target[..]) == old(multiset(target[..]))
    decreases j
  {
    if target[j] > target[j+1] {
      Exchange(target, j);
    } else {
      return;
    }
    j := j - 1;
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

  if target[0] > target[1] {
    Exchange(target, 0);
  } else {
    // do nothing
  }
  assert forall i,j :: 0 <= i < j < 2 ==> target[i] <= target[j];
  // first two are ordered now

  var k := 2;
  while (k < target.Length)
    invariant 2 <= k <= target.Length
    invariant multiset(target[..]) == old(multiset(target[..]))
    invariant forall i,j :: 0 <= i < j <= k-1 ==> target[i] <= target[j]
  {
    Insert(target, k);
    assert forall i,j :: 0 <= i < j <= k ==> target[i] <= target[j];
    k := k + 1;
  }
  assert k == target.Length;
}

method TestInsertionSortAtLengthTwo(target : array<int>)
  modifies target
  requires target.Length == 2
  ensures forall i,j :: 0 <= i < j < target.Length ==> target[i] <= target[j]
  ensures multiset(target[..]) == old(multiset(target[..]))
{
  InsertionSort(target);
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
