predicate Sorted(a : array<int>, min : int, max : int)
  requires 0 <= min <= max <= a.Length - 1
  reads a
{
  forall i, j :: min <= i <= j <= max ==> a[i] <= a[j]
}

method Exchange(target : array<int>, j : int)
  modifies target
  requires 1 <= j <= target.Length - 1
  requires target[j] < target[j-1]
  ensures multiset(target[..]) == old(multiset(target[..]))
  ensures target[j-1] < target[j]
{
  var key := target[j - 1];
  target[j - 1] := target[j];
  target[j] := key;
}
// idea: The 0..k-1 is sorted array, now insert k to proper position,
// and at the end of this method 0..k is sorted
method Insert(target : array<int>, k : int)
  modifies target
  requires 1 <= k <= target.Length - 1
  requires Sorted(target, 0, k-1)
  ensures multiset(target[..]) == old(multiset(target[..]))
  ensures Sorted(target, 0, k)
{
  if k == 1 {
    if target[0] > target[1] {
      Exchange(target, 1);
    }
    return;
  } else {
    assert k >= 2;
    if target[k-1] > target[k] {
      assert target[k-1] > target[k];
      var key := target[k - 1];
      target[k - 1] := target[k];
      target[k] := key;
      assert target[k] > target[k-1];
      assert Sorted(target, 0, k-2);
      Insert(target, k-1);
      assert Sorted(target, 0, k-1);
      assert target[k] > target[k-1];
      assert Sorted(target, 0, k);
    }
  }
}

method InsertionSort(target : array<int>)
  modifies target
  // well, [] and [x] is trivial, no need to sort it
  requires target.Length >= 2
  ensures Sorted(target, 0, target.Length - 1)
  ensures multiset(target[..]) == old(multiset(target[..]))
{
  if target[0] > target[1] {
    var k := target[1];
    target[1] := target[0];
    target[0] := k;
  }
  assert Sorted(target, 0, 1);
  // first two are ordered now

  var k := 2;
  while (k < target.Length)
    invariant 2 <= k <= target.Length
    invariant multiset(target[..]) == old(multiset(target[..]))
    invariant Sorted(target, 0, k - 1)
  {
    Insert(target, k);
    k := k + 1;
  }
  assert k == target.Length;
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
