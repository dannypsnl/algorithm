function max(a : int, b : int) : int {
  if a > b then
    a
  else
    b
}

method Solve(target : array<int>) returns (max_sum : int)
  modifies target
{
  max_sum := -1;
  var i := 0;
  while (i < target.Length - 2) {
    var j := i + 1;
    max_sum := max(max_sum, target[i]);
    var local_sum := target[i] + target[j];
    if (local_sum > target[j]) {
      target[j] := local_sum;
    }
    max_sum := max(max_sum, target[j]);

    assert max_sum >= local_sum;
    assert max_sum >= target[i];
    assert max_sum >= target[j];

    i := i + 1;
  }
}
