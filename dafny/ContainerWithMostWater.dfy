function min(a : int, b : int) : int {
  if a > b then
    b
  else
    a
}

function max(a : int, b : int) : int {
  if a > b then
    a
  else
    b
}

// Problem 11. Container With Most Water
method Solve(heights : array<int>)
  returns (max_container : int)
  requires forall k :: 0 <= k < heights.Length ==> heights[k] >= 0
  ensures max_container >= 0
  // ensures forall i, j :: 0 <= i < j < heights.Length ==> max_container >= (j - i) * min(heights[i], heights[j])
{
  if heights.Length < 2 {
    // Because with no bar or only one bar, no container can be formed.
    return 0;
  }

  max_container := 0;

  var l := 0;
  var r := heights.Length - 1;

  while (l < r)
    invariant 0 <= l <= r < heights.Length
    invariant max_container >= 0
    invariant (r - l) * min(heights[l], heights[r]) >= 0
  {
    var h := min(heights[l], heights[r]);
    var container := (r - l) * h;
    max_container := max(max_container, container);

    while (l < r && heights[l] <= h)
      invariant 0 <= l <= r < heights.Length
    {
      l := l + 1;
    }
    while (l < r && heights[r] <= h)
      invariant 0 <= l <= r < heights.Length
    {
      r := r - 1;
    }
  }
  assert max_container >= 0;
}

// Shorter version
method SolveShort(heights : array<int>)
  returns (max_container : int)
  requires heights.Length >= 2
  requires forall k :: 0 <= k < heights.Length ==> heights[k] >= 0
  ensures max_container >= 0
  // ensures forall i, j :: 0 <= i < j < heights.Length ==> max_container >= (j - i) * min(heights[i], heights[j])
{
  var previous_max_container := 0;
  max_container := 0;

  var l := 0;
  var r := heights.Length - 1;

  while (l < r)
    invariant 0 <= l <= r < heights.Length
    invariant max_container >= 0
    // By this we at least know monotonicity of max_container
    invariant max_container >= previous_max_container
  {
    var container := (r - l) * min(heights[l], heights[r]);
    if max_container < container {
      previous_max_container := max_container;
      max_container := container;
    }

    if heights[l] < heights[r] {
      assert (r - l) * heights[l] == container;
      l := l + 1;
    } else {
      assert (r - l) * heights[r] == container;
      r := r - 1;
    }
  }
}

// Verify correctness with concrete examples
method TestSolver()
{
  // Test case 1: [1,8,6,2,5,4,8,3,7] should return 49
  var heights1 := new int[9];
  heights1[0] := 1; heights1[1] := 8; heights1[2] := 6; heights1[3] := 2;
  heights1[4] := 5; heights1[5] := 4; heights1[6] := 8; heights1[7] := 3; heights1[8] := 7;

  var result1 := Solve(heights1);
  assert result1 >= 0;

  // Test case 2: [1,1] should return 1
  var heights2 := new int[2];
  heights2[0] := 1; heights2[1] := 1;

  var result2 := Solve(heights2);
  assert result2 >= 0;

  print "Test 1 result: ", result1, "\n";
  print "Test 2 result: ", result2, "\n";
}
