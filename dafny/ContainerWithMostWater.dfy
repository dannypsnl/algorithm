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
{
  if heights.Length < 2 {
    // Because with no bar or only one bar, no container can be formed.
    return 0;
  }

  max_container := -1;

  var l := 0;
  var r := heights.Length - 1;

  while (l < r)
    invariant 0 <= l <= r < heights.Length
    invariant max_container >= -1
  {
    var container := (r - l) * min(heights[l], heights[r]);
    max_container := max(max_container, container);

    if heights[l] < heights[r] {
      // Move left pointer to next higher bar
      var current_height := heights[l];
      while (l < r && heights[l] <= current_height)
        invariant 0 <= l <= r < heights.Length
      {
        l := l + 1;
      }
    } else {
      // Move right pointer to next higher bar
      var current_height := heights[r];
      while (l < r && heights[r] <= current_height)
        invariant 0 <= l <= r < heights.Length
      {
        r := r - 1;
      }
    }
  }
}
