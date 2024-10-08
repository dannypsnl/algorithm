method LinearSearch(xs : array<int>, x : int) returns (index : int)
{
  index := 0;
  while (index < xs.Length - 1)
  {
    if (xs[index] == x) {
      return index;
    }
    index := index + 1;
  }
  return -1;
}
