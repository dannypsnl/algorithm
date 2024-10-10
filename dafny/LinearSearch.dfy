method LinearSearch<T>(xs : array<T>, P : T -> bool) returns (index : int)
{
  index := 0;
  while (index < xs.Length - 1)
  {
    if (P(xs[index])) {
      return index;
    }
    index := index + 1;
  }
  return -1;
}
