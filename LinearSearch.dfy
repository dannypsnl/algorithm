method LinearSearch<T>(xs : array<T>, P : T -> bool) returns (index : int)
  ensures 0 <= index <= xs.Length
  ensures index == xs.Length || P(xs[index])
{
  index := 0;
  while (index != xs.Length)
    invariant 0 <= index <= xs.Length
  {
    if (P(xs[index])) {
      return;
    }
    index := index + 1;
  }
}
