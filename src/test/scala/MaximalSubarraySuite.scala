class MaximalSubarraySuite extends munit.FunSuite {
  test("maximal subarray sum: dynamic solver") {
    val solver = MaximalSubarray(Array(-1, 1, 2, 3));
    val obtained = solver.dynamic_solve();
    val expected = solver.naive_solve();
    assertEquals(obtained, expected)
  }

  test("can it cross the boundary?") {
    val solver = MaximalSubarray(Array(10, -1, 1, 2, 3));
    val obtained = solver.dynamic_solve();
    val expected = solver.naive_solve();
    assertEquals(obtained, expected)
  }
}
