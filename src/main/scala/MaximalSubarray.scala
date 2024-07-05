import scala.collection.mutable.HashMap

def sum(xs: Array[Int]): Int = {
  var s = 0;
  for (x <- xs) {
    s = s + x;
  }
  s
}

def all_subarray(xs: Array[Int]): Set[Array[Int]] = {
  var s = Set[Array[Int]]();
  for (i <- 0 to xs.length) {
    for (j <- i + 1 to xs.length) {
      s = s + xs.slice(i, j)
    }
  }
  s
}

class MaximalSubarray(target: Array[Int]) {
  var max_sum: Int = 0;
  var cur_sum: Int = 0;
  var computed_sum: HashMap[Tuple2[Int, Int], Int] = HashMap();

  def cache_sum(from: Int, size: Int): Int = {
    computed_sum.get((from, size)) match {
      case Some(s) => s
      case None => {
        val xs_sum = if (size == 1) {
          target(from)
        } else {
          val sum_left =
            cache_sum(from, size - 1) + cache_sum(from + size - 1, 1)
          val sum_right = cache_sum(from, 1) + cache_sum(from + 1, size - 1)
          math.max(sum_left, sum_right)
        }
        computed_sum.put((from, size), xs_sum)
        max_sum = math.max(xs_sum, max_sum)
        xs_sum
      }
    }
  }

  def dynamic_solve(): Int = {
    cache_sum(0, target.length)
    max_sum
  }

  def naive_solve(): Int = {
    max_sum = 0
    val subarrays = all_subarray(target);
    for (arr <- subarrays) {
      max_sum = math.max(sum(arr), max_sum)
    }
    max_sum
  }
}
