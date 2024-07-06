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
  var max_sum: Int = Int.MinValue;
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

  def induced_solve(): Int = {
    max_sum = Int.MinValue
    var cloned_target = target.clone()
    for (i <- 0 to cloned_target.length - 2; j = i + 1) {
      max_sum = math.max(max_sum, cloned_target(i))
      val local_sum = cloned_target(i) + cloned_target(j)
      if (local_sum > cloned_target(j)) {
        cloned_target(j) = local_sum
      }
      max_sum = math.max(max_sum, cloned_target(j))
    }
    max_sum
  }

  def dynamic_solve(): Int = {
    max_sum = Int.MinValue
    cache_sum(0, target.length)
    max_sum
  }

  def naive_solve(): Int = {
    max_sum = Int.MinValue
    val subarrays = all_subarray(target);
    for (arr <- subarrays) {
      max_sum = math.max(sum(arr), max_sum)
    }
    max_sum
  }
}
