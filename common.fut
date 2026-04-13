-- | Common functions.

-- | Values for pointing to nothing.
def nil : i64 = -1

-- | Ceiled integer log2.
def ceil_log2 (a: i64) : i64 =
  i64.i32 (i64.num_bits - i64.clz (a - 1))

-- | Floored integer log2.
def floor_log2 (a: i64) : i64 =
  i64.i32 ((i64.num_bits - 1) - i64.clz a)

-- | Invert the pointers of a successor array.
def invert [n] (succ: [n]i64) : [n]i64 =
  scatter (rep nil) succ (iota n)

-- | Find index of which satisfies a predicate.
def find_index 'a [n] (p: a -> bool) (as: [n]a) : i64 =
  let op (x, i) (y, j) =
    if x && y
    then if i < j
         then (x, i)
         else (y, j)
    else if y
    then (y, j)
    else (x, i)
  in (reduce_comm op (false, -1) (zip (map p as) (iota n))).1

-- | Find the end of list.
def end [n] (succ: [n]i64) : i64 =
  find_index (== nil) succ
