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

-- | Least Significant Bit Difference (e.g. lsb 0b0101 0b0001 == 2 )
def lsb_diff (a: i64) (b: i64) : i8 =
  if a == b
  then -1
  else a ^ b |> i64.ctz |> i8.i32

-- | An initial n-coloring of a list.
def init_color (n: i64) : [n]i64 = iota n

-- | A log k-coloring constructed from a list and a k-coloring and a
-- list.
def logk_coloring [n] (color: [n]i64) (succ: [n]i64) : [n]i8 =
  tabulate n (\i -> lsb_diff color[i] color[succ[i]])

-- | The different found in lsb_diff.
def bit (v: i64) (b: i8) : i8 =
  i8.i64 ((v >> i64.i8 b) & 1)

-- | Construct a log n-ruling set.
def ruling_set [n] (h: i64) (succ: [n]i64) : [n]bool =
  let l = end succ
  let succ = copy succ with [l] = h
  let color0 = init_color n
  let color1 = logk_coloring color0 succ
  let is_local_min = tabulate n (\i -> color1[i] >= color1[succ[i]] && color1[succ[i]] <= color1[succ[succ[i]]])
  let is_local_max = tabulate n (\i -> color1[i] <= color1[succ[i]] && color1[succ[i]] >= color1[succ[succ[i]]])
  let selected =
    tabulate n (\i ->
                  let neighbor_is_local_min = is_local_min[i] || is_local_min[succ[succ[i]]]
                  let coin = bit color0[succ[i]] color1[succ[i]]
                  in is_local_min[succ[i]] && ((not neighbor_is_local_min) || coin == 1))
  let available =
    tabulate n (\i ->
                  not selected[succ[i]]
                  && not selected[i]
                  && not selected[succ[succ[i]]]
                  && is_local_max[succ[i]])
  let selected' =
    tabulate n (\i ->
                  let neighbor_is_available = available[i] || available[succ[succ[i]]]
                  let coin = bit color0[succ[i]] color1[succ[i]]
                  in selected[succ[i]] || (available[succ[i]] && ((not neighbor_is_available) || coin == 1)))
  in selected'
