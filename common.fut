-- | Common functions.

import "lib/github.com/diku-dk/cpprandom/random"
import "lib/github.com/diku-dk/sorts/radix_sort"

-- | Values for pointing to nothing.
def nil : i64 = -1

-- | Assert if the parent vector forms a valid list.
def is_valid_list [n] (h: i64) (S: [n]i64) : bool =
  let (final_node, visited) =
    loop (i, visited) = (h, replicate n false)
    while 0 <= i && i < n && not visited[i] && S[i] != nil do
      (S[i], visited with [i] = true)
  let visited[final_node] = true
  in S[final_node] == nil && and visited

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

def lsb_diff_i8 (a: i8) (b: i8) : i8 =
  if a == b
  then -1
  else a ^ b |> i8.ctz |> i8.i32

-- | An initial n-coloring of a list.
def init_color (n: i64) : [n]i64 = iota n

-- | A log k-coloring constructed from a list and a k-coloring and a
-- list.
def logk_coloring [n] (color: [n]i64) (succ: [n]i64) : [n]i8 =
  tabulate n (\i -> lsb_diff color[i] color[succ[i]])

-- | The different found in lsb_diff.
def bit (v: i64) (b: i8) : i8 =
  i8.i64 ((v >> i64.i8 b) & 1)

def logk_coloring_i8 [n] (color: [n]i8) (succ: [n]i64) : [n]i8 =
  tabulate n (\i -> lsb_diff_i8 color[i] color[succ[i]])

-- | The different found in lsb_diff.
def bit_i8 (v: i8) (b: i8) : i8 =
  (v >> b) & 1

def predecessor [n] (succ: [n]i64) : [n]i64 =
  scatter (rep nil) succ (iota n)

def logk_ruling_set [n] (h: i64) (succ: [n]i64) : [n]bool =
  let pred = predecessor succ
  let l = end succ
  let succ = copy succ with [l] = h
  let pred = copy pred with [h] = l
  let color0 = init_color n
  let color1 = logk_coloring color0 succ
  let color2 = logk_coloring_i8 color1 succ
  let is_local_min = tabulate n (\i -> color2[pred[i]] >= color2[i] && color2[i] <= color2[succ[i]])
  let is_local_max = tabulate n (\i -> color2[pred[i]] <= color2[i] && color2[i] >= color2[succ[i]])
  let selected =
    tabulate n (\i ->
                  let neighbor_is_local_min = is_local_min[pred[i]] || is_local_min[succ[i]]
                  let coin = bit color0[i] color2[i]
                  in is_local_min[i] && ((not neighbor_is_local_min) || coin == 1))
  let available =
    tabulate n (\i ->
                  not selected[i]
                  && not selected[pred[i]]
                  && not selected[succ[i]]
                  && is_local_max[i])
  let selected' =
    tabulate n (\i ->
                  let neighbor_is_available = available[pred[i]] || available[succ[i]]
                  let coin = bit color0[i] color2[i]
                  in selected[i] || (available[i] && ((not neighbor_is_available) || coin == 1)))
  in selected'

def logx_ruling_set [n] (h: i64) (succ: [n]i64) : [n]bool =
  let l = end succ
  let succ = copy succ with [l] = h
  let color0 = init_color n
  let color2 = logk_coloring color0 succ
  let is_local_min =
    tabulate n (\i -> color2[i] >= color2[succ[i]] && color2[succ[i]] <= color2[succ[succ[i]]])
    |> scatter (replicate n false) (rotate 1 (iota n))
  let is_local_max =
    tabulate n (\i -> color2[i] <= color2[succ[i]] && color2[succ[i]] >= color2[succ[succ[i]]])
    |> scatter (replicate n false) (rotate 1 (iota n))
  let selected =
    tabulate n (\i ->
                  let neighbor_is_local_min = is_local_min[i] || is_local_min[succ[succ[i]]]
                  let coin = bit color0[succ[i]] color2[succ[i]]
                  in is_local_min[succ[i]] && ((not neighbor_is_local_min) || coin == 1))
    |> scatter (replicate n false) (rotate 1 (iota n))
  let available =
    tabulate n (\i ->
                  not selected[succ[i]]
                  && not selected[i]
                  && not selected[succ[succ[i]]]
                  && is_local_max[succ[i]])
    |> scatter (replicate n false) (rotate 1 (iota n))
  let selected' =
    tabulate n (\i ->
                  let neighbor_is_available = available[i] || available[succ[succ[i]]]
                  let coin = bit color0[succ[i]] color2[succ[i]]
                  in selected[succ[i]] || (available[succ[i]] && ((not neighbor_is_available) || coin == 1)))
    |> scatter (replicate n false) (rotate 1 (iota n))
  in selected'

-- | Construct a 2-ruling set.
def two_ruling_set [n] (h: i64) (succ: [n]i64) : [n]bool =
  let set = rep false
  let is = iota n
  let succ = copy succ
  let (set, h, succ, is) =
    loop (set, h, succ, is)
    while 3 < length succ do
      let small_set =
        assert (is_valid_list h succ)
        (copy (map2 (\i s ->
                       if i == h || i == succ[h]
                       then false
                       else s)
                    (indices succ)
                    (logk_ruling_set h succ)))
      let ns =
        map (\i ->
               if small_set[i]
               then succ[i]
               else if succ[i] != nil && small_set[succ[i]]
               then i
               else nil)
            (indices succ)
      let rs = map (\i -> if small_set[i] then i else nil) (indices succ)
      let set = scatter set (map (\j -> if j == nil then nil else is[j]) rs) (rep true)
      let small_set = scatter small_set ns (rep true)
      let keep = filter (\i -> not small_set[i]) (indices succ)
      let succ =
        map (\i ->
               loop i while i != nil && small_set[i] do succ[i])
            succ
      let compressed = scatter (replicate (length succ) nil) keep (indices keep)
      let succ = map (\a -> if succ[a] == nil then nil else compressed[succ[a]]) keep
      let is = map (\i -> is[i]) keep
      in (set, compressed[h], succ, is)
  let set =
    if length is == 3
    then let set[is[h]] = true
         let set[is[succ[succ[h]]]] = true
         in set
    else let set[is[h]] = true
         in set
  in set

module rng_engine = minstd_rand
module rand_i32 = uniform_int_distribution i32 u32 rng_engine

entry blocked_list (n: i64) (B: i64) =
  let seed = 13632
  let rng = rng_engine.rng_from_seed [seed]
  let rngs = rng_engine.split_rng n rng
  let keys =
    map2 (\i rng ->
            let x = i / B
            let (_, y) = rand_i32.rand (0, i32.highest - 1) rng
            in (u64.i64 x << 32) | (u64.i32 y))
         (iota n)
         rngs
  let tmp = map (.1) (radix_sort_by_key (.0) u64.num_bits u64.get_bit (zip keys (iota n)))
  let (idx, S) = zip tmp (rotate 1 tmp) |> unzip
  let lst = scatter (replicate n 0) idx S
  let h = lst[n - 1]
  let lst[n - 1] = nil
  in (h, lst)

-- | Check if a subset of vertices forms a k-ruling set.
def is_k_ruling_set [n] (k: i64) (succ: [n]i64) (selected: [n]bool) : bool =
  let no_adjacent =
    all (\i ->
           if selected[i] && succ[i] != nil
           then !selected[succ[i]]
           else true)
        (iota n)
  let can_reach_within_k =
    all (\start ->
           let (found, _, _) =
             loop (found, pos, steps) = (false, start, 0)
             while !found && steps <= k && pos != nil do
               if selected[pos] || succ[pos] == -1
               then (true, pos, steps)
               else (false, succ[pos], steps + 1)
           in found)
        (iota n)
  in no_adjacent && can_reach_within_k

-- ==
-- entry: test_two_ruling_set test_logn_ruling_set
-- "n=10000,s=1"     compiled nobench script input { blocked_list 10000i64 1i64 }  output { true }
-- "n=10000,s=10"    compiled nobench script input { blocked_list 10000i64 10i64 } output { true }
-- "n=10000,s=100"   compiled nobench script input { blocked_list 10000i64 100i64 } output { true }
-- "n=100000,s=1"    compiled nobench script input { blocked_list 100000i64 1i64 }  output { true }
-- "n=100000,s=10"   compiled nobench script input { blocked_list 100000i64 10i64 } output { true }
-- "n=100000,s=100"  compiled nobench script input { blocked_list 100000i64 100i64 } output { true }
entry test_two_ruling_set [n] (h: i64) (succ: [n]i64) : bool =
  let ruling_set = two_ruling_set h succ
  in is_k_ruling_set 2 succ ruling_set

entry test_logn_ruling_set [n] (h: i64) (succ: [n]i64) : bool =
  let k = ceil_log2 n
  let ruling_set = logk_ruling_set h succ
  in is_k_ruling_set k succ ruling_set

-- ==
-- entry: test_blocked_list_valid
-- "n=10000,s=1"     compiled nobench input { 10000i64 1i64 } output { true }
-- "n=10000,s=10"    compiled nobench input { 10000i64 10i64 } output { true }
-- "n=10000,s=100"   compiled nobench input { 10000i64 100i64 } output { true }
-- "n=100000,s=1"    compiled nobench input { 100000i64 1i64 } output { true }
-- "n=100000,s=10"   compiled nobench input { 100000i64 10i64 } output { true }
-- "n=100000,s=100"  compiled nobench input { 100000i64 100i64 } output { true }
entry test_blocked_list_valid (n: i64) (B: i64) : bool =
  let (h, succ) = blocked_list n B
  in is_valid_list h succ

def logn_bucket_sort 'a [n] (keys: [n]i8) (values: [n]a) : ([n]i8, [n]a) =
  let block_size = ceil_log2 n
  let block_num = (n + block_size - 1) / block_size
  let block_count block_i =
    let start = block_i * block_size
    let end = i64.min n ((block_i + 1) * block_size)
    let rank = replicate block_size (-1i8)
    let count = replicate block_size 0i64
    let block_keys = keys[start:end]
    in loop (rank, count)
       for (j, i) in zip (indices block_keys) block_keys do
         let rank[j] = i8.i64 count[i]
         let count[i] = count[i] + 1
         in (rank, count)
  let (ranks, counts) =
    tabulate block_num block_count
    |> unzip
  let counts = transpose counts |> flatten
  let offsets =
    counts
    |> scan (+) 0
    |> flip (map2 (-)) counts
    |> unflatten
    |> transpose
  let flat_ranks = flatten ranks
  let is =
    tabulate n (\i ->
                  let block_id = i / block_size
                  in offsets[block_id][keys[i]] + i64.i8 flat_ranks[i])
  let sorted_keys = scatter (replicate n 0i8) is keys
  let sorted_values = scatter (#[scratch] replicate n values[0]) is values
  in (sorted_keys, sorted_values)

module rand_i8 = uniform_int_distribution i8 u32 rng_engine

def is_sorted [n] (arr: [n]i8) : bool =
  all (\i -> i == n - 1 || arr[i] <= arr[i + 1]) (iota n)

def is_stable [n] (sorted_keys: [n]i8) (sorted_indices: [n]i64) : bool =
  all (\i ->
         i == n - 1
         || sorted_keys[i] != sorted_keys[i + 1]
         || sorted_indices[i] < sorted_indices[i + 1])
      (iota n)

def gen_random_keys (n: i64) (seed: i32) : [n]i8 =
  let log_n = i64.max 1 (ceil_log2 n)
  let max_val = i8.i64 (log_n - 1)
  let rng = rng_engine.rng_from_seed [seed]
  let rngs = rng_engine.split_rng n rng
  in map (\r -> (rand_i8.rand (0, max_val) r).1) rngs

-- ==
-- entry: test_logn_bucket_sort
-- input { 8i64 42i32 }
-- output { true true }
-- input { 100i64 123i32 }
-- output { true true }
-- input { 1000i64 999i32 }
-- output { true true }
-- input { 10000i64 55555i32 }
-- output { true true }
entry test_logn_bucket_sort (n: i64) (seed: i32) : (bool, bool) =
  let keys = gen_random_keys n seed
  let values = iota n
  let (sorted_keys, sorted_values) = logn_bucket_sort keys values
  let sorted = is_sorted sorted_keys
  let stable = is_stable sorted_keys sorted_values
  in (sorted, stable)
