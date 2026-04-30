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
  in (reduce_comm op (false, nil) (zip (map p as) (iota n))).1

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
  tabulate n (\i -> lsb_diff color[i] succ[i])

-- | The different found in lsb_diff.
def bit (v: i64) (b: i8) : i8 =
  i8.i64 ((v >> i64.i8 b) & 1)

-- | Inverts a successor parent vector such that the pointer point in
-- the opposite direction.
def predecessor [n] (succ: [n]i64) : [n]i64 =
  scatter (rep nil) succ (iota n)

def logk_ruling_set_old [n] (h: i64) (succ: [n]i64) : ([n]i8, [n]bool) =
  let pred = predecessor succ
  let l = end succ
  let next i = if succ[i] == nil then h else succ[i]
  let prev i = if pred[i] == nil then l else pred[i]
  let color1 = tabulate n (\i -> lsb_diff i (next i))
  let is_local_min = tabulate n (\i -> color1[prev i] >= color1[i] && color1[i] <= color1[next i])
  let is_local_max = tabulate n (\i -> color1[prev i] <= color1[i] && color1[i] >= color1[next i])
  let selected =
    tabulate n (\i ->
                  let neighbor_is_local_min = is_local_min[prev i] || is_local_min[next i]
                  let coin = bit i color1[i]
                  in is_local_min[i] && ((not neighbor_is_local_min) || coin == 1))
  let available =
    tabulate n (\i ->
                  not selected[i]
                  && not selected[prev i]
                  && not selected[next i]
                  && is_local_max[i])
  let set =
    tabulate n (\i ->
                  let neighbor_is_available = available[prev i] || available[next i]
                  let coin = bit i color1[i]
                  in selected[i] || (available[i] && ((not neighbor_is_available) || coin == 1)))
  in (color1, set)

def logk_ruling_set_filter [n] (h: i64) (succ: [n]i64) : ([n]i8, [n]bool) =
  let pred = predecessor succ
  let l = end succ
  let next i = if succ[i] == nil then h else succ[i]
  let prev i = if pred[i] == nil then l else pred[i]
  let color1 = tabulate n (\i -> lsb_diff i (next i))
  let is_local_min = tabulate n (\i -> color1[prev i] >= color1[i] && color1[i] <= color1[next i])
  let is_local_max = tabulate n (\i -> color1[prev i] <= color1[i] && color1[i] >= color1[next i])
  let is_min_candidates =
    filter (.0) (zip is_local_min (iota n))
    |> map (.1)
  let is_max_candidates =
    filter (.0) (zip is_local_max (iota n))
    |> map (.1)
  let selected =
    map (\i ->
           let neighbor_is_local_min = is_local_min[prev i] || is_local_min[next i]
           let coin = bit i color1[i]
           in if (not neighbor_is_local_min) || coin == 1 then (i, true) else (-1, false))
        is_min_candidates
    |> unzip
    |> \(is, vs) -> scatter (replicate n false) is vs
  let available =
    map (\i ->
           if not selected[i]
              && not selected[prev i]
           && not selected[next i]
           then (i, true)
           else (-1, false))
        is_max_candidates
    |> unzip
    |> \(is, vs) -> scatter (replicate n false) is vs
  let set =
    tabulate n (\i ->
                  let neighbor_is_available = available[prev i] || available[next i]
                  let coin = bit i color1[i]
                  in selected[i] || (available[i] && ((not neighbor_is_available) || coin == 1)))
  in (color1, set)

def logk_ruling_set [n] (h: i64) (succ: [n]i64) : ([n]i8, [n]bool) =
  let next i = if succ[i] == nil then h else succ[i]
  let (colors, js_bools) =
    tabulate n (\i ->
                  let si = next i
                  let ssi = next si
                  let sssi = next ssi
                  let v = next sssi
                  let sv = next v
                  let ssv = next sv
                  -- colors computable from i..ssv
                  let c2ppppv = lsb_diff i si
                  let c2pppv = lsb_diff si ssi
                  let c2ppv = lsb_diff ssi sssi
                  let c2pv = lsb_diff sssi v
                  let c2v = lsb_diff v sv
                  let c2sv = lsb_diff sv ssv
                  -- ilm_v and ilmax_v are now fully determined
                  let ilm_v = c2pv >= c2v && c2v <= c2sv
                  let ilmax_v = c2pv <= c2v && c2v >= c2sv
                  in if !ilm_v && !ilmax_v
                     then -- sel_v=false, avail_v=false: no need to compute sssv..sssssv
                          (c2ppppv, (-1, false))
                     else let sssv = next ssv
                          let ssssv = next sssv
                          let sssssv = next ssssv
                          let c2ssv = lsb_diff ssv sssv
                          let c2sssv = lsb_diff sssv ssssv
                          let c2ssssv = lsb_diff ssssv sssssv
                          -- is_local_min
                          let ilm_pppv = c2ppppv >= c2pppv && c2pppv <= c2ppv
                          let ilm_ppv = c2pppv >= c2ppv && c2ppv <= c2pv
                          let ilm_pv = c2ppv >= c2pv && c2pv <= c2v
                          let ilm_sv = c2v >= c2sv && c2sv <= c2ssv
                          let ilm_ssv = c2sv >= c2ssv && c2ssv <= c2sssv
                          let ilm_sssv = c2ssv >= c2sssv && c2sssv <= c2ssssv
                          -- is_local_max
                          let ilmax_pv = c2ppv <= c2pv && c2pv >= c2v
                          let ilmax_sv = c2v <= c2sv && c2sv >= c2ssv
                          -- coins
                          let coin_ppv = bit ssi c2ppv
                          let coin_pv = bit sssi c2pv
                          let coin_v = bit v c2v
                          let coin_sv = bit sv c2sv
                          let coin_ssv = bit ssv c2ssv
                          -- selected for pred^2[v], pred[v], v
                          let sel_ppv = ilm_ppv && (!(ilm_pppv || ilm_pv) || coin_ppv == 1)
                          let sel_pv = ilm_pv && (!(ilm_ppv || ilm_v) || coin_pv == 1)
                          let sel_v = ilm_v && (!(ilm_pv || ilm_sv) || coin_v == 1)
                          in if sel_v
                             then -- no need to compute avail at all
                                  (c2ppppv, (v, true))
                             else let sel_sv = ilm_sv && (!(ilm_v || ilm_ssv) || coin_sv == 1)
                                  let sel_ssv = ilm_ssv && (!(ilm_sv || ilm_sssv) || coin_ssv == 1)
                                  let avail_pv = !sel_pv && !sel_ppv && !sel_v && ilmax_pv
                                  let avail_v = !sel_v && !sel_pv && !sel_sv && ilmax_v
                                  let avail_sv = !sel_sv && !sel_v && !sel_ssv && ilmax_sv
                                  in ( c2ppppv
                                     , if avail_v && (!(avail_pv || avail_sv) || coin_v == 1)
                                       then (v, true)
                                       else (-1, false)
                                     ))
    |> unzip
  let (js, bools) = unzip js_bools
  let bools = scatter (replicate n false) js bools
  in (colors, bools)

-- | Work efficient bucket sort with log n buckets, it does O(n) work
-- and has O(log n) span.
def logn_bucket_sort 'a [n] (keys: [n]i8) (values: [n]a) : ?[m].([m]i64, [n]i8, [n]a) =
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
  let exprefix_sum =
    counts
    |> scan (+) 0
    |> flip (map2 (-)) counts
  let js =
    map (\i -> if i % block_num == 0 then i / block_num else nil)
        (indices exprefix_sum)
  let seg_offsets =
    scatter (replicate block_size 0)
            js
            exprefix_sum
  let offsets =
    unflatten exprefix_sum
    |> transpose
  let flat_ranks = flatten ranks
  let is =
    tabulate n (\i ->
                  let block_id = i / block_size
                  in offsets[block_id][keys[i]] + i64.i8 flat_ranks[i])
  let sorted_keys = scatter (#[scratch] replicate n keys[0]) is keys
  let sorted_values = scatter (#[scratch] replicate n values[0]) is values
  let seg_offsets_is =
    #[sequential] filter (\i -> i == 0 || seg_offsets[i - 1] != seg_offsets[i]) (indices seg_offsets)
  let seg_offsets = map (\i -> seg_offsets[i]) seg_offsets_is
  in (seg_offsets, sorted_keys, sorted_values)

-- | Construct a 2-ruling set.
def two_ruling_set [n] (h: i64) (succ: [n]i64) : [n]bool =
  if n == 1
  then replicate n true
  else if n == 2
  then (replicate n false) with [h] = true
  else if n == 3
  then ((replicate n false) with [h] = true) with [succ[succ[h]]] = true
  else let next i = if succ[i] == nil then h else succ[i]
       -- Use logk_ruling_set for initial set, also recover color1 for bucket sort
       let (color1, set) = copy (logk_ruling_set h succ)
       -- Sort by color of successor: j becomes pred[v] where v = next j
       let (offsets, _, is) = logn_bucket_sort (map (\j -> color1[next j]) (iota n)) (iota n)
       let spans =
         indices offsets
         |> map (\i ->
                   if i == length offsets - 1
                   then (offsets[i], n)
                   else (offsets[i], offsets[i + 1]))
       let set =
         loop set
         for (start, end) in spans do
           let js = is[start:end]
           -- v = next j, so pred[v]=j and succ[v]=next(next j) are free — no pred array needed
           let flags = map (\j -> not set[j] && not set[next j] && not set[next (next j)]) js
           let set = scatter set (map2 (\f j -> if f then next j else nil) flags js) (rep true)
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
               if selected[pos] || succ[pos] == nil
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
  let (_, ruling_set) = logk_ruling_set h succ
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
  let (_, sorted_keys, sorted_values) = logn_bucket_sort keys values
  let sorted = is_sorted sorted_keys
  let stable = is_stable sorted_keys sorted_values
  in (sorted, stable)
