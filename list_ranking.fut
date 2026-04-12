-- Therese Lyngby and Alba Lili Dekens have contributed significant work,
-- including the random mate and sequential implementations, as well as input
-- generation and testing.

import "blocked_list_ranking"
import "lib/github.com/diku-dk/cpprandom/random"
import "lib/github.com/diku-dk/sorts/radix_sort"
import "lib/github.com/diku-dk/cpprandom/shuffle"

def head [n] (S: [n]i64) : i64 =
  i64.sum (scatter (iota n) S (replicate n 0))

def ilog2 (x: i64) = 63 - i64.i32 (i64.clz x)

module type list_ranking = {
  val list_ranking [n] : (S: [n]i64) -> [n]i32
}

-- | Sequential reference implementation. Do not run this with the GPU backends,
-- as it will be monstrously slow.
module sequential : list_ranking = {
  def list_ranking [n] (S: [n]i64) =
    let (_, ranks) =
      loop (i, ranks) = (head S, (replicate n (i32.i64 n)))
      while S[i] != n do
        let j = S[i]
        let ranks[j] = ranks[i] - 1
        in (j, ranks)
    in ranks
}

-- | Wyllie's list ranking. Deterministic, but not work efficient.
module wyllie : list_ranking = {
  def step [n] (R: [n]i32) (S: [n]i64) =
    let f i =
      if S[i] == n
      then (R[i], S[i])
      else (R[i] + R[S[i]], S[S[i]])
    in unzip (tabulate n f)

  def list_ranking [n] (S: [n]i64) : [n]i32 =
    let R = replicate n 1
    let (R, _) =
      loop (R, S) for _i < 64 - i64.clz n do
        step R S
    in R
}

module rng_engine = minstd_rand
module rand_i8 = uniform_int_distribution i8 u32 rng_engine
module rand_i32 = uniform_int_distribution i32 u32 rng_engine
module shuffle = mk_shuffle u64 xorshift128plus

module random_mate_utils = {
  def hash (x: i32) : i32 =
    let x = u32.i32 x
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x)
    in i32.u32 x

  type sex = #F | #M

  #[inline]
  def bury_dead [k] [n]
                (t: i64)
                (dead: [k]i64)
                (removed: *[n]i64)
                (removed_offsets: *[]i64) : (*[n]i64, *[]i64) =
    let removed' =
      scatter removed (tabulate k (+ removed_offsets[t - 1])) dead
    let removed_offsets' =
      removed_offsets with [t] = k + removed_offsets[t - 1]
    in (removed', removed_offsets')

  -- note we have m <= n

  #[inline]
  def loop_body [n] [m]
                (R: *[n]i32)
                (S: *[n]i64)
                (t: i64)
                (active: [m]i64)
                (sexes: *[n]sex)
                (keep: *[n]bool)
                (removed: *[n]i64)
                (removed_offsets: *[]i64) : (*[n]i32, *[n]i64, i64, []i64, *[n]sex, *[n]bool, *[n]i64, *[]i64) =
    let sexes' =
      tabulate m (\i -> if hash (i32.i64 (i ^ t)) % 2 == 0 then #F else #M)
    let sexes' = scatter sexes active sexes'
    let update i =
      if S[i] == n
      then -- no update, remove inactive element
           (-1i64, i)
      else if sexes'[i] == #F && sexes'[S[i]] == #M
      then ( i
           , -- This might make dublicate indices in remove, but
             -- this should be ok since we always want to insert
             -- false in the scatter
             S[i]
           )
      else -- nothing became inactive
           (-1i64, -1i64)
    let (update_idx, rm_idx) = unzip (map update active)
    -- book keeping
    let R' =
      scatter R update_idx (map (\i -> if i == -1 then -1 else R[i] + R[S[i]]) update_idx)
    let S' =
      scatter S update_idx (map (\i -> if i == -1 then -1 else S[S[i]]) update_idx)
    let sexes' = scatter sexes' rm_idx (rep #M)
    -- calc. new active cells
    let keep' = scatter keep rm_idx (rep false)
    let (active', dead) = copy (partition (\i -> keep'[i]) active)
    -- Bury the dead (inactive cells) in the graveyard (removed)
    let (removed', removed_offsets') =
      bury_dead t dead removed removed_offsets
    in (R', S', t + 1i64, active', sexes', keep', removed', removed_offsets')
}

-- Random Mate as described in 'List ranking and parallel tree contraction' by
-- M. Reid-Miller, G. L. Miller, and F. Modugno, although with adaptations to
-- the data parallel model.
module random_mate : list_ranking = {
  open random_mate_utils

  def list_ranking [n] (S: [n]i64) : [n]i32 =
    let h = head S
    let R = replicate n 1i32
    let sexes = replicate n #M
    let active = iota n
    let keep = replicate n true
    let removed = replicate n (-1i64)
    let removed_offsets = replicate n 0
    let (R, S, t, _, _, _, removed, removed_offsets) =
      -- Pointer jumping phase
      loop (R, S, t, active, sexes, keep, removed, removed_offsets) =
             (R, copy S, 1i64, active, sexes, keep, removed, removed_offsets)
      while S[h] != n do
        loop_body R S t active sexes keep removed removed_offsets
    -- Reconstruction phase
    let n_rounds = t
    in loop R = copy R
       for t in n_rounds - 1..n_rounds - 2...1 do
         let RA_now = removed[removed_offsets[t - 1]:removed_offsets[t]]
         let updateR = map (\i -> if S[i] == n then R[i] else R[i] + R[S[i]]) RA_now
         in (scatter R RA_now updateR)
}

-- | A variant of Random Mate that shifts to using Wyllie's algorithm once a
-- certain threshold has been reached.
module random_mate_optim : list_ranking = {
  open random_mate_utils

  def modified_wyllie [n] [m] (R: *[n]i32) (S: *[n]i64) (active: [m]i64) : (*[n]i32, *[n]i64) =
    loop (R, S) for _i < 64 - i64.clz n do
      -- step
      let f i =
        if S[i] == n
        then (R[i], S[i])
        else (R[i] + R[S[i]], S[S[i]])
      let (R', S') = unzip (map f active)
      -- put our step
      in (scatter R active R', scatter S active S')

  def list_ranking [n] (S: [n]i64) : ([n]i32) =
    let h = head S
    let R = replicate n 1i32
    let sexes = replicate n #M
    let active = iota n
    let keep = replicate n true
    let removed = replicate n (-1i64)
    let removed_offsets = replicate n 0
    let cut_off = n / ilog2 n
    let (R, S, t, active, _, _, removed, removed_offsets) =
      -- Pointer jumping phase
      loop (R, S, t, active, sexes, keep, removed, removed_offsets) =
             (R, copy S, 1i64, active, sexes, keep, removed, removed_offsets)
      while S[h] != n && length active > cut_off do
        loop_body R S t active sexes keep removed removed_offsets
    --  might have to also get S post-wyllie
    let (R, S) = modified_wyllie R S active
    -- Reconstruction phase
    let n_rounds = t
    in loop R = copy R
       for t in n_rounds - 1..n_rounds - 2...1 do
         let RA_now = removed[removed_offsets[t - 1]:removed_offsets[t]]
         let updateR = map (\i -> if S[i] == n then R[i] else R[i] + R[S[i]]) RA_now
         in (scatter R RA_now updateR)
}

-- | Anderson/Miller list ranking. Deterministic and work efficient
-- but suboptimal implementation at this moment.
module work_efficient_suboptim : list_ranking = {
  def lsb_diff (a: i64) (b: i64) : i8 =
    if a == b
    then -1
    else a ^ b |> i64.ctz |> i8.i32

  def predecessor [n] (succ: [n]i64) : [n]i64 =
    scatter (rep n) succ (iota n)

  def init_color (n: i64) : [n]i64 = iota n

  def logn_coloring [n] (color: [n]i64) (succ: [n]i64) : [n]i8 =
    tabulate n (\i -> lsb_diff color[i] color[succ[i]])

  def bit (v: i64) (b: i8) : i8 =
    i8.i64 ((v >> i64.i8 b) & 1)

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

  def ceil_log2 x = i64.num_bits - i64.clz (x - 1)

  def ruling_set [n] (succ: [n]i64) : (i64, [n]bool) =
    let pred = predecessor succ
    let l_idx = find_index (== n) succ
    let h_idx = find_index (== n) pred
    let succ = copy succ with [l_idx] = h_idx
    let pred = copy pred with [h_idx] = l_idx
    let color0 = init_color n
    let color1 = logn_coloring color0 succ
    let is_local_min = tabulate n (\i -> color1[pred[i]] >= color1[i] && color1[i] <= color1[succ[i]])
    let is_local_max = tabulate n (\i -> color1[pred[i]] <= color1[i] && color1[i] >= color1[succ[i]])
    let selected =
      tabulate n (\i ->
                    let neighbor_is_local_min = is_local_min[pred[i]] || is_local_min[succ[i]]
                    let coin = bit color0[i] color1[i]
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
                    let coin = bit color0[i] color1[i]
                    in selected[i] || (available[i] && ((not neighbor_is_available) || coin == 1)))
    in (h_idx, selected')

  def list_ranking [n] (succ: [n]i64) : [n]i32 =
    if n == 0
    then [] :> [n]i32
    else let (h_idx, selected) = ruling_set succ
         let selected = map2 (\i s -> i == h_idx || s) (iota n) selected
         in blocked_list_ranking (ceil_log2 n) selected succ
}

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
  let lst[n - 1] = n
  in lst

def mk_test list_ranking S =
  let expected = wyllie.list_ranking S
  let res = list_ranking S
  in and (map2 (==) expected res)

-- ==
-- entry: sequential_test random_mate_test random_mate_optim_test work_efficient_suboptim_test
-- "n=100000,s=1"     compiled nobench script input { blocked_list 10000i64 1i64 }  output { true }
-- "n=100000,s=10"    compiled nobench script input { blocked_list 10000i64 10i64 } output { true }
-- "n=100000,s=100"   compiled nobench script input { blocked_list 10000i64 100i64 } output { true }
entry sequential_test = mk_test sequential.list_ranking
entry random_mate_test = mk_test random_mate.list_ranking
entry random_mate_optim_test = mk_test random_mate_optim.list_ranking
entry work_efficient_suboptim_test = mk_test work_efficient_suboptim.list_ranking

-- entry: sequential_bench
-- compiled notest script input { blocked_list 1000000i64 1i64 }
-- compiled notest script input { blocked_list 1000000i64 10i64 }
-- compiled notest script input { blocked_list 1000000i64 100i64 }
-- compiled notest script input { blocked_list 1000000i64 1000i64 }
-- compiled notest script input { blocked_list 1000000i64 10000i64 }
-- compiled notest script input { blocked_list 1000000i64 100000i64 }
-- compiled notest script input { blocked_list 1000000i64 1000000i64 }
entry sequential_bench = sequential.list_ranking

-- ==
-- entry: wyllie_bench random_mate_bench random_mate_optim_bench
-- compiled notest script input { blocked_list 100000000i64 1i64 }
-- compiled notest script input { blocked_list 100000000i64 10i64 }
-- compiled notest script input { blocked_list 100000000i64 100i64 }
-- compiled notest script input { blocked_list 100000000i64 1000i64 }
-- compiled notest script input { blocked_list 100000000i64 10000i64 }
-- compiled notest script input { blocked_list 100000000i64 100000i64 }
-- compiled notest script input { blocked_list 100000000i64 1000000i64 }
-- compiled notest script input { blocked_list 100000000i64 10000000i64 }
-- compiled notest script input { blocked_list 100000000i64 100000000i64 }
entry wyllie_bench = wyllie.list_ranking
entry random_mate_bench = random_mate.list_ranking
entry random_mate_optim_bench = random_mate_optim.list_ranking

entry average_stride [n] (S: [n]i64) =
  map2 (\i s -> f64.i64 (i64.abs (i - s))) (indices S) S
  |> f64.sum
  |> (/ f64.i64 n)
