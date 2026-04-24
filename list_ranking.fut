-- Therese Lyngby and Alba Lili Dekens have contributed significant work,
-- including the random mate and sequential implementations, as well as input
-- generation and testing.

import "blocked_list_ranking"
import "common"

module type list_ranking = {
  val list_ranking [n] : (h: i64) -> (S: [n]i64) -> [n]i32
}

-- | Sequential reference implementation. Do not run this with the GPU backends,
-- as it will be monstrously slow.
module sequential : list_ranking = {
  def list_ranking [n] (h: i64) (S: [n]i64) =
    let (_, ranks) =
      loop (i, ranks) = (h, (replicate n (i32.i64 n)))
      while S[i] != nil do
        let j = S[i]
        let ranks[j] = ranks[i] - 1
        in (j, ranks)
    in ranks
}

-- | Wyllie's list ranking. Deterministic, but not work efficient.
module wyllie : list_ranking = {
  def step [n] (R: [n]i32) (S: [n]i64) =
    let f i =
      if S[i] == nil
      then (R[i], S[i])
      else (R[i] + R[S[i]], S[S[i]])
    in unzip (tabulate n f)

  def list_ranking [n] (_: i64) (S: [n]i64) : [n]i32 =
    let R = replicate n 1
    let (R, _) =
      loop (R, S) for _i < ceil_log2 n do
        step R S
    in R
}

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
      if S[i] == nil
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

  def list_ranking [n] (h: i64) (S: [n]i64) : [n]i32 =
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
      while S[h] != nil do
        loop_body R S t active sexes keep removed removed_offsets
    -- Reconstruction phase
    let n_rounds = t
    in loop R = copy R
       for t in n_rounds - 1..n_rounds - 2...1 do
         let RA_now = removed[removed_offsets[t - 1]:removed_offsets[t]]
         let updateR = map (\i -> if S[i] == nil then R[i] else R[i] + R[S[i]]) RA_now
         in (scatter R RA_now updateR)
}

module type state = {
  type^ s
  val get_rulers [n] : (t: i64) -> (h: i64) -> (succ: [n]i64) -> *s
  val is_ruler : s -> i64 -> bool
}

module list_ranking_independent_set (S: state) : list_ranking = {
  type^ s = S.s

  #[inline]
  def is_ruler = S.is_ruler

  #[inline]
  def get_rulers = S.get_rulers

  def gather [n] [m] 'a (as: [n]a) (is: [m]i64) =
    map (\i -> as[i]) is

  #[inline]
  def loop_body [n] [m]
                (rank: *[m]i32)
                (succ: *[m]i64)
                (is: *[m]i64)
                (final_rank: *[n]i32)
                (final_succ: *[n]i64)
                (h: i64)
                (t: i64)
                (removed: *[n]i64)
                (removed_offsets: *[]i64) : ?[k].(*[k]i32, *[k]i64, *[k]i64, *[n]i32, *[n]i64, i64, i64, *[n]i64, *[]i64) =
    if 10000 < t
    then assert false (rank, succ, is, final_rank, final_succ, h, t + 1i64, removed, removed_offsets)
    else if length succ == 1
    then let final_rank[is[0]] = rank[0]
         in ([], [], [], final_rank, final_succ, h, t, removed, removed_offsets)
    else let state = get_rulers t h succ
         let active = tabulate m (is_ruler state)
         let update i a r s =
           if succ[i] == nil
           then (r, s, nil)
           else if a
           then (rank[i] + rank[succ[i]], succ[succ[i]], succ[i])
           else (r, s, nil)
         let (rank, succ, remove) = unzip3 (map4 update (iota m) active rank succ)
         let keep = scatter (replicate m true) remove (rep false)
         let (active, dead) = copy (partition (\i -> keep[i]) (iota m))
         let dead_is = gather is dead
         let removed_is = map (+ removed_offsets[t - 1]) (indices dead)
         let removed = scatter removed removed_is dead_is
         let dead_rank = gather rank dead
         let final_rank = scatter final_rank dead_is dead_rank
         let dead_succ =
           map (\a -> if succ[a] == nil then nil else is[succ[a]]) dead
         let final_succ = scatter final_succ dead_is dead_succ
         let removed_offsets =
           if length removed_offsets == t
           then let removed_offsets = removed_offsets ++ map (const 0) removed_offsets
                in removed_offsets with [t] = length dead + removed_offsets[t - 1]
           else removed_offsets with [t] = length dead + removed_offsets[t - 1]
         let compressed = scatter (replicate m nil) active (indices active)
         let succ = map (\a -> if succ[a] == nil then nil else compressed[succ[a]]) active
         let is = gather is active
         let rank = gather rank active
         let h = compressed[h]
         in (rank, succ, is, final_rank, final_succ, h, t + 1i64, removed, removed_offsets)

  def list_ranking [n] (h: i64) (succ: [n]i64) : [n]i32 =
    let rank = replicate n 1i32
    let removed = replicate n (-1i64)
    let removed_offsets = replicate 128 0
    let (_, _, _, rank, succ, _, t_rounds, removed, removed_offsets) =
      loop (rank, succ, is, final_rank, final_succ, h, t, removed, removed_offsets) =
             (copy rank, copy succ, (iota n), rank, copy succ, h, 1i64, removed, removed_offsets)
      while not (null succ) do
        loop_body rank succ is final_rank final_succ h t removed removed_offsets
    in loop rank
       for t in t_rounds - 1..t_rounds - 2...1 do
         let is = removed[removed_offsets[t - 1]:removed_offsets[t]]
         let rs = map (\i -> if succ[i] == nil then rank[i] else rank[i] + rank[succ[i]]) is
         in scatter rank is rs
}

module random_mate_state : state = {
  type^ s = ?[n].[n]bool
  def is_ruler [n] (s: [n]bool) (i: i64) : bool = s[i]

  def hash (x: i32) : i32 =
    let x = u32.i32 x
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x)
    in i32.u32 x

  def get_rulers [n] (t: i64) (_: i64) (succ: [n]i64) : *[n]bool =
    let flip i = hash (i32.i64 (i ^ t)) % 2 == 0
    in map (\i ->
              flip i && not (flip succ[i]))
           (indices succ)
}

module random_mate_example : list_ranking =
  list_ranking_independent_set random_mate_state

module cole_vishkin_state : state = {
  type^ s = ?[n].[n]bool
  def is_ruler [n] (s: [n]bool) (i: i64) : bool = s[i]

  def get_rulers [n] (_: i64) (h: i64) (succ: [n]i64) : *[n]bool =
    two_ruling_set h (copy succ)
}

module cole_vishkin : list_ranking =
  list_ranking_independent_set cole_vishkin_state

-- | A variant of Random Mate that shifts to using Wyllie's algorithm once a
-- certain threshold has been reached.
module random_mate_optim : list_ranking = {
  open random_mate_utils

  def modified_wyllie [n] [m] (R: *[n]i32) (S: *[n]i64) (active: [m]i64) : (*[n]i32, *[n]i64) =
    loop (R, S) for _i < 64 - i64.clz n do
      -- step
      let f i =
        if S[i] == nil
        then (R[i], S[i])
        else (R[i] + R[S[i]], S[S[i]])
      let (R', S') = unzip (map f active)
      -- put our step
      in (scatter R active R', scatter S active S')

  def list_ranking [n] (h: i64) (S: [n]i64) : ([n]i32) =
    let R = replicate n 1i32
    let sexes = replicate n #M
    let active = iota n
    let keep = replicate n true
    let removed = replicate n (-1i64)
    let removed_offsets = replicate n 0
    let cut_off = n / floor_log2 n
    let (R, S, t, active, _, _, removed, removed_offsets) =
      -- Pointer jumping phase
      loop (R, S, t, active, sexes, keep, removed, removed_offsets) =
             (R, copy S, 1i64, active, sexes, keep, removed, removed_offsets)
      while S[h] != nil && length active > cut_off do
        loop_body R S t active sexes keep removed removed_offsets
    --  might have to also get S post-wyllie
    let (R, S) = modified_wyllie R S active
    -- Reconstruction phase
    let n_rounds = t
    in loop R = copy R
       for t in n_rounds - 1..n_rounds - 2...1 do
         let RA_now = removed[removed_offsets[t - 1]:removed_offsets[t]]
         let updateR = map (\i -> if S[i] == nil then R[i] else R[i] + R[S[i]]) RA_now
         in (scatter R RA_now updateR)
}

def mk_test list_ranking h S =
  let expected = wyllie.list_ranking h S
  let res = list_ranking h S
  in and (map2 (==) expected res)

entry blocked_list = blocked_list

-- ==
-- entry: sequential_test random_mate_test random_mate_optim_test random_mate_example_test cole_vishkin_test
-- "n=100000,s=1"     compiled nobench script input { blocked_list 10000i64 1i64 }  output { true }
-- "n=100000,s=10"    compiled nobench script input { blocked_list 10000i64 10i64 } output { true }
-- "n=100000,s=100"   compiled nobench script input { blocked_list 10000i64 100i64 } output { true }

entry sequential_test = mk_test sequential.list_ranking
entry random_mate_test = mk_test random_mate.list_ranking
entry random_mate_optim_test = mk_test random_mate_optim.list_ranking
entry random_mate_example_test = mk_test random_mate_example.list_ranking
entry cole_vishkin_test = mk_test cole_vishkin.list_ranking

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
-- entry: wyllie_bench random_mate_bench random_mate_optim_bench random_mate_example_bench cole_vishkin_bench
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
entry random_mate_example_bench = random_mate_example.list_ranking
entry random_mate_bench = random_mate.list_ranking
entry random_mate_optim_bench = random_mate_optim.list_ranking
entry cole_vishkin_bench = cole_vishkin.list_ranking

entry average_stride [n] (S: [n]i64) =
  map2 (\i s -> f64.i64 (i64.abs (i - s))) (indices S) S
  |> f64.sum
  |> (/ f64.i64 n)
