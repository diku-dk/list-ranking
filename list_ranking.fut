-- Therese Lyngby and Alba Lili Dekens have contributed significant work,
-- including the random mate and sequential implementations, as well as input
-- generation and testing.

import "lib/github.com/diku-dk/containers/bitset"
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

-- | Module for computing independent sets of lists.
--
-- A independent set is a set of nodes from the list that have no
-- edges in common.
module type independent_set = {
  -- | The type of the set.
  type^ s

  -- | Construction of a independent set from a time stamp, head node,
  -- and a parent vector.
  val get_independent_set [n] : (t: i64) -> (h: i64) -> (succ: [n]i64) -> *s

  --| Check if a node of the list is a member in the independent set.
  val is_member : s -> i64 -> bool

  -- | Check if the list is smalle enough to default to wyllies list
  -- ranking algorithm. The arguments given is the current list length
  -- and the list length originally.
  val is_base_case : i64 -> i64 -> bool
}

-- | Given a module for constructing a independent set create a list
-- ranking module.
module list_ranking_independent_set (S: independent_set) : list_ranking = {
  type^ s = S.s

  #[inline]
  def get_independent_set = S.get_independent_set

  #[inline]
  def is_member = S.is_member

  #[inline]
  def is_base_case = S.is_base_case

  #[gather]
  def gather [n] [m] 'a (as: [n]a) (is: [m]i64) =
    map (\i -> as[i]) is

  #[inline]
  def step [n] (R: [n]i32) (S: [n]i64) =
    let f i =
      if S[i] == nil
      then (R[i], S[i])
      else (R[i] + R[S[i]], S[S[i]])
    in unzip (tabulate n f)

  #[inline]
  def wyllie_list_ranking [n] (_: i64) (R: [n]i32) (S: [n]i64) : [n]i32 =
    let (R, _) =
      loop (R, S) for _i < ceil_log2 n do
        step R S
    in R

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
    if is_base_case m n
    then let wyllie_rank = wyllie_list_ranking h rank succ
         let final_rank = scatter final_rank is wyllie_rank
         in ([], [], [], final_rank, final_succ, h, t, removed, removed_offsets)
    else if length succ == 1
    then let final_rank[is[0]] = rank[0]
         in ([], [], [], final_rank, final_succ, h, t, removed, removed_offsets)
    else let set = get_independent_set t h succ
         let active = tabulate m (is_member set)
         let update i a r s =
           if succ[i] == nil
           then (r, s, nil)
           else if a
           then (rank[i] + rank[succ[i]], succ[succ[i]], succ[i])
           else (r, s, nil)
         let (rank, succ, remove) = unzip3 (map4 update (iota m) active rank succ)
         let keep = bitset.from_array m remove
         let (active, dead) = partition (\i -> not (bitset.member i keep)) (iota m)
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

-- | A module for performing random mate.
module random_mate_state (B: {val is_base_case : i64 -> i64 -> bool}) : independent_set = {
  type^ s = ?[n].[n]bool
  def is_member [n] (s: [n]bool) (i: i64) : bool = s[i]
  def is_base_case = B.is_base_case

  def hash (x: i32) : i32 =
    let x = u32.i32 x
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x) * 0x45d9f3b
    let x = ((x >> 16) ^ x)
    in i32.u32 x

  def get_independent_set [n] (t: i64) (_: i64) (succ: [n]i64) : *[n]bool =
    let flip i = hash (i32.i64 (i ^ t)) % 2 == 0
    in map (\i ->
              flip i && not (flip succ[i]))
           (indices succ)
}

module random_mate : list_ranking =
  list_ranking_independent_set (random_mate_state {def is_base_case _ _ = false})

module random_mate_bounded : list_ranking =
  list_ranking_independent_set (random_mate_state {def is_base_case m n = m < n / floor_log2 n})

-- | A module for performing Cole/Vishkin's list ranking algorithm.
module cole_vishkin_state (B: {val is_base_case : i64 -> i64 -> bool}) : independent_set = {
  type^ s = ?[n].[n]bool
  def is_member [n] (s: [n]bool) (i: i64) : bool = s[i]
  def is_base_case = B.is_base_case

  def get_independent_set [n] (_: i64) (h: i64) (succ: [n]i64) : *[n]bool =
    two_ruling_set h (copy succ)
}

module cole_vishkin : list_ranking =
  list_ranking_independent_set (cole_vishkin_state {def is_base_case _ _ = false})

module cole_vishkin_bounded : list_ranking =
  list_ranking_independent_set (cole_vishkin_state {def is_base_case m n = m < n / floor_log2 n})

def mk_test list_ranking h S =
  let expected = wyllie.list_ranking h S
  let res = list_ranking h S
  in and (map2 (==) expected res)

entry blocked_list = blocked_list

-- ==
-- entry: sequential_test random_mate_test random_mate_bounded_test cole_vishkin_test cole_vishkin_bounded_test
-- "n=100000,s=1"     compiled nobench script input { blocked_list 10000i64 1i64 }  output { true }
-- "n=100000,s=10"    compiled nobench script input { blocked_list 10000i64 10i64 } output { true }
-- "n=100000,s=100"   compiled nobench script input { blocked_list 10000i64 100i64 } output { true }

entry sequential_test = mk_test sequential.list_ranking
entry random_mate_test = mk_test random_mate.list_ranking
entry random_mate_bounded_test = mk_test random_mate_bounded.list_ranking
entry cole_vishkin_test = mk_test cole_vishkin.list_ranking
entry cole_vishkin_bounded_test = mk_test cole_vishkin_bounded.list_ranking

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
-- entry: wyllie_bench random_mate_bench random_mate_bounded_bench cole_vishkin_bench cole_vishkin_bounded_bench
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
entry random_mate_bounded_bench = random_mate_bounded.list_ranking
entry cole_vishkin_bench = cole_vishkin.list_ranking
entry cole_vishkin_bounded_bench = cole_vishkin_bounded.list_ranking

entry average_stride [n] (S: [n]i64) =
  map2 (\i s -> f64.i64 (i64.abs (i - s))) (indices S) S
  |> f64.sum
  |> (/ f64.i64 n)
