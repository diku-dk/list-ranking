-- Therese Lyngby and Alba Lili Dekens have contributed significant work,
-- including the random mate and sequential implementations, as well as input
-- generation and testing.

import "lib/github.com/diku-dk/cpprandom/random"
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
module rand_i64 = uniform_int_distribution i64 u32 rng_engine
module shuffle = mk_shuffle u64 xorshift128plus

-- Random Mate as described in 'List ranking and parallel tree contraction' by
-- M. Reid-Miller, G. L. Miller, and F. Modugno, although with adaptations to
-- the data parallel model.
module random_mate : list_ranking = {
  type sex = #F | #M

  def bury_dead [k] [n]
                (t: i64)
                (dead: [k]i64)
                (removed: *[n]i64)
                (removed_offsets: []i64) : (*[n]i64, []i64) =
    let removed' =
      scatter removed (map (+ removed_offsets[t - 1]) (iota k)) dead
    let removed_offsets' = removed_offsets ++ [k + removed_offsets[t - 1]]
    in (removed', removed_offsets')

  -- note we have m <= n
  def loop_body [n] [m]
                (R: *[n]i32)
                (S: *[n]i64)
                (t: i64)
                (active: [m]i64)
                (sexes: *[n]sex)
                (keep: *[n]bool)
                (removed: *[n]i64)
                (removed_offsets: []i64) : (*[n]i32, *[n]i64, i64, []i64, *[n]sex, *[n]bool, *[n]i64, []i64) =
    -- originally in round
    let sexes_vals = [#F : sex, #M]
    -- 4243 and 731705 are carefully chosen constants.
    -- NEVER put a combination of even odd
    let sexes' = map (\i -> sexes_vals[((i + 1 + t) * 4243 + 713705) % 2]) (indices active)
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
      scatter R update_idx (map (\i -> if i == (-1i64) then -1i32 else R[i] + R[S[i]]) update_idx)
    let S' =
      scatter S update_idx (map (\i -> if i == (-1i64) then -1i64 else S[S[i]]) update_idx)
    let sexes' = scatter sexes' rm_idx (rep #M)
    -- calc. new active cells
    let keep' = scatter keep rm_idx (rep false)
    let (active', dead) = copy (partition (\i -> keep'[i]) active)
    -- Bury the dead (inactive cells) in the graveyard (removed)
    let (removed', removed_offsets') = bury_dead t dead removed removed_offsets
    in (R', S', t + 1i64, active', sexes', keep', removed', removed_offsets')

  def list_ranking [n] (S: [n]i64) : [n]i32 =
    let h = head S
    let R = replicate n 1i32
    let sexes = replicate n #M
    let active = iota n
    let keep = replicate n true
    let removed = replicate n (-1i64)
    let removed_offsets = [0]
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
  type sex = #F | #M

  def bury_dead [k] [n]
                (t: i64)
                (dead: [k]i64)
                (removed: *[n]i64)
                (removed_offsets: []i64) : (*[n]i64, []i64) =
    let removed' =
      scatter removed (map (+ removed_offsets[t - 1]) (iota k)) dead
    let removed_offsets' = removed_offsets ++ [k + removed_offsets[t - 1]]
    in (removed', removed_offsets')

  -- note we have m <= n
  def og_loop_body [n] [m]
                   (R: *[n]i32)
                   (S: *[n]i64)
                   (t: i64)
                   (active: [m]i64)
                   (sexes: *[n]sex)
                   (keep: *[n]bool)
                   (removed: *[n]i64)
                   (removed_offsets: []i64) : (*[n]i32, *[n]i64, i64, []i64, *[n]sex, *[n]bool, *[n]i64, []i64) =
    -- originally in round
    let sexes_vals = [#F : sex, #M]
    -- 4243 and 731705 are carefully chosen constants.
    -- NEVER put a combination of even odd
    let sexes' = map (\i -> sexes_vals[((i + 1 + t) * 4243 + 713705) % 2]) (indices active)
    let sexes' = scatter sexes active sexes'
    let update i =
      if S[i] == n
      then -- no update, remove inactive element
           (R[i], S[i], i)
      else if sexes'[i] == #F && sexes'[S[i]] == #M
      then ( R[i] + R[S[i]]
           , S[S[i]]
           , -- This might make dublicate indices in remove, but
             -- this should be ok since we always want to insert
             -- false in the scatter
             S[i]
           )
      else -- nothing became inactive
           (R[i], S[i], -1i64)
    let (R', S', rm_idx) = unzip3 (map update active)
    -- book keeping
    let R' =
      scatter R active R'
    let S' =
      scatter S active S'
    let sexes' = scatter sexes' rm_idx (rep #M)
    -- calc. new active cells
    let keep' = scatter keep rm_idx (rep false)
    let (active', dead) = copy (partition (\i -> keep'[i]) active)
    -- Bury the dead (inactive cells) in the graveyard (removed)
    let (removed', removed_offsets') = bury_dead t dead removed removed_offsets
    in (R', S', t + 1i64, active', sexes', keep', removed', removed_offsets')

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
    let removed_offsets = [0]
    let cut_off = n / ilog2 n
    let (R, S, t, active, _, _, removed, removed_offsets) =
      -- Pointer jumping phase
      loop (R, S, t, active, sexes, keep, removed, removed_offsets) =
             (R, copy S, 1i64, active, sexes, keep, removed, removed_offsets)
      while S[h] != n && length active > cut_off do
        og_loop_body R S t active sexes keep removed removed_offsets
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

entry generate_list (n: i64) (seed: i32) : [n]i64 =
  let rng = rng_engine.rng_from_seed [seed]
  let rng' = xorshift128plus.rng_from_seed [seed]
  let (_, h) = rand_i64.rand (0i64, (n - 1)) rng
  let (_, tmp) = shuffle.shuffle rng' (iota n)
  let (idx, S) = zip tmp (rotate 1 tmp) |> unzip
  let lst = scatter (replicate n 0) idx S
  let lst[h] = n
  in lst

def mk_test list_ranking S =
  let expected = wyllie.list_ranking S
  let res = list_ranking S
  in and (map2 (==) expected res)

-- ==
-- entry: sequential_test random_mate_test random_mate_optim_test
-- "n=10"     compiled nobench script input { generate_list 10i64 13632i32 } output { true }
-- "n=100"    compiled nobench script input { generate_list 100i64 13632i32 } output { true }
-- "n=1000"   compiled nobench script input { generate_list 1000i64 13632i32 } output { true }
-- "n=10000"  compiled nobench script input { generate_list 10000i64 13632i32 } output { true }
-- "n=100000" compiled nobench script input { generate_list 100000i64 13632i32 } output { true }
entry sequential_test = mk_test sequential.list_ranking
entry random_mate_test = mk_test random_mate.list_ranking
entry random_mate_optim_test = mk_test random_mate_optim.list_ranking

-- ==
-- entry: sequential_bench
-- "n=10"      compiled notest no_cuda no_opencl no_hip script input { generate_list 10i64 13632i32 }
-- "n=100"     compiled notest no_cuda no_opencl no_hip script input { generate_list 100i64 13632i32 }
-- "n=1000"    compiled notest no_cuda no_opencl no_hip script input { generate_list 1000i64 13632i32 }
-- "n=10000"   compiled notest no_cuda no_opencl no_hip script input { generate_list 10000i64 13632i32 }
-- "n=100000"  compiled notest no_cuda no_opencl no_hip script input { generate_list 100000i64 13632i32 }
-- "n=1000000" compiled notest no_cuda no_opencl no_hip script input { generate_list 1000000i64 13632i32 }
entry sequential_bench = sequential.list_ranking

-- ==
-- entry: wyllie_bench random_mate_bench random_mate_optim_bench
-- "n=10"        compiled notest script input { generate_list 10i64 13632i32 }
-- "n=100"       compiled notest script input { generate_list 100i64 13632i32 }
-- "n=1000"      compiled notest script input { generate_list 1000i64 13632i32 }
-- "n=10000"     compiled notest script input { generate_list 10000i64 13632i32 }
-- "n=100000"    compiled notest script input { generate_list 100000i64 13632i32 }
-- "n=1000000"   compiled notest script input { generate_list 1000000i64 13632i32 }
-- "n=10000000"  compiled notest script input { generate_list 10000000i64 13632i32 }
-- "n=100000000" compiled notest script input { generate_list 100000000i64 13632i32 }
entry wyllie_bench = wyllie.list_ranking
entry random_mate_bench = random_mate.list_ranking
entry random_mate_optim_bench = random_mate_optim.list_ranking
