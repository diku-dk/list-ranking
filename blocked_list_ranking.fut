local
def ceil_log2 x = i64.num_bits - i64.clz (x - 1)

local
def gather [n] [m] (as: [n]i64) (is: [m]i64) : [m]i64 =
  map (\i -> if i == -1 then -1 else as[i]) is

local
def step [n] (rank: [n]i32) (succ: [n]i64) =
  let f i =
    if succ[i] == -1
    then (rank[i], succ[i])
    else (rank[i] + rank[succ[i]], succ[succ[i]])
  in unzip (tabulate n f)

local
def wyllie [n] (rank: [n]i32) (succ: [n]i64) : [n]i32 =
  let (rank, _) =
    loop (rank, succ) for _i < i64.num_bits - i64.clz n do
      step rank succ
  in rank

def blocked_list_ranking [n] (m: i64) (selected: [n]bool) (succ: [n]i64) : [n]i32 =
  let active_before =
    zip selected (iota n)
    |> filter (.0)
    |> map (.1)
  let temp = scatter (replicate n (-1)) active_before (indices active_before)
  let rank = rep 0
  let active_rank = map (const 1) active_before
  let active = gather succ active_before
  let (active_after, active_rank) =
    loop (active, active_rank)
    for _i < m do
      let (active, active_rank) =
        map2 (\r a ->
                if a == -1 || selected[a]
                then (a, r)
                else (succ[a], r + 1))
             active_rank
             active
        |> unzip
      in (active, active_rank)
  let ruler_list =
    scatter (map (const (-1)) (indices active_after))
            (gather temp active_before)
            (gather temp active_after)
  let ruler_rank =
    scatter (map (const 0) active_after)
            (gather temp active_before)
            active_rank
  let ruler_rank = wyllie ruler_rank ruler_list
  let rank = scatter rank active_before ruler_rank
  let active_rank = ruler_rank
  let active = gather succ active_before
  let (rank, _, _) =
    loop (rank, active, active_rank)
    for _i < m do
      let (active, active_rank) =
        map2 (\r a ->
                if a == -1 || selected[a]
                then (-1, r)
                else (a, r - 1))
             active_rank
             active
        |> unzip
      let rank = scatter rank active active_rank
      let active = gather succ active
      in (rank, active, active_rank)
  in map (+ (-1)) rank
