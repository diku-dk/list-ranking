import "common"

local
def gather [n] [m] (as: [n]i64) (is: [m]i64) : [m]i64 =
  map (\i -> if i == nil then nil else as[i]) is

local
def step [n] (rank: [n]i32) (succ: [n]i64) =
  let f i =
    if succ[i] == nil
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
  let temp = scatter (replicate n nil) active_before (indices active_before)
  let rank = rep 0
  let active_rank = map (const 1) active_before
  let active = gather succ active_before
  let (active_after, active_rank) =
    loop (active, active_rank)
    for _i < m do
      let (active, active_rank) =
        map2 (\r a ->
                if a == nil || selected[a]
                then (a, r)
                else (succ[a], r + 1))
             active_rank
             active
        |> unzip
      in (active, active_rank)
  let ruler_list =
    scatter (map (const nil) (indices active_after))
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
                if a == nil || selected[a]
                then (nil, r)
                else (a, r - 1))
             active_rank
             active
        |> unzip
      let rank = scatter rank active active_rank
      let active = gather succ active
      in (rank, active, active_rank)
  in rank

def blocked_list_ranking_filter [n] (selected: [n]bool) (succ: [n]i64) : [n]i32 =
  let active_before =
    zip selected (iota n)
    |> filter (.0)
    |> map (.1)
  let temp = scatter (replicate n nil) active_before (indices active_before)
  let rank = rep 0
  let active_rank = map (const 1) active_before
  let active = copy (gather succ active_before)
  let queue = zip3 active (map (const 1) active_before) (indices active_before)
  let (active_after, active_rank, _) =
    loop (active, active_rank, queue)
    while not (null queue) do
      let flags =
        map (\(a, _r, _i) -> not (a == nil || selected[a])) queue
      let offsets = scan (+) 0 (map i64.bool flags)
      let is = map2 (\f o -> if f then o - 1 else -1) flags offsets
      let js =
        map2 (\f (_a, _r, i) -> if f then -1 else i) flags queue
      let count =
        scatter [0]
                (map (\j -> if j == length queue - 1 then 0 else -1) (indices queue))
                offsets
      let active = scatter active js (map (.0) queue)
      let active_rank = scatter active_rank js (map (.1) queue)
      let queue =
        map2 (\f (a, r, i) -> if f then (succ[a], r + 1, i) else (a, r, i)) flags queue
        |> scatter (map (const (0, 0, 0)) queue) is
      in (active, active_rank, queue[:count[0]])
  let ruler_list =
    scatter (map (const nil) (indices active_after))
            (gather temp active_before)
            (gather temp active_after)
  let ruler_rank =
    scatter (map (const 0) active_after)
            (gather temp active_before)
            active_rank
  let ruler_rank = wyllie ruler_rank ruler_list
  let rank = scatter rank active_before ruler_rank
  let queue = zip (gather succ active_before) ruler_rank
  let (rank, _) =
    loop (rank, queue)
    while not (null queue) do
      let flags =
        map (\(a, _r) -> not (a == nil || selected[a])) queue
      let offsets = scan (+) 0 (map i64.bool flags)
      let is = map2 (\f o -> if f then o - 1 else -1) flags offsets
      let count =
        scatter [0]
                (map (\j -> if j == length queue - 1 then 0 else -1) (indices queue))
                offsets
      let queue = map2 (\f (a, r) -> if f then (a, r - 1) else (nil, 0)) flags queue
      let (active, active_rank) = unzip queue
      let rank = scatter rank active active_rank
      let queue =
        map (\(a, r) -> if a == nil then (a, r) else (succ[a], r)) queue
        |> scatter (map (const (nil, 0)) queue) is
      in (rank, queue[:count[0]])
  in rank
