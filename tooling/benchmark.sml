val program = "list_ranking.fut"
val spec_file_name = "list_ranking.spec"
val json_file_name = "list_ranking.json"

val unwords = concat o map (fn x => x ^ " ")
val unlines = concat o map (fn x => x ^ "\n")

fun linspace (k: int, a: real, b: real) : real list =
  if k <= 1 then
    [a]
  else
    let
      val step = (b - a) / Real.fromInt (k - 1)
      fun value i =
        a + step * Real.fromInt i
    in
      List.tabulate (k, value)
    end

fun logspace (k: int, a: real, b: real) : real list =
  let
    val ratio = b / a
    fun value i =
      a * Math.pow (ratio, Real.fromInt i / Real.fromInt (k - 1))
  in
    List.tabulate (k, value)
  end

fun workloadName n B =
  "n=" ^ Int.toString n ^ ",B=" ^ Int.toString B

fun generateNs min_n max_n k =
  map Real.round (linspace (k, real min_n, real max_n))

fun generateBs n k =
  map Real.round (logspace (k, 1.0, real n))

fun generateSpec entry_points ns k =
  let
    fun mk_case n B =
      "\"" ^ workloadName n B ^ "\" script input { blocked_list "
      ^ Int.toString n ^ "i64 " ^ Int.toString B ^ " }"
  in
    unlines
      (["==", "entry: " ^ unwords entry_points]
       @ List.concat (map (fn n => map (mk_case n) (generateBs n k)) ns))
  end

fun writeFile fname s =
  let val f = TextIO.openOut fname
  in TextIO.output (f, s) before TextIO.closeOut f
  end

fun writeSpecFile entry_points ns k =
  writeFile spec_file_name (generateSpec entry_points ns k)

local
  fun lookArray obj k =
    case Json.objLook obj k of
      SOME (Json.ARRAY l) => l
    | _ => raise Fail ("Missing key: " ^ k)

  fun lookObj obj k =
    case Json.objLook obj k of
      SOME (Json.OBJECT obj) => obj
    | _ => raise Fail ("Missing key: " ^ k)

  fun realFromJSON (Json.NUMBER s) =
        (case Real.fromString s of
           SOME x => x
         | _ => raise Fail ("Cannot parse as number: " ^ s))
    | realFromJSON _ = raise Fail "Expected number"

  fun mean xs =
    foldl op+ 0.0 xs / real (length xs)
in
  fun resultsForAlgorithm (Json.OBJECT obj) ns k entry_point =
        let
          val datasets =
            lookObj (lookObj obj (program ^ ":" ^ entry_point)) "datasets"
        in
          map
            (fn n =>
               (map
                  (fn B =>
                     (mean (map realFromJSON
                        (lookArray (lookObj datasets (workloadName n B))
                           "runtimes")))) (generateBs n k))) ns
        end
    | resultsForAlgorithm _ _ _ _ = raise Fail "Invalid JSON"
end

val backend_opt: string ref = ref "cuda"
val k_opt: int ref = ref 15
val min_n_opt: int ref = ref 100000
val max_n_opt: int ref = ref 100000000

fun options () : unit GetOpt.opt_descr list =
  [ { short = []
    , long = ["backend"]
    , arg = GetOpt.REQ_ARG (fn s => backend_opt := s, "BACKEND")
    , desc = "Set Futhark backend."
    }
  , { short = [#"k"]
    , long = []
    , arg = GetOpt.REQ_ARG
        ( fn s =>
            k_opt
            :=
            (case Int.fromString s of
               SOME x => x
             | _ => raise Fail "Invalid -k")
        , "Number of block sizes"
        )
    , desc = "Set experiment scale"
    }
  , { short = []
    , long = ["max-n"]
    , arg = GetOpt.REQ_ARG
        ( fn s =>
            max_n_opt
            :=
            (case Int.fromString s of
               SOME x => x
             | _ => raise Fail "Invalid --max-n")
        , "Maximal value of n"
        )
    , desc = "Set maximal input size"
    }
  , { short = []
    , long = ["min-n"]
    , arg = GetOpt.REQ_ARG
        ( fn s =>
            min_n_opt
            :=
            (case Int.fromString s of
               SOME x => x
             | _ => raise Fail "Invalid --max-n")
        , "Minimal value of n"
        )
    , desc = "Set minimum input size"
    }
  ]
and usage () =
  "Usage: benchmark [OPTIONS]\n" ^ GetOpt.usage (options ())

fun err s = TextIO.output (TextIO.stdErr, s)

fun generateTable baseline competitor =
  let
    fun cell (x, y) =
      Real.toString (x / y)
    fun row (n_baseline, n_competitor) =
      unwords (ListPair.map cell (n_baseline, n_competitor))
  in
    unlines (ListPair.map row (baseline, competitor))
  end

fun main () =
  case GetOpt.getopt GetOpt.PERMUTE (options ()) (CommandLine.arguments ()) of
    (_, _, []) =>
      let
        val k = !k_opt
        val ns = generateNs (!min_n_opt) (!max_n_opt) k
        val entry_points = ["wyllie_bench", "random_mate_bench"]
        val baseline_entry_point = hd entry_points
        val () = writeSpecFile entry_points ns k
        val status = OS.Process.system
          ("futhark bench" ^ " " ^ program ^ " --backend=" ^ !backend_opt
           ^ " --spec-file=" ^ spec_file_name ^ " --json=" ^ json_file_name)
        val () =
          if not (OS.Process.isSuccess status) then OS.Process.exit status
          else ()
        val benchmark_results = Json.fromString
          (TextIO.inputAll (TextIO.openIn json_file_name))
        val entry_point_results =
          map (resultsForAlgorithm benchmark_results ns k) entry_points
        val baseline_results = hd entry_point_results
        val () =
          writeFile "random_mate.speedups" (generateTable baseline_results
            (List.nth (entry_point_results, 1)))
      in
        ()
      end
  | (_, _, errors) =>
      (List.app err errors; err (usage ()); OS.Process.exit OS.Process.failure)


val () = main ()
