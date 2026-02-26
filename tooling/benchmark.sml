val program = "list_ranking.fut"
val spec_file_name = "list_ranking.spec"
val json_file_name = "list_ranking.json"

val unwords = concat o map (fn x => x ^ " ")
val unlines = concat o map (fn x => x ^ "\n")

fun logspace (k: int, n: int) : real list =
  let
    fun value i =
      Math.pow (real n, Real.fromInt i / Real.fromInt (k - 1))
  in
    List.tabulate (k, value)
  end

fun workloadName n B =
  "n=" ^ Int.toString n ^ ",B=" ^ Int.toString B

fun generateBs n k =
  map Real.round (logspace (k, n))

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

fun writeSpecFile entry_points ns k =
  let
    val spec = generateSpec entry_points ns k
    val f = TextIO.openOut spec_file_name
  in
    TextIO.output (f, spec) before TextIO.closeOut f
  end

local
  fun stringFromJSON (Json.STRING s) = s
    | stringFromJSON _ = raise Fail "Not a string"

  fun lookBool obj k =
    case Json.objLook obj k of
      SOME (Json.BOOL b) => b
    | _ => raise Fail ("Missing key: " ^ k)

  fun lookInt obj k =
    case Json.objLook obj k of
      SOME (Json.NUMBER s) =>
        (case Int.fromString s of
           SOME x => x
         | NONE => raise Fail ("Not an int: " ^ s))
    | _ => raise Fail ("Missing key: " ^ k)

  fun lookString obj k =
    case Json.objLook obj k of
      SOME (Json.STRING s) => s
    | _ => raise Fail ("Missing key: " ^ k)

  fun lookArray obj k =
    case Json.objLook obj k of
      SOME (Json.ARRAY l) => l
    | _ => raise Fail ("Missing key: " ^ k)

  fun lookObj obj k =
    case Json.objLook obj k of
      SOME (Json.OBJECT obj) => obj
    | _ => raise Fail ("Missing key: " ^ k)

  fun mustBeReal (Json.NUMBER s) =
        (case Real.fromString s of
           SOME x => x
         | _ => raise Fail ("Cannot parse as number: " ^ s))
    | mustBeReal _ = raise Fail "Expected number"

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
               ( n
               , map
                   (fn B =>
                      ( B
                      , mean (map mustBeReal
                          (lookArray (lookObj datasets (workloadName n B))
                             "runtimes"))
                      )) (generateBs n k)
               )) ns
        end
    | resultsForAlgorithm _ _ _ _ = raise Fail "Invalid JSON"
end

val backend_opt: string ref = ref "cuda"

fun options () : unit GetOpt.opt_descr list =
  [{ short = []
   , long = ["backend"]
   , arg = GetOpt.REQ_ARG (fn s => backend_opt := s, "BACKEND")
   , desc = "Set Futhark backend."
   }]
and usage () =
  "Usage: smlfut [OPTIONS] MANIFEST.json\n" ^ GetOpt.usage (options ())

fun err s = TextIO.output (TextIO.stdErr, s)

fun main () =
  case GetOpt.getopt GetOpt.PERMUTE (options ()) (CommandLine.arguments ()) of
    (_, _, []) =>
      let
        val ns = [10000, 100000, 1000000]
        val k = 10
        val entry_points = ["wyllie_bench", "random_mate_bench"]
        val () = writeSpecFile entry_points ns k
        (*
        val status = OS.Process.system
        ("futhark bench" ^ " " ^ program ^ " --backend=" ^ !backend_opt
        ^ " --spec-file=" ^ spec_file_name ^ " --json=" ^ json_file_name)
        val () =
        if not (OS.Process.isSuccess status) then OS.Process.exit status
        else ()
        *)
        val benchmark_results = Json.fromString
          (TextIO.inputAll (TextIO.openIn json_file_name))
        val entry_point_results =
          map (resultsForAlgorithm benchmark_results ns k) entry_points
        fun printRes (entry_point, workloads) =
          ( print (entry_point ^ "\n")
          ; List.app
              (fn (n, Bs) =>
                 ( print ("n=" ^ Int.toString n ^ "\n")
                 ; List.app
                     (fn (B, xs) =>
                        print
                          ("B=" ^ Int.toString B ^ " " ^ Real.toString xs ^ "\n"))
                     Bs
                 ; print "\n"
                 )) workloads
          )
      in
        ListPair.app printRes (entry_points, entry_point_results)
      end
  | (_, _, errors) =>
      (List.app err errors; err (usage ()); OS.Process.exit OS.Process.failure)


val () = main ()
