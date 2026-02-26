val backend = "cuda"
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

fun generate_spec entry_points n k =
  let
    fun mk_case x =
      "script input { blocked_list 100000000i64 " ^ Int.toString (Real.round x)
      ^ " }"
  in
    unlines
      (["==", "entry: " ^ unwords entry_points] @ map mk_case (logspace (k, n)))
  end

fun write_spec_file entry_points n k =
  let
    val spec = generate_spec entry_points n k
    val f = TextIO.openOut spec_file_name
  in
    TextIO.output (f, spec) before TextIO.closeOut f
  end

fun main () =
  let
    val n = 1000000
    val k = 10
    val entry_points =
      ["wyllie_bench", "random_mate_bench", "random_mate_optim_bench"]
    val () = write_spec_file entry_points n k
    val status = OS.Process.system
      ("futhark bench" ^ " " ^ program ^ " --backend=" ^ backend
       ^ " --spec-file=" ^ spec_file_name ^ " --json=" ^ json_file_name)
  in
    if not (OS.Process.isSuccess status) then OS.Process.exit status else ()
  end

val () = main ()
