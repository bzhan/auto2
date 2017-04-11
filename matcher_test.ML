(* Test of matcher. *)

local

val thy = @{theory}
val thy' = thy |> Nat_Arith.add_arith_ac_data
               |> add_list_ac_data
val ctxt = Proof_Context.init_global thy
val ac_samples = [@{term "(a::nat) + b"},
                  @{term "(a::nat) * b"},
                  @{term "(a::int) + b"},
                  @{term "(a::int) * b"},
                  @{term "(a::'a::ring) + b"},
                  @{term "(a::'a::linordered_field) + b"},
                  @{term "(a::'a::linordered_field) * b"}]
val ctxt' = thy' |> Proof_Context.init_global
                 |> fold ACUtil.add_inst_ac_infos ac_samples
val init = RewriteTable.empty ctxt
val tbl = RewriteTable.empty ctxt'

(* Conversion between (id, th) used in rewrite.ML and (id, t) used in
   test cases.
 *)
fun to_term_info (id, th) = (id, rhs_of th)

(* Comparison of list of (box_id, term) pairs. *)
fun eq_info_list (l1, l2) =
    (length l1 = length l2) andalso eq_set (eq_pair (op =) (op aconv)) (l1, l2)

fun print_term_info ctxt (id, t) =
    "(" ^ (string_of_box_id id) ^ ", " ^ (pretty_term ctxt t |> str) ^ ")"

fun print_term_infos ctxt lst =
    commas (map (print_term_info ctxt) lst)

(* info is expected, in box_id * term form, info' is returned value,
   in box_id * thm form (to be printed).
 *)
fun assert_eq_info (info, info') txt (tbl as {ctxt, ...}) =
    if eq_info_list (info, map to_term_info info') then tbl
    else let
      val _ = tracing ("Expected: " ^ print_term_infos ctxt info)
      val _ = tracing ("Actual: " ^ print_infos ctxt info')
    in
      raise AUTO2 txt
    end

fun add_prim_id (prim_id, id) (tbl as {lat, ...}) =
    let
      val (prim_id', lat') = BoxID.add_prim_id id lat
      val _ = assert (prim_id = prim_id') "add_prim_id"
    in
      tbl |> RewriteTable.map_lat (K lat')
    end

fun declare_term str (tbl as {ctxt, ...}) =
    tbl |> RewriteTable.map_context (Variable.auto_fixes (read_term ctxt str))

fun declare_pat str (tbl as {ctxt, ...}) =
    tbl |> RewriteTable.map_context (Variable.auto_fixes (read_pat ctxt str))

fun add_rewrite id (str1, str2) (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
      val th = assume_eq (RewriteTable.theory_of tbl) (t1, t2)
    in
      tbl |> RewriteTable.add_rewrite (id, th)
    end

(* Check th is actually t(env) == u. *)
fun check_info (t, u) txt {ctxt, ...} ((_, inst), th) =
    let
      val t' = subst_term_norm inst t
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of th)
    in
      if lhs aconv t' andalso rhs aconv u then ()
      else let
        val _ = tracing ("inst does not match th.\nt', u' = " ^
                         (pretty_terms ctxt [t', u] |> str) ^
                         "\nth = " ^
                         (pretty_term ctxt (Thm.prop_of th) |> str))
      in raise AUTO2 txt end
    end

fun assert_match_gen matcher ((str_t, str_u), info_str) (tbl as {ctxt, ...}) =
    let
      val (t, u) = (read_pat ctxt str_t, read_term ctxt str_u)
      val _ = trace_tlist_ctxt ctxt "Matching" [t, u]
      val info = map (apsnd (read_term ctxt)) info_str
      val info' = matcher tbl [] (t, cert ctxt u) ([], fo_init)
      val _ = map (check_info (t, u) "assert_match" tbl) info'
      val info'' = map (fn ((id, _), th) => (id, meta_sym th)) info'
    in
      assert_eq_info (info, info'') "assert_match" tbl
    end

fun assert_ac_match ((str_t, str_u), info_str) (tbl as {ctxt, ...}) =
    let
      val ac_info_opt =
          ACUtil.get_head_ac_info_all_thy thy' (read_pat ctxt str_t)
    in
      case ac_info_opt of
          NONE =>
          let
            val _ = tracing ("t: " ^ str_t)
            val _ = tracing ("u: " ^ str_u)
          in
            raise AUTO2 "assert_ac_match"
          end
        | SOME ac_info => assert_match_gen (Matcher.match_ac_raw false ac_info)
                                           ((str_t, str_u), info_str) tbl
    end

val assert_match = assert_match_gen Matcher.match
val assert_head_match = assert_match_gen Matcher.match_head

fun assert_match_list (pairs_str, info_str) (tbl as {ctxt, ...}) =
    let
      val pairs =
          map (fn (is_head, (str_t, str_u)) =>
                  (is_head, (read_pat ctxt str_t,
                             cert ctxt (read_term ctxt str_u))))
              pairs_str
      val info = map (apsnd (map (read_term ctxt))) info_str
      val info' = Matcher.rewrite_match_list tbl pairs ([], fo_init)
      fun check_info_list (instsp, ths) =
          let
            fun check_pair ((t, cu), th) =
                check_info (t, Thm.term_of cu)
                           "assert_match_list" tbl (instsp, th)
          in
            map check_pair (map snd pairs ~~ ths)
          end
      val _ = map check_info_list info'
      val info'' = map (fn ((id, _), ths) => (id, map meta_sym ths)) info'
      val eq_info_list' = eq_set (eq_pair (op =) (eq_list (op aconv)))
      fun to_term_info' (id, ths) = (id, map rhs_of ths)
    in
      if eq_info_list' (info, map to_term_info' info'') then tbl
      else let
        val _ = tracing ("got " ^ print_infos' ctxt info'')
      in
        raise AUTO2 "assert_match_list"
      end
    end

fun done str _ = let val _ = tracing ("Finished " ^ str) in () end

in

val nat_plus_info =
    the (ACUtil.get_head_ac_info_thy thy' @{term "(a::nat) + b"})

val test_shift_to_n =
    let
      val ctxt'' = ctxt' |> Variable.auto_fixes (Free ("n", natT))
      fun test_to_r (n, t, t') =
          test_conv ctxt'' (Matcher.ac_shift_n_to_r_cv nat_plus_info n)
                    "test_shift_n_to_r" (t, t')
      fun test_r (n, t, t') =
          test_conv ctxt'' (Matcher.ac_shift_r_to_n_cv nat_plus_info n)
                    "test_shift_r_to_n" (t, t')
      fun test_l (n, t, t') =
          test_conv ctxt'' (Matcher.ac_shift_l_to_n_cv nat_plus_info n)
                    "test_shift_l_to_n" (t, t')

      val test_data_to_r =[
        (0, "m", "m"),
        (0, "m + n", "m + n"),
        (1, "m + n", "n + m"),
        (0, "m + n + p", "m + n + p"),
        (1, "m + n + p", "m + p + n"),
        (2, "m + n + p", "n + p + m"),
        (3, "m + n + p + q", "n + p + q + m")
      ]

      val test_data_r = [
        (0, "m", "m"),
        (1, "m + n", "m + n"),
        (0, "m + n", "n + m"),
        (2, "m + n + p", "m + n + p"),
        (1, "m + n + p", "m + p + n"),
        (0, "m + n + p", "p + m + n"),
        (0, "m + n + p + q", "q + m + n + p")
      ]

      val test_data_l = [
        (0, "m", "m"),
        (0, "m + n", "m + n"),
        (1, "m + n", "n + m"),
        (0, "m + (n + p)", "m + (n + p)"),
        (1, "m + (n + p)", "n + (m + p)"),
        (2, "m + (n + p)", "n + (p + m)"),
        (3, "m + (n + (p + q))", "n + (p + (q + m))")
      ]
    in
      map test_to_r test_data_to_r @
      map test_r test_data_r @ map test_l test_data_l
    end

val test_ac_group_n =
    let
      val ctxt'' = ctxt' |> Variable.auto_fixes (Free ("n", natT))
      fun test_first_n (n, t, t') =
          test_conv ctxt'' (Matcher.ac_group_first_n_cv nat_plus_info n)
                    "test_group_first_n" (t, t')
      fun test_last_n (n, t, t') =
          test_conv ctxt'' (Matcher.ac_group_last_n_cv nat_plus_info n)
                    "test_group_last_n" (t, t')

      val test_data_last = [
        (1, "m", "m"),
        (1, "m + n", "m + n"),
        (2, "m + n", "m + n"),
        (2, "m + n + p", "m + (n + p)"),
        (3, "m + n + p", "m + n + p"),
        (2, "m + n + p + q", "m + n + (p + q)"),
        (3, "m + n + p + q", "m + (n + p + q)")
      ]

      val test_data_first = [
        (1, "m", "m"),
        (1, "m + n", "m + n"),
        (2, "m + n", "m + n"),
        (2, "m + (n + p)", "m + n + p"),
        (3, "m + (n + p)", "m + (n + p)"),
        (2, "m + (n + (p + q))", "m + n + (p + q)"),
        (3, "m + (n + (p + q))", "m + (n + p) + q")
      ]
    in
      map test_last_n test_data_last @ map test_first_n test_data_first
    end

(* No rewriting, no matching. *)
val test_basic =
    tbl |> declare_term "[m::nat, n, p]"
        |> fold assert_ac_match
        [(("m + n", "m + n"), [([], "m + n")]),
         (("n + m", "m + n"), [([], "n + m")]),
         (("m + n + p", "m + n + p"), [([], "m + n + p")]),
         (("p + m + n", "m + n + p"), [([], "p + m + n")])]
        |> done "test_basic"

(* Matching on subterms. *)
val test_match_subterm =
    tbl |> declare_term "[m::nat, n, p]"
        |> declare_term "f::(nat => nat)"
        |> fold assert_ac_match
        [(("m + f ?a", "m + f n"), [([], "m + f n")]),
         (("f ?a + m", "m + f n"), [([], "f n + m")]),
         (("f ?a + f ?b", "f m + f n"), [([], "f m + f n"), ([], "f n + f m")])]
        |> done "test_match_subterm"

(* Rewriting, without AC. *)
val test_rewrite_no_ac =
    tbl |> fold add_prim_id [(0, []), (1, [])]
        |> declare_term "[m::nat, n, p, q]"
        |> add_rewrite [0] ("m", "p")
        |> add_rewrite [1] ("n", "q")
        |> fold assert_ac_match
        [(("m + n", "m + q"), [([1], "m + n")]),
         (("n + m", "m + q"), [([1], "n + m")]),
         (("m + n", "p + q"), [([0, 1], "m + n")]),
         (("n + m", "p + q"), [([0, 1], "n + m")]),
         (("m + m", "m + p"), [([0], "m + m"), ([0], "m + m")])]
        |> done "test_rewrite_no_ac"

(* Rewriting and AC. *)
val test_rewrite_ac =
    tbl |> fold add_prim_id [(0, []), (1, [])]
        |> declare_term "[m::nat, n, p, q, r, x, y, z]"
        |> add_rewrite [0] ("m", "p + q")
        |> add_rewrite [1] ("n", "r")
        |> add_rewrite [0] ("x", "y + z")
        |> fold assert_ac_match
        [(("p + q", "m"), [([0], "p + q")]),
         (("n + r", "n + r"), [([], "n + r"), ([1], "n + r")]),
         (("p + q + n", "m + r"), [([0, 1], "p + q + n")]),
         (("p + n + q", "m + r"), [([0, 1], "p + n + q")]),
         (("n + p + q", "m + r"), [([0, 1], "n + p + q")]),
         (("p + p + q + q", "m + m"), [([0], "p + p + q + q")]),
         (("q + p + q + p", "m + m"), (replicate 2 ([0], "q + p + q + p"))),
         (("p + y + q + z", "m + x"), [([0], "p + y + q + z")]),
         (("p + y + q + z", "x + m"), [([0], "p + y + q + z")])]
        |> done "test_rewrite_ac"

(* Pattern contains exactly one pure schematic variable. *)
val test_pure_schematic =
    tbl |> declare_term "[m::nat, n, p, r, s]"
        |> add_rewrite [] ("m", "r + s")
        |> fold assert_ac_match
        [(("m + ?n", "m + n"), [([], "m + n")]),
         (("m + p + ?n", "p + m + n"), [([], "m + p + n")]),
         (("r + ?n", "m"), [([], "r + s")]),
         (("r + ?n", "m + n"), [([], "r + (s + n)")]),
         (("r + r + ?n", "m + m"), [([], "r + r + (s + s)")]),
         (("r + s + ?n", "m + m"),
          [([], "r + s + (r + s)"), ([], "r + s + m")]),
         (("m + ?n", "m + n + p + r"), [([], "m + (n + (p + r))")]),
         (("m + n + ?n", "m + n + p + r + s"), [([], "m + n + (p + (r + s))")])]
        |> done "test_pure_schematic"

(* Deeper expansion. *)
val test_pure_schematic2 =
    tbl |> declare_term "[m::nat, n, p, r, s]"
        |> add_rewrite [] ("m", "n + p")
        |> add_rewrite [] ("p", "r + s")
        |> fold assert_ac_match
        [(("n + r + ?s", "m"), [([], "n + r + s")]),
         (* If r is matched first, cannot find expansion. *)
         (("r + n + ?s", "m"), [])]
        |> done "test_pure_schematic2"

(* Matching with minus, one schematic variable. *)
val test_minus_schematic =
    tbl |> declare_term "[m::int, n, p, q]"
        |> fold assert_ac_match
        [(("m + -?n", "m - n"), [([], "m + -n")]),
         (("m + -?n", "m - n - p"), [([], "m + -(n + p)")]),
         (("m + ?n", "m - n"), [([], "m + -n")]),
         (("m + ?n", "m - n - p"), [([], "m + (-n + -p)")]),
         (("m + -?n", "m - n - p - q"), [([], "m + -(n + (p + q))")]),
         (("m + -?n", "m - n + p + q"), [([], "m + -(n + (-p + -q))")])]
        |> done "test_minus_schematic"

(* Associativity only. Uses append on lists. *)
val test_assoc_only =
    tbl |> declare_term "[l::('a list), m, n]"
        |> fold assert_ac_match
        [(("l @ m", "l @ m"), [([], "l @ m")]),
         (("(l @ m) @ n", "l @ m @ n"), [([], "(l @ m) @ n")]),
         (("l @ ?n", "l @ m"), [([], "l @ m")]),
         (("l @ ?n", "l @ m @ n"), [([], "l @ m @ n")])]
        |> done "test_assoc_only"

(* Associativity only, with rewrite. *)
val test_assoc_only_rewrite =
    tbl |> declare_term "[l::('a list), m, n, p, q]"
        |> add_rewrite [] ("l", "m @ n")
        |> add_rewrite [] ("n", "p @ q")
        |> fold assert_ac_match
        [(("m @ ?n", "l"), [([], "m @ n")]),
         (("(m @ p) @ ?n", "l"), [([], "(m @ p) @ q")]),
         (("m @ ?n", "l @ l"), [([], "m @ n @ l")]),
         (("((m @ n) @ m) @ ?n", "l @ l"), [([], "((m @ n) @ m) @ n")])]
        |> done "test_assoc_only_rewrite"

(* Associativity only, schematic variable at left. *)
val test_assoc_only_left =
    tbl |> declare_term "[l::('a list), m, n, p, q]"
        |> fold assert_ac_match
        [(("?n @ m", "l @ m"), [([], "l @ m")]),
         (("?n @ n", "l @ m @ n"), [([], "(l @ m) @ n")]),
         (("?n @ p", "l @ m @ n @ p"), [([], "((l @ m) @ n) @ p")]),
         (("(?n @ p) @ q", "l @ m @ n @ p @ q"),
          [([], "(((l @ m) @ n) @ p) @ q")])]
        |> done "test_assoc_only_left"

(* Associativity only, schematic variable at left, with rewrite. *)
val test_assoc_only_left_rewrite =
    tbl |> declare_term "[l::('a list), m, n, p, q]"
        |> add_rewrite [] ("l", "m @ n")
        |> add_rewrite [] ("m", "p @ q")
        |> fold assert_ac_match
        [(("?m @ n", "l"), [([], "m @ n")]),
         (("(?m @ q) @ n", "l"), [([], "(p @ q) @ n")]),
         (("?m @ n", "l @ l"), [([], "(l @ m) @ n")]),
         (("((?m @ n) @ m) @ n", "l @ l"), [([], "((m @ n) @ m) @ n")])]
        |> done "test_assoc_only_left_rewrite"

(* Basic rewriting. *)
val test_rewrite =
    init |> add_prim_id (0, []) |> add_prim_id (1, [])
         |> declare_term "[a::nat, b, c]"
         |> declare_term "f::(nat => nat => nat)"
         |> declare_pat "[?m::nat, ?n]"
         |> declare_pat "?A::('a::{plus})"
         |> add_rewrite [0] ("a", "b")
         |> add_rewrite [1] ("a", "c")
         |> fold assert_match
         [(("a", "b"), [([0], "a")]),
          (("c", "a"), [([1], "c")]),
          (("?n + ?n", "a + b"), [([0], "a + a")]),
          (("?A + ?A", "c + a"), [([1], "c + c")]),
          (("?A + ?A + ?A", "a + b + c"), [([0, 1], "a + a + a")]),
          (("f ?m ?n", "f a b"), [([], "f a b")]),
          (("f ?m ?m", "f c a"), [([1], "f c c")])]
         |> done "test_rewrite"

(* Rewriting from atomic to function application. *)
val test_rewrite2 =
    init |> add_prim_id (0, []) |> add_prim_id (1, [])
         |> declare_term "[a::nat, b, c]"
         |> declare_pat "[?n::nat]"
         |> add_rewrite [0] ("a", "b + c")
         |> add_rewrite [1] ("b", "c")
         |> assert_match (("?n + ?n", "a"), [([0, 1], "b + b")])
         |> done "test_rewrite2"

(* Abstractions. *)
val test_abstraction =
    init |> declare_term "[m::nat, n]"
         |> declare_term "P::(nat => nat => nat)"
         |> declare_pat "?A::(nat => nat => 'a::{plus})"
         |> fold assert_match
         [(("%x y. ?A x y", "%m n. P m n"), [([], "%m n. P m n")]),
          (("%x y. ?A x y + ?A y x", "%m n. P m n + P n m"),
           [([], "%m n. P m n + P n m")]),
          (("%x y. ?A x y", "%x y. (x::nat) + y + y"),
           [([], "%x y. (x::nat) + y + y")])]
         |> done "test_abstraction"

(* Abstractions with rewriting. *)
val test_abstraction_rewrite =
    init |> declare_term "[m::nat, n, p]"
         |> declare_term "P::(nat => nat => nat)"
         |> declare_term "f::(nat => nat => 'a::{plus})"
         |> declare_pat "?A::(nat => ?'a::{plus})"
         |> add_rewrite [] ("m", "n")
         |> add_rewrite [] ("p", "0::nat")
         |> assert_match (("%x. ?A x + ?A x", "%x. P x m + P x n"),
                          [([], "%x. P x m + P x m")])
         |> assert_match (("%x. f x 0", "%x. f x p"), [([], "%x. f x 0")])
         |> done "test_abstraction_rewrite"

(* One side is abstraction, use eta_conversion. *)
val test_eta_conversion =
    init |> declare_term "P::(nat => nat)"
         |> assert_match (("%x. P x", "P"), [([], "%x. P x")])
         |> assert_match (("P", "%x. P x"), [([], "P")])
         |> done "test_eta_conversion"

(* Test matching of higher order patterns. *)
val test_higher_order =
    init |> declare_term "f::(nat => nat)"
         |> declare_pat "?f::(nat => nat)"
         |> assert_match (("%n. (?f n, ?f (n + 1))", "%n. (f n, f (n + 1))"),
                          [([], "%n. (f n, f (n + 1))")])
         |> assert_match (("%n. (?f (n + 1), ?f n)", "%n. (f (n + 1), f n)"),
                          [([], "%n. (f (n + 1), f n)")])
         |> done "test_higher_order"

(* Test handling of schematic type variables. *)
val test_match_type =
    tbl |> assert_match (("image_mset ?f {#}", "{#i. i :# {#}#}"),
                         [([], "{#i. i :# {#}#}")])
        |> assert_match (("image_mset ?f {#}", "{#(i::nat). i :# {#}#}"),
                         [([], "{#(i::nat). i :# {#}#}")])
        (* sorted [] has concrete type, but not []. *)
        |> assert_match (("sorted []", "sorted []"), [([], "sorted []")])
        |> done "test_match_type"

(* Test special schematic variable ?NUMC. *)
val test_numc =
    init |> declare_term "[k::int, m]"
         |> add_rewrite [] ("k", "1::int")
         |> assert_match (("?NUMC::int", "k"), [([], "1::int")])
         |> assert_match (("?NUMC", "k"), [([], "1::int")])
         |> assert_match (("?NUMC", "m"), [])
         |> done "test_numc"

(* Reduction of unit. *)

fun check_reduce_unit (str, info_str) (tbl as {ctxt, ...}) =
    let
      val t = read_pat ctxt str
      val info = map (apsnd (read_pat ctxt)) info_str
      val thy = RewriteTable.theory_of tbl
      val ac_info = the (ACUtil.get_head_ac_info_thy thy t)
      val info' = Matcher.reduce_unit_t tbl ac_info ([], t)
    in
      assert_eq_info (info, info') "check_reduce_unit" tbl
    end

val test_reduce_unit =
    tbl |> declare_term "[m::nat, n, p, q]"
        |> declare_pat "[?A::nat, ?B]"
        |> add_prim_id (0, [])
        |> add_rewrite [] ("p", "1::nat")
        |> add_rewrite [0] ("q", "1::nat")
        |> check_reduce_unit ("m * n", [([], "m * n")])
        |> check_reduce_unit ("m * p", [([], "m")])
        |> check_reduce_unit ("m * q", [([], "m * q"), ([0], "m")])
        |> check_reduce_unit ("p * q", [([], "q"), ([0], "1::nat")])
        |> check_reduce_unit ("m * 1", [([], "m")])
        |> check_reduce_unit ("p * 1", [([], "1::nat")])
        |> check_reduce_unit ("m + 0", [([], "m::nat")])
        |> done "test_reduce_unit"

(* Analysis of pattern. *)

fun check_analyze_t (str, info_str) (tbl as {ctxt, ...}) =
    let
      val t = read_pat ctxt str
      val ac_info_opt = ACUtil.get_head_ac_info_all_thy thy' t
      val info = map (apsnd (read_pat ctxt)) info_str
      val info' =
          case ac_info_opt of
              NONE => [([], Thm.reflexive (cert ctxt t))]
            | SOME ac_info =>
              map (fn (_, (id, _), th) => (id, th))
                  (Matcher.analyze_t ac_info tbl ([], fo_init) t)
    in
      assert_eq_info (info, info') "check_analyze_t" tbl
    end

val test_analyze_t =
    tbl |> declare_term "[m::nat, n]"
        |> declare_pat "[?A::nat, ?B, ?Au]"
        |> declare_term "[l::nat list]"
        |> declare_pat "[?l::nat list]"
        |> fold check_analyze_t
        [("m", [([], "m")]),
         ("?A", [([], "?A")]),
         ("m + n", [([], "m + n")]),
         ("m + 0", [([], "m")]),
         ("m + ?A", [([], "m + ?A")]),
         ("m + (n + ?A)", [([], "m + n + ?A")]),
         ("?A + (m + n)", [([], "m + n + ?A")]),
         ("?Au + m", [([], "m + ?Au"), ([], "m")]),
         ("l @ ?l", [([], "l @ ?l")]),
         ("?l @ l", [([], "?l @ l")]),
         ("?A + (?A - ?B)", [([], "(?A - ?B) + ?A")]),
         ("1 * m", [([], "m")])
        ]
        |> done "check_analyze_t"

(* Working with AC matching. *)
val test_ac_whole =
    tbl |> declare_term "[m::nat, n, p, q]"
        |> add_rewrite [] ("p", "m + n")
        |> assert_match (("m + n", "m + n"), [([], "m + n")])
        |> assert_match (("m + n", "p"), [([], "m + n")])
        |> assert_match (("p", "m + n"), [([], "p")])
        |> assert_match (("m + n + q", "p + q"), [([], "m + n + q")])
        |> done "test_ac_whole"

val test_ac_whole_inverse =
    tbl |> declare_term "[m::('a::linordered_field), n]"
        |> fold assert_match
        [(("m - n", "m - n"), [([], "m - n")]),
         (("m + (-n)", "m - n"), [([], "m + (-n)")]),
         (("?n + m + (-m)", "n + m - m"), [([], "n + m + (-m)")]),
         (("(?m, ?n * ?m * inverse ?m)", "(m, n * m / m)"),
          [([], "(m, n * m * inverse m)")]),
         (("(?m, ?n * ?m * inverse ?m)", "(m, n / m * m)"),
          [([], "(m, n * m * inverse m)")])]
        |> done "test_ac_whole_inverse"

val test_ac_whole_with_rewrite =
    tbl |> declare_term "[m::int, n, p, q, r, s]"
        |> declare_pat "?a::int"
        |> add_rewrite [] ("m", "p + q")
        |> add_rewrite [] ("n", "r + s")
        |> assert_match (("?a + p + r", "m + n"), [([], "s + q + p + r")])
        |> assert_match (("?a + p - r", "m - n"), [([], "-s + q + p - r")])
        |> done "test_ac_whole_with_rewrite"

(* Test those cases where comb matching will be used. *)
val test_ac_literal =
    tbl |> declare_term "[m::nat, n, p]"
        |> declare_term "f::(nat => nat => nat)"
        |> declare_pat "[?A::nat, ?B, ?C]"
        |> fold assert_match
        [(("?A + ?B", "m + n"), [([], "m + n")]),
         (("?A + ?B + ?C", "m + n + p"), [([], "m + n + p")]),
         (("?A + ?B + ?C", "m + (n + p)"), []),
         (("?A - ?B", "m - n"), [([], "m - n")]),
         (("?A - ?B", "m + n"), []),
         (("?A + f ?A ?B", "m + f m n"), [([], "m + f m n")])]
        |> done "test_ac_literal"

(* Comb matching is avoided because some of the schematic variables
   are already instantiated.
 *)
val test_ac_literal2 =
    tbl |> declare_term "[m::int, n, p]"
        |> declare_pat "[?A::int, ?B]"
        |> fold assert_match
        [(("(?A, ?A + ?B)", "(m, n + m)"), [([], "(m, m + n)")]),
         (("(?A, ?A + ?B)", "(m, m + n + p)"), [([], "(m, m + (n + p))")]),
         (("(?A, ?A - ?A + ?B)", "(m, m + p - m)"), [([], "(m, m - m + p)")]),
         (("(?A, ?A - ?A + ?B)", "(m, -(m - m + p))"),
          [([], "(m, m - m + -p)")]),
         (("(?A, ?A - ?A - ?B)", "(m, -(m - m + p))"),
          [([], "(m, m - m - p)")])]
        |> done "test_ac_literal2"

(* For natural numbers, minus is not an AC operation. *)
val test_ac_nat_minus =
    tbl |> declare_term "[m::nat, n]"
        |> declare_term "[a::int, b]"
        |> declare_pat "[?m::nat, ?n]"
        |> declare_pat "[?a::int, ?b]"
        |> fold assert_match
        [(("?m + (?m - ?n)", "m + (m - n)"), [([], "m + (m - n)")]),
         (("?m + (?m - ?n)", "(m - n) + m"), [([], "m + (m - n)")]),
         (("?a + (?a - ?b)", "a + (a - b)"), [([], "a + (a - b)")]),
         (("?a + (?a - ?b)", "(a - b) + a"), [])]
        |> done "test_ac_nat_minus"

(* Test elimination of redundancy in the output of AC matcher. *)
val test_redundant =
    tbl |> fold add_prim_id [(0, []), (1, [])]
        |> declare_term "[m::nat, n, p, q, r, x, y, z]"
        |> add_rewrite [0] ("m", "p + q")
        |> add_rewrite [1] ("n", "r")
        |> fold assert_match
        [(("n + r", "n + r"), [([], "n + r")]),
         (("q + p + q + p", "m + m"), [([0], "q + p + q + p")])]
        |> done "test_redundant"

(* Test for the ac_subterm_equivs function. *)

fun assert_ac_subterm_equivs ((id, str), info_str) (tbl as {ctxt, ...}) =
    let
      val u = read_term ctxt str
      val ac_info =
          the (ACUtil.get_head_ac_info_all_thy thy' u)
          handle Option.Option =>
                 raise AUTO2 "assert_ac_subterm_equivs: ac_info not found."
      val info = map (apsnd (read_term ctxt)) info_str
      val res = Matcher.ac_subterm_equivs tbl ac_info (id, cert ctxt u)
    in
      assert_eq_info (info, res) "assert_ac_subterm_equivs" tbl
    end

val test_ac_subterm_equivs =
    tbl |> declare_term "[m::int, n, p, q, r]"
        |> add_rewrite [] ("p", "m + n")
        |> fold assert_ac_subterm_equivs
        [(([], "m + n"), [([], "m + n")]),
         (([], "m + n + q"), [([], "p + q"), ([], "m + n + q")]),
         (([], "m + n - q"), [([], "p - q"), ([], "m + n - q")]),
         (([], "q - (m + n)"), [([], "q - p"), ([], "q - (m + n)")]),
         (([], "m + n + q + r"), [([], "m + n + q + r"), ([], "p + q + r")]),
         (([], "m + n + (m + n)"),
          [([], "m + n + (m + n)"), ([], "p + (m + n)"), ([], "m + n + p"),
           ([], "p + p")]),
         (([], "-(m + n)"), [([], "-(m + n)"), ([], "-p")])]
        |> done "test_ac_subterm_equivs"

(* Test subterm equivalence during AC matching. *)
val test_ac_subterm_equivs_match =
    tbl |> declare_term "[m::int, n, p, q, r]"
        |> add_rewrite [] ("p", "m + n")
        |> fold assert_match
        [(("p + q", "m + n + q"), [([], "p + q")]),
         (("p + q + r", "m + n + q + r"), [([], "p + q + r")]),
         (("p - q", "m + n - q"), [([], "p - q")]),
         (("q - p", "q - (m + n)"), [([], "q - p")]),
         (("q - p", "q + -(m + n)"), [([], "q - p")])]
        |> done "test_ac_subterm_equivs_match"

(* Test special schematic variable ?au. *)
val test_unit =
    tbl |> declare_term "[k::nat, m]"
        |> fold assert_match
        [(("?a * k", "k"), []),
         (("?au * k", "k"), [([], "1 * k")]),
         (("?au * k", "m * k"), [([], "m * k")]),
         (("?NUMCu * k", "k"), [([], "1 * k")]),
         (("?NUMCu * k", "m * k"), []),
         (("?k * ?au", "k"), [([], "k * 1")]),
         (("?au * (k + ?bu)", "k"), [([], "1 * (k + 0)")]),
         (("?au * (k + m)", "m + k"), [([], "1 * (k + m)")]),
         (("1 * m", "m"), [([], "1 * m")])]
        |> done "test_unit"

(* Mix of AC matching and abstraction. *)
val test_ac_abstraction =
    tbl |> declare_term "[f::(nat => nat), g]"
        |> assert_match (("%n. f n + g n", "%n. g n + f n"),
                         [([], "%n. f n + g n")])
        |> done "test_ac_abstraction"

(* Mix of AC matching and higher order patterns. *)
val test_ac_higher_order =
    tbl |> declare_term "f::(nat => nat)"
        |> declare_pat "?f::(nat => nat)"
        (* TODO: handle the reverse case. *)
        |> assert_match (("%n. ?f n + ?f (n + 1)", "%n. f n + f (n + 1)"),
                         [([], "%n. f n + f (n + 1)")])
        |> assert_match (("%n. ?f n + ?f (n + 1)", "%n. f (n + 1) + f n"),
                         [([], "%n. f n + f (n + 1)")])
        |> done "test_ac_higher_order"

(* Handling of units on the t side. *)
val test_ac_match_unit =
    tbl |> declare_term "[m::nat, n, p]"
        |> add_rewrite [] ("1::nat", "n")
        |> add_rewrite [] ("m", "m * n")
        |> fold assert_match
        [(("m * n", "m * n"), [([], "m * n")]),
         (("?a * m", "m * n"), []),
         (("?au * m", "m * n"), [([], "1 * m")]),
         (("(?a, ?a * m)", "(1::nat, m)"), [([], "(1::nat, 1 * m)")]),
         (("(?a, ?a * m * p)", "(1::nat, m * p)"),
          [([], "(1::nat, 1 * m * p)")]),
         (("(?a, m * ?a * p)", "(1::nat, m * p)"),
          [([], "(1::nat, m * 1 * p)")]),
         (("(?a, m * p * ?a)", "(1::nat, m * p)"),
          [([], "(1::nat, m * p * 1)")])]
        |> done "test_ac_match_unit"

(* Test head match. *)
val test_head_match =
    tbl |> declare_term "[k::nat, m, n]"
        |> add_rewrite [] ("k", "m")
        |> fold assert_head_match
        [(("k", "m"), []),
         (("?au * k", "k"), [([], "1 * k")]),
         (("?au * (?bu + k)", "k"), [([], "1 * (0 + k)")]),
         (("?au * (k + m)", "m + k"), [([], "1 * (k + m)")])]
        |> done "test_head_match"

(* Test match list. *)
val test_match_list =
    init |> declare_term "[k::nat, l]"
         |> declare_pat "?a::nat"
         |> add_rewrite [] ("k", "l")
         |> assert_match_list ([(false, ("?a", "k")), (false, ("?a", "l"))],
                               [([], ["k", "k"])])
         |> assert_match_list ([(false, ("?a", "k")), (true, ("?a", "l"))], [])
         |> assert_match_list ([(true, ("?a", "k")), (false, ("?a", "l"))],
                               [([], ["k", "k"])])
         |> assert_match_list ([(true, ("?a + b", "k + b")),
                                (true, ("?a + b", "l + b"))],
                               [([], ["k + b", "k + b"])])
         |> done "test_match_list"

(* Test of pre-matcher. *)
fun assert_pre_match_gen res at_head (str_t, str_u) (tbl as {ctxt, ...}) =
    let
      val (t, cu) = (read_pat ctxt str_t, cert ctxt (read_term ctxt str_u))
      val pre_match_fn = if at_head then Matcher.pre_match_head
                         else Matcher.pre_match
    in
      if pre_match_fn tbl (t, cu) = res then tbl
      else let
        val _ = trace_tlist_ctxt ctxt "Pattern, term: " [t, Thm.term_of cu]
      in
        raise AUTO2 ("assert_pre_match (expected " ^ (string_of_bool res) ^ ")")
      end
    end

val assert_pre_match = assert_pre_match_gen true false
val assert_not_pre_match = assert_pre_match_gen false false
val assert_pre_match_head = assert_pre_match_gen true true
val assert_not_pre_match_head = assert_pre_match_gen false true

val test_pre_match =
    init |> declare_term "[m::nat, n]"
         |> declare_term "[a::'a]"
         |> declare_pat "?n::nat"
         |> declare_pat "?a::?'a"
         |> assert_pre_match ("?a", "n")
         |> assert_pre_match ("?n", "n")
         |> assert_not_pre_match ("?n", "a")
         |> assert_not_pre_match ("m", "n")
         |> done "test_pre_match"

val test_pre_match_quant =
    tbl |> declare_term "[P::(nat => bool), Q]"
        |> declare_term "[S::(nat => nat => bool), T]"
        |> declare_term "[x::nat, y, z]"
        |> assert_pre_match ("ALL x. P x", "ALL y. P y")
        |> assert_not_pre_match ("ALL x. P x", "ALL x. Q x")
        |> assert_pre_match ("ALL x y. S x y", "ALL y z. S y z")
        |> assert_not_pre_match ("ALL x y. S x y", "ALL x y. S y x")
        |> assert_not_pre_match ("ALL x y. S x y", "ALL x y. T x y")
        |> assert_pre_match ("ALL x y. ?S x y", "ALL x y. x < y")
        |> assert_pre_match ("ALL x. x + y = z & ?P x",
                             "ALL x. x + y = z & P x")
        |> done "test_pre_match_quant"

val test_pre_match_eta_conversion =
    init |> declare_term "[P::(nat => nat), Q]"
         |> assert_pre_match ("%x. P x", "P")
         |> assert_pre_match ("P", "%x. P x")
         |> assert_not_pre_match ("P", "%x. Q x")
         |> done "test_pre_match_eta_conversion"

val test_pre_match_ac =
    tbl |> declare_term "[m::int, n]"
        |> declare_pat "[?a::int, ?b]"
        |> assert_pre_match ("?a + ?b", "m + n")
        |> assert_pre_match ("?a + ?b", "m - n")
        |> assert_pre_match ("?a + ?b", "-m")
        |> assert_not_pre_match ("?a + ?b", "m")
        |> assert_pre_match ("?a - ?b", "m + n")
        |> assert_not_pre_match ("?a * ?b", "m + n")
        |> done "test_pre_match_ac"

val test_pre_match_unit =
    tbl |> declare_term "[m::int, n]"
        |> declare_pat "[?au::int, ?b, ?c]"
        |> declare_pat "[?ru::?'a::ring, ?su, ?t]"
        |> assert_pre_match ("?au + ?b", "m")
        |> assert_pre_match ("?au + ?b", "m * n")
        |> assert_pre_match ("?au + ?b", "m + n")
        |> assert_pre_match ("?au + (?b + ?c)", "m + n")
        |> assert_not_pre_match ("?au + (?b + ?c)", "m * n")
        |> assert_pre_match ("?ru + ?t", "m")
        |> assert_pre_match ("?ru + (?su * ?t)", "m")
        |> done "test_pre_match_unit"

val test_pre_match_head_ac =
    tbl |> declare_term "[m::int, n]"
        |> declare_term "[r::'a::ring, s]"
        |> declare_pat "[?a::int, ?b]"
        |> declare_pat "[?r::(?'a::ring), ?s]"
        |> assert_pre_match_head ("?a + ?b", "m - n")
        |> assert_pre_match_head ("?r + ?s", "m - n")
        |> assert_not_pre_match_head ("?a + ?b", "r - s")
        |> assert_pre_match_head ("?r + ?s", "r - s")
        |> done "test_pre_match_head_ac"

(* Counting number of literal AC matches. *)
val test_literal_ac_count =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term_pat "?a::int"}, @{term_pat "?n::nat"}]

      fun test (str_t, n) =
          let
            val t = read_pat ctxt' str_t
            val n' = Matcher.literal_ac_count thy' t []
          in
            if n = n' then ()
            else let
              val _ = trace_t_ctxt ctxt "t:" t
              val _ = tracing ("Should be " ^ (string_of_int n) ^ ", got " ^
                               (string_of_int n'))
            in
              raise AUTO2 "test_literal_ac_count"
            end
          end

      val test_data = [
        ("?a + ?b", 1), ("?a - ?b", 1),
        ("?m + ?n", 1), ("?m - ?n", 0),
        ("?a + (m + ?b)", 1), ("?a + (m * ?b)", 0),
        ("(?a, ?a + ?b)", 0), ("(?a + ?b, ?a)", 1),
        ("(?a + ?b) * ?c", 1),
        ("(?a, (?a + ?b) * ?c)", 0), ("(?c, (?a + ?b) * ?c)", 1)
      ]
    in
      map test test_data
    end

val test_get_pattern_order =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term_pat "?a::int"}, @{term_pat "?n::nat"}]

      fun test (str_t1, str_t2, res) =
          let
            val (t1, t2) = apply2 (read_pat ctxt') (str_t1, str_t2)
            val res' = Matcher.get_pattern_order thy' (t1, t2)
          in
            if res = res' then ()
            else let
              val _ = trace_tlist_ctxt ctxt "t1, t2:" [t1, t2]
              val _ = tracing ("Should be " ^ (string_of_bool res))
            in
              raise AUTO2 "test_get_pattern_order"
            end
          end

      val test_data = [
        ("?a", "?a + ?b", true),
        ("?a + ?b", "?a", false)
      ]
    in
      map test test_data
    end

end
