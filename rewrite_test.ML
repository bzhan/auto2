(* Unit test for rewrite.ML. *)

local

val thy = @{theory}
val thy' = thy |> add_logic_ac_data |> Nat_Arith.add_arith_ac_data
val ctxt' = Proof_Context.init_global thy'
val init = RewriteTable.empty @{context}
val tbl = RewriteTable.empty ctxt'

fun add_prim_id (prim_id, id) (tbl as {lat, ...}) =
    let
      val (prim_id', lat') = BoxID.add_prim_id id lat
      val _ = assert (prim_id = prim_id') "add_prim_id"
    in
      tbl |> RewriteTable.map_lat (K lat')
    end

(* Conversion between (id, th) used in rewrite.ML and (id, t) used in
   test cases.
 *)
fun to_term_info (id, th) = (id, rhs_of th)
(* Comparison of list of box_ids. *)
val eq_id_list = eq_set (op =)
(* Comparison of list of (box_id, term) pairs. *)
val eq_info_list = eq_set (eq_pair (op =) (op aconv))

fun print_term_info ctxt (id, t) =
    "(" ^ (string_of_box_id id) ^ ", " ^ (pretty_term ctxt t |> str) ^ ")"
fun print_term_infos ctxt lst =
    commas (map (print_term_info ctxt) lst)
val string_of_box_id_list = string_of_list BoxID.string_of_box_id

fun done str _ = let val _ = tracing ("Finished " ^ str) in () end

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

fun assert_rew_info str info_str (tbl as {ctxt, ...}) =
    let
      val t = read_term ctxt str
      val info = map (apsnd (read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.get_rewrite_info tbl t)
                     "assert_rew_info" tbl
    end

fun assert_srew_info str info_str (tbl as {ctxt, ...}) =
    let
      val t = read_term ctxt str
      val info = map (apsnd (read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.get_subterm_rewrite_info tbl t)
                     "assert_srew_info" tbl
    end

fun assert_head_rep (id, str) info_str (tbl as {ctxt, ...}) =
    let
      val t = read_term ctxt str
      val info = map (apsnd (read_term ctxt)) info_str
      val th = RewriteTable.refl tbl t
    in
      assert_eq_info (info, RewriteTable.get_head_rep_with_id_th tbl (id, th))
                     "assert_head_rep" tbl
    end

fun assert_equiv_gen exp_equiv id (str1, str2) (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
    in
      if exp_equiv = RewriteTable.is_equiv id tbl (t1, t2) then tbl
      else let
        val _ = tracing ("id: " ^ (string_of_box_id id))
        val _ = trace_tlist_ctxt ctxt "Input:" [t1, t2]
      in
        raise AUTO2 (if exp_equiv then "assert_equiv" else "assert_not_equiv")
      end
    end

val assert_equiv = assert_equiv_gen true
val assert_not_equiv = assert_equiv_gen false

fun assert_simpl_info str info_str (tbl as {ctxt, ...}) =
    let
      val t = read_term ctxt str
      val info = map (apsnd (read_term ctxt)) info_str
    in
      assert_eq_info (info, RewriteTable.simplify_info tbl t)
                     "assert_simpl_info" tbl
    end

fun assert_simpl id (str, str') (tbl as {ctxt, ...}) =
    let
      val (t, t') = (read_term ctxt str, read_term ctxt str')
      val res = rhs_of (RewriteTable.simplify id tbl t)
    in
      if res aconv t' then tbl
      else let
        val _ = trace_t_ctxt ctxt "Input:" t
        val _ = trace_t_ctxt ctxt "Expected:" t'
        val _ = trace_t_ctxt ctxt "Actual:" res
      in
        raise AUTO2 "assert_simpl"
      end
    end

(* Collect all head equivs under box id. The return value of
   get_head_equiv is in the form [(head, [((id, th), groups), ...]), ...],
   and we want to collect the set of (id, th).
 *)
fun assert_head_equivs (id, str) info_str (tbl as {ctxt, ...}) =
    let
      val u = read_term ctxt str
      val info = map (apsnd (read_term ctxt)) info_str
      val res = (RewriteTable.get_head_equiv tbl u)
                    |> maps snd |> map fst
                    |> RewriteTable.merge_box_with_info tbl id
    in
      assert_eq_info (info, res) "assert_head_equivs" tbl
    end

(* Return value of get_head_equiv_t is in the form [((id, th), groups), ...]
 *)
fun assert_head_equivs_t str_t (id, str) info_str (tbl as {ctxt, ...}) =
    let
      val (t, u) = (read_term ctxt str_t, read_term ctxt str)
      val info = map (apsnd (read_term ctxt)) info_str
      val res = (RewriteTable.get_head_equiv_with_t tbl (id, u) t) |> map fst
    in
      assert_eq_info (info, res) "assert_head_equivs_t" tbl
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

fun assert_match ((str_t, str_u), info_str) (tbl as {ctxt, ...}) =
    let
      val (t, u) = (read_pat ctxt str_t, read_term ctxt str_u)
      val _ = trace_tlist_ctxt ctxt "Matching" [t, u]
      val info = map (apsnd (read_term ctxt)) info_str
      val info' = fo_table_match [] tbl (t, u)
      val _ = map (check_info (t, u) "assert_match" tbl) info'
      val info'' = map (fn ((id, _), th) => (id, meta_sym th)) info'
    in
      assert_eq_info (info, info'') "assert_match" tbl
    end

fun assert_match_list (pairs_str, info_str) (tbl as {ctxt, ...}) =
    let
      val pairs =
          map (fn (is_head, (str_t, str_u)) =>
                  (is_head, (read_pat ctxt str_t, read_term ctxt str_u)))
              pairs_str
      val info = map (apsnd (map (read_term ctxt))) info_str
      val info' = fo_table_match_list [] tbl pairs
      fun check_info_list (instsp, ths) =
          let
            fun check_pair ((t, u), th) =
                check_info (t, u) "assert_match_list" tbl (instsp, th)
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

fun assert_match_diff (str_lhs, str_rhs) (str_t, str_u) info_str
                      (tbl as {ctxt, ...}) =
    let
      val (lhs, rhs) = (read_term ctxt str_lhs, read_term ctxt str_rhs)
      val (t, u) = (read_pat ctxt str_t, read_term ctxt str_u)
      val _ = trace_tlist_ctxt ctxt "Matching (diff)" [t, u]
      val info = map (apsnd (read_term ctxt)) info_str
      val tbl' = tbl |> RewriteTable.append_rewrite (lhs, rhs)
      val rtype = RewriteTable.LAST (tbl', [])
      val info' = (fo_table_match [] tbl' (t, u))
                      |> RewriteTable.replace_id_for_type rtype
      val _ = map (check_info (t, u) "assert_match_diff" tbl) info'
      val info'' = info' |> map (fn ((id, _), th) => (id, meta_sym th))
    in
      assert_eq_info (info, info'') "assert_match_diff" tbl
    end

(* count is expected, count is returned value (to be printed). *)
fun assert_count count count' txt tbl =
    if count = count' then tbl else
    let val _ = tracing ("got " ^ string_of_int count') in raise AUTO2 txt end

fun assert_num_match (str_t, str_u) count (tbl as {ctxt, ...}) =
    let
      val (t, u) = (read_pat ctxt str_t, read_term ctxt str_u)
      val count' = length (fo_table_match [] tbl (t, u))
    in
      assert_count count count' "assert_num_match" tbl
    end

fun index_reps tbl =
    let
      fun index_reps_t t =
          fold RewriteTable.update_subsimp
               (RewriteTable.get_subterm_rewrite_info tbl t)
    in
      fold index_reps_t (RewriteTable.get_all_terms tbl) tbl
    end

fun declare_term str (tbl as {ctxt, ...}) =
    tbl |> RewriteTable.map_context (Variable.auto_fixes (read_term ctxt str))

fun declare_pat str (tbl as {ctxt, ...}) =
    tbl |> RewriteTable.map_context (Variable.auto_fixes (read_pat ctxt str))

(* First part: test internal functions. *)

(* Modification functions using terms. *)
fun add_equiv id (str1, str2) (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
      val eq_th = assume_meta_eq (RewriteTable.theory_of tbl) (t1, t2)
    in
      tbl |> RewriteTable.add_equiv (id, eq_th)
    end

fun add_term str (tbl as {ctxt, ...}) =
    tbl |> RewriteTable.add_term ([], read_term ctxt str)

fun assert_eq_edges (str1, str2) ids (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
      val ids' = (RewriteTable.equiv_neighs tbl t1)
                     |> map to_term_info
                     |> filter (fn (_, t2') => t2 aconv t2') |> map fst
    in
      if eq_id_list (ids, ids') then tbl
      else let
        val _ = trace_tlist_ctxt ctxt "Input:" [t1, t2]
        val _ = tracing ("Expected: " ^ (string_of_box_id_list ids))
        val _ = tracing ("Actual: " ^ (string_of_box_id_list ids'))
      in
        raise AUTO2 "assert_eq_edges"
      end
    end

fun update_simp id (str1, str2) (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
      val eq_th = assume_meta_eq (RewriteTable.theory_of tbl) (t1, t2)
    in
      tbl |> RewriteTable.update_simp (id, eq_th)
    end

fun assert_rewrite id (str, str') (tbl as {ctxt, ...}) =
    let
      val (t, t') = (read_term ctxt str, read_term ctxt str')
      val res = rhs_of (RewriteTable.get_rewrite id tbl t)
    in
      if res aconv t' then tbl
      else let
        val _ = trace_t_ctxt ctxt "Input:" t
        val _ = trace_t_ctxt ctxt "Expected:" t'
        val _ = trace_t_ctxt ctxt "Actual:" res
      in
        raise AUTO2 "assert_rewrite"
      end
    end

fun add_rewrite id (str1, str2) (tbl as {ctxt, ...}) =
    let
      val (t1, t2) = (read_term ctxt str1, read_term ctxt str2)
    in
      tbl |> RewriteTable.add_rewrite id (t1, t2)
    end

in

val test_equiv_basic =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0]), (3, [1])]
         |> declare_term "[a, b, c, d]"
         |> fold add_term ["a", "b", "c", "d"]
         |> add_equiv [1] ("a", "b") |> assert_eq_edges ("a", "b") [[1]]
         |> add_equiv [2] ("b", "c") |> assert_eq_edges ("b", "c") [[2]]
         |> add_equiv [] ("a", "b")  |> assert_eq_edges ("a", "b") [[]]
         |> add_equiv [3] ("a", "d") |> assert_eq_edges ("a", "d") [[3]]
         |> add_equiv [2] ("a", "d") |> assert_eq_edges ("a", "d") [[2], [3]]
         |> add_equiv [1] ("a", "d") |> assert_eq_edges ("a", "d") [[1], [2]]
         |> add_equiv [] ("a", "d")  |> assert_eq_edges ("a", "d") [[]]
         |> done "test_equiv_basic"

val test_simp_basic =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0]), (3, [1])]
         |> declare_term "[a, b, c, d, e]"
         |> fold add_term ["a", "b", "c", "d", "e"]
         |> update_simp [1] ("e", "d") |> assert_rewrite [1, 2] ("e", "d")
         |> update_simp [2] ("e", "c") |> assert_rewrite [2] ("e", "c")
         |> update_simp [2] ("e", "b") |> assert_rewrite [1, 2] ("e", "b")
         |> update_simp [3] ("e", "a") |> assert_rewrite [1, 2] ("e", "b")
         |> update_simp [1] ("e", "b")
         |> update_simp [1, 2] ("e", "a")
         |> assert_rew_info "e" [([], "e"), ([3], "a"), ([2], "b"),
                                 ([1], "b"), ([1, 2], "a")]
         |> done "test_simp_basic"

val test_head_rep =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f b d"
         |> update_simp [1] ("d", "c")
         |> update_simp [2] ("b", "a")
         |> assert_srew_info "f b d" [([], "f b d"), ([1], "f b c"),
                                      ([2], "f a d"), ([1, 2], "f a c")]
         |> index_reps
         |> assert_head_rep ([], "f a c") [([1, 2], "f b d")]
         |> assert_head_rep ([], "f b c") [([1], "f b d")]
         |> assert_head_rep ([], "f a d") [([2], "f b d")]
         |> assert_head_rep ([], "f b d") [([], "f b d")]
         |> assert_head_rep ([2], "f b c") [([1, 2], "f b d")]
         |> done "test_head_rep"

val test_head_rep2 =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f b c" |> add_term "f a d"
         |> update_simp [1] ("d", "c")
         |> update_simp [2] ("b", "a")
         |> index_reps
         |> assert_head_rep ([], "f a c") [([1], "f a d"), ([2], "f b c")]
         |> assert_head_rep ([1], "f a c") [([1], "f a d"), ([1, 2], "f b c")]
         |> assert_head_rep ([2], "f a c") [([2], "f b c"), ([1, 2], "f a d")]
         |> done "test_head_rep2"

val test_add_term =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_rewrite [1] ("d", "c")
         |> add_rewrite [2] ("b", "a")
         |> index_reps
         |> add_term "f b c" |> add_term "f a d"
         |> assert_head_rep ([], "f a c") [([1], "f a d"), ([2], "f b c")]
         |> assert_eq_edges ("f a d", "f b c") [[1, 2]]
         |> add_term "f a c" |> add_term "f b d"
         |> assert_head_rep ([], "f a c") [([], "f a c"), ([1], "f a d"),
                                           ([2], "f b c"), ([1, 2], "f b d")]
         |> assert_equiv [1, 2] ("f a c", "f b d")
         |> assert_not_equiv [1] ("f a c", "f b d")
         |> assert_not_equiv [2] ("f a c", "f b d")
         |> done "test_add_term"

val test_add_rewrite =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "f a b"]
         |> add_term "f a d"
         |> add_rewrite [1] ("d", "c")
         |> assert_head_rep ([], "f a c") [([1], "f a d")]
         |> add_term "f b d"
         |> assert_head_rep ([], "f b c") [([1], "f b d")]
         |> add_rewrite [2] ("a", "b")
         |> assert_eq_edges ("f a d", "f b d") [[2]]
         |> assert_rew_info "f b d" [([], "f b d"), ([1], "f b c"),
                                     ([2], "f a d"), ([1, 2], "f a c")]
         |> add_term "f b c"
         |> assert_head_rep ([], "f a c") [([1], "f a d"), ([2], "f b c"),
                                           ([1, 2], "f b d")]
         |> done "test_add_rewrite"

val test_simplify =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [0] ("f b d", "e")
         |> add_rewrite [1] ("d", "c")
         |> add_rewrite [2] ("b", "a")
         |> assert_simpl_info "f a c" [([], "f a c"), ([1, 2], "e")]
         |> assert_simpl_info "f a d" [([], "f a d"), ([1], "f a c"),
                                       ([2], "e")]
         |> assert_simpl_info "f b c" [([], "f b c"), ([2], "f a c"),
                                       ([1], "e")]
         |> assert_simpl_info "f b d" [([], "f b d"), ([0], "e")]
         |> assert_simpl [1] ("f a c", "f a c")
         |> assert_simpl [1, 2] ("f a c", "e")
         |> assert_simpl [1] ("f a d", "f a c")
         |> assert_simpl [2] ("f a d", "e")
         |> assert_simpl [1, 2] ("f a d", "e")
         |> add_rewrite [] ("f b d", "e")
         |> assert_simpl_info "f b d" [([], "e")]
         |> add_term "f a c"
         |> assert_equiv [1, 2] ("f a c", "f b d")
         |> done "test_simplify"

val test_simplify2 =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0]), (3, [1])]
         |> declare_term "[a, b, c, d]"
         |> add_rewrite [2] ("b", "c")
         |> add_rewrite [3] ("a", "b")
         |> add_rewrite [1] ("c", "d")
         |> assert_simpl_info "c" [([], "c"), ([2], "b"), ([2, 3], "a")]
         |> assert_simpl_info "d" [([], "d"), ([1], "c"), ([1, 2], "b"),
                                   ([2, 3], "a")]
         |> done "test_simplify2"

val test_simplify3 =
    init |> fold add_prim_id [(0, []), (1, [0])]
         |> declare_term "[a, b, c, d, e, g]"
         |> add_rewrite [0] ("e", "c") |> add_rewrite [0] ("g", "d")
         |> add_rewrite [1] ("e", "b") |> add_rewrite [1] ("g", "a")
         |> add_rewrite [] ("e", "g")
         |> assert_simpl_info "e" [([], "e"), ([0], "c"), ([1], "a")]
         |> assert_simpl_info "g" [([], "e"), ([0], "c"), ([1], "a")]
         |> done "test_simplify3"

val test_head_equivs =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [0] ("f b d", "e")
         |> add_rewrite [1] ("d", "c")
         |> add_rewrite [2] ("b", "a")
         |> assert_head_equivs ([], "c") [([], "c"), ([1], "d")]
         |> assert_head_equivs ([], "f b d") [([], "f b d"), ([0], "e")]
         |> assert_head_equivs ([1], "f b c") [([1], "f b c"), ([1], "e")]
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([1], "e")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([1, 2], "e")]
         |> add_term "f a c"
         |> assert_head_equivs ([], "f b d") [([], "f b d"), ([0], "e")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([1, 2], "e")]
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([1], "e")]
         |> done "test_head_equivs"

val test_head_equivs2 =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0]), (3, [1])]
         |> declare_term "[a, b, c, d]"
         |> add_rewrite [2] ("b", "c")
         |> add_rewrite [3] ("a", "b")
         |> assert_head_equivs ([], "b") [([], "b"), ([2], "c"), ([3], "a")]
         |> add_rewrite [1] ("c", "d")
         |> assert_head_equivs ([], "b") [([], "b"), ([2], "c"), ([3], "a"),
                                          ([1, 2], "d")]
         |> done "test_head_equivs2"

val test_head_equivs3 =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [] ("b", "a")
         |> add_rewrite [1] ("f b d", "e")
         |> add_rewrite [2] ("f a d", "e")
         (* Both fbd and fad are ok in the result. *)
         |> assert_head_equivs ([], "f a d") [([], "f b d"), ([1], "e"),
                                              ([2], "e")]
         |> assert_head_equivs ([], "f b d") [([], "f a d"), ([1], "e"),
                                              ([2], "e")]
         |> done "test_head_equivs3"

val test_head_equivs4 =
    init |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
         |> fold declare_term ["[a, b, c, d]", "[f a b, e]"]
         |> add_rewrite [1] ("b", "a")
         |> add_rewrite [] ("f b c", "e")
         |> add_rewrite [2] ("f a c", "e")  (* Note fbc ~ fac under 2. *)
         |> assert_head_equivs ([], "f b c") [([], "f b c"), ([], "e"),
                                              ([2], "f a c")]
         |> assert_head_equivs ([], "f a c") [([], "f a c"), ([1], "e"),
                                              ([2], "e"), ([2], "f b c")]
         |> done "test_head_equivs4"

(* Simplify with nat variables. *)
val test_simplify_nat =
    init |> declare_term "[a::nat, b, c]"
         |> add_rewrite [] ("a + b", "b + a")
         |> add_rewrite [] ("a", "c")
         |> assert_simpl [] ("b + c", "a + b")
         |> assert_equiv [] ("b + c", "a + b")
         |> done "test_simplify_nat"

val test_fo_match =
    init |> declare_term "[a::nat, c, d, e]"
         |> add_rewrite [] ("c * d + c * e", "c * (d + e)")
         |> assert_match (("(?a::nat) + (?b + ?c)", "a + c * (d + e)"),
                          [([], "a + (c * d + c * e)")])
         |> done "test_fo_match"

val test_fo_match2 =
    init |> declare_term "[k::nat, l]"
         |> add_rewrite [] ("k", "l")
         |> assert_match (("(?a::nat) + ?a", "k + l"), [([], "k + k")])
         |> done "test_fo_match2"

val test_fo_match_list =
    init |> declare_term "[k::nat, l, b]"
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
         |> done "test_fo_match_list"

val test_fo_match_diff =
    init |> fold declare_term ["[n::nat, k]", "g n k"]
         |> declare_pat "[?a::nat, ?b]"
         |> assert_match_diff ("n", "k") ("g ?a ?a", "g n k") [([], "g n n")]
         |> assert_match_diff ("n", "k") ("g ?a ?b", "g n k") []
         |> done "test_fo_match_diff"

(* Quantifiers. *)
val test_fo_match_quant =
    init |> declare_term "n::nat"
         |> assert_match (("EX (x::nat) (y::nat). ?A x y & ?B x",
                           "EX m k. n = m * k & 1 < m"),
                          [([], "EX m k. n = m * k & 1 < m")])
         |> done "test_fo_match_quant"

(* Multiple matches. *)
val test_fo_match_mult =
    init |> declare_term "[a::nat, b, c]"
         |> add_rewrite [] ("a + (b + c)", "a + b + c")
         |> add_rewrite [] ("b + c", "c + b")
         |> add_rewrite [] ("a + (c + b)", "a + c + b")
         (* a + (b + c) and a + (c + b) are both acceptable. *)
         |> assert_match (("(?a::nat) + ?b", "a + b + c"),
                          [([], "a + (c + b)"), ([], "a + b + c"),
                           ([], "a + c + b")])
         |> done "test_fo_match_mult"

(* Quantifiers, match diff. *)
val test_fo_match_quant3 =
    init |> fold declare_term ["[n::nat, p]", "Q::(nat => bool)"]
         |> assert_match_diff ("n", "0::nat")
         ("EX (k::nat). k dvd 0 & ?A k", "EX p. p dvd n & Q p")
         [([], "EX p. p dvd 0 & Q p")]
         |> done "test_fo_match_quant3"

(* More match diff tests. *)
val test_fo_match_diff2 =
    init |> declare_term "[a::nat, b, c, d]"
         |> add_prim_id (0, [])
         |> add_rewrite [0] ("b * (c + d)", "b * c + b * d")
         |> assert_match (("(?a::nat) + (?b + ?c)", "a + b * (c + d)"),
                          [([0], "a + (b * c + b * d)")])
         |> assert_match_diff ("b * (c + d)", "b * c + b * d")
         ("(?a::nat) + (?b + ?c)", "a + b * (c + d)")
         [([], "a + (b * c + b * d)")]
         |> done "test_fo_match_diff2"

val test_fo_match_diff3 =
    init |> declare_term "[a::nat, b]"
         |> declare_pat "?a::nat"
         |> assert_match_diff ("a", "b") ("?a = ?a", "a = b") [([], "a = a")]
         |> add_rewrite [] ("b", "a")
         |> assert_match_diff ("a", "b") ("?a = ?a", "a = b") []
         |> done "test_fo_match_diff3"

val test_fo_match_eq =
    init |> declare_term "[x::nat, y, z]"
         |> add_rewrite [] ("x", "y")
         |> assert_match (("?A = ?A", "x = y"), [([], "x = x")])
         |> assert_match (("EX a. ?A a = ?A a", "EX a. x + a = y + a"),
                          [([], "EX a. x + a = x + a")])
         |> assert_match (("EX a. ?A a = ?A a", "EX a. x + a = z + a"), [])
         |> done "test_fo_match_eq"

(* Test on matching of AC functions. *)

val test_fo_match_ac =
    tbl |> declare_term "[m::nat, n]"
        |> assert_match (("gcd (?a::nat) ?b", "gcd m n"),
                         [([], "gcd m n"), ([], "gcd n m")])
        |> done "test_fo_match_ac"

val test_fo_match_ac2 =
    tbl |> fold declare_term ["[p::nat, n]", "Q::(nat => bool)"]
        |> assert_match (("(Q (?a::nat), gcd ?a ?b)", "(Q p, gcd n p)"),
                         [([], "(Q p, gcd p n)")])
        |> done "test_fo_match_ac2"

(* AC functions with more than two terms. *)
val test_fo_match_ac3 =
    tbl |> declare_term "[a::nat, b, c, d, e]"
        |> assert_match (("?a + c + e + a + b", "a + b + c + d + e"),
                         [([], "d + c + e + a + b")])
        |> done "test_fo_match_ac3"

(* AC functions with more than two terms, combined with table match. *)
val test_fo_match_ac4 =
    tbl |> declare_term "[a::nat, b, c, d, e]"
        |> add_rewrite [] ("a", "b") |> add_rewrite [] ("c", "d")
        |> assert_match (("?a + b + c", "a + d + e"), [([], "e + b + c")])
        |> done "test_fo_match_ac4"

(* Matching schematic variables to more than one term. *)
val test_fo_match_ac5 =
    tbl |> declare_term "[a::nat, b, c, d, k, l, m, n]"
        |> assert_match (("c + ?a", "c + k + l"), [([], "c + (k + l)")])
        |> assert_match (("?a + n", "k + l + n"), [([], "k + l + n")])
        |> assert_match (("((?a::nat) + ?b, ?b)", "(a + b + c + d, b + d)"),
                         [([], "(a + c + (b + d), b + d)")])
        (* Tricky since pattern has no specified type. *)
        |> assert_match_diff ("k", "2::nat") ("?a * 2", "k * m") [([], "m * 2")]
        (* As well test handling of units here. *)
        |> assert_match_diff ("k", "1::nat") ("?a * 1", "k * m") [([], "m * 1")]
        |> assert_num_match ("~ (?A | ?B)", "~ (A | B | C)") 6
        |> done "test_fo_match_ac5"

(* More AC tests. *)
val test_fo_match_ac6 =
    tbl |> declare_term "[a::nat, b, c, d]" |> declare_pat "?a::nat"
        (* Pattern is not associated in the usual order. *)
        |> assert_match (("?a + (?b + ?c)", "a + b + c"), [])
        |> add_rewrite [] ("a + b * (c + d)", "a + b * c + b * d")
        |> assert_match (("(?a + ?b + ?c, ?a, ?b)",
                          "(a + b * (c + d), a, b * c)"),
                         [([], "(a + b * c + b * d, a, b * c)")])
        |> done "test_fo_match_ac6"

(* Count of matchings on 4 or 5 terms. *)
val test_fo_match_ac7 =
    tbl |> declare_term "[a::nat, b, c, d, e]" |> declare_pat "?a::nat"
        |> assert_num_match ("?a", "a + b + c + d + e") 1
        |> assert_num_match ("?a + ?b", "a + b + c + d + e") 30
        |> assert_num_match ("?a + ?b + ?c", "a + b + c + d + e") 150
        |> assert_num_match ("?a + ?b + ?c + ?d", "a + b + c + d + e") 240
        |> assert_num_match ("?a + ?b + ?c + ?d", "a + b + c + d") 24
        |> done "test_fo_match_ac7"

(* Use of distributive law and reverse associative law only. *)
val test_fo_match_ac8 =
    tbl |> declare_term "[a::nat, b, c, d, e, f]" |> declare_pat "?a::nat"
        |> add_rewrite [] ("c * d + c * e", "c * (d + e)")
        |> assert_equiv [] ("c * d + c * e", "c * (d + e)")
        |> assert_num_match ("?a", "a + b + c * (d + e) + f") 1
        |> assert_num_match ("?a + ?b", "a + b + c * (d + e) + f") 30
        |> assert_num_match ("?a + ?b + ?c", "a + b + c * (d + e) + f") 150
        |> assert_num_match ("?a + ?b + ?c + ?d", "a + b + c * (d + e) + f") 240
        |> assert_num_match ("?a + ?b + ?c + ?d + ?e",
                             "a + b + c * (d + e) + f") 120
        |> done "test_fo_match_ac8"

val test_get_ac_head_equivs =
    tbl |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
        |> declare_term "[x::nat, y, p, q, z, u, v]"
        |> add_rewrite [1] ("x", "p * z")
        |> add_rewrite [2] ("y", "q * z")
        |> assert_head_equivs ([], "x * y")
        [([], "x * y"), ([1], "p * y * z"), ([2], "q * x * z"),
         ([1, 2], "p * q * z * z")]
        |> add_rewrite [1] ("u", "1::nat")
        |> add_rewrite [2] ("v", "1::nat")
        |> assert_head_equivs_t "x * y" ([], "u * v") [([], "u * v")]
        |> assert_head_equivs_t "u" ([], "u * v") [([2], "u")]
        |> assert_head_equivs_t "1" ([], "u * v") [([1, 2], "1::nat")]
        |> done "test_get_ac_head_equivs"

(* Expanding one of the AC terms for matching. *)
val test_fo_match_ac9 =
    tbl |> declare_term "[x::nat, p, y, z]"
        |> add_rewrite [] ("x", "p * z")
        |> assert_match (("p * ?q", "x * y"), [([], "p * (y * z)")])
        |> done "test_fo_match_ac9"

val test_ac_equiv =
    tbl |> declare_term "[n::nat, m, k]"
        |> add_rewrite [] ("n", "m * k")
        |> add_rewrite [] ("1::nat", "k")
        |> add_rewrite [] ("1::nat", "m")
        |> assert_equiv [] ("m", "n")
        |> done "test_ac_equiv"

(* Some tests about handling units. *)
val test_fo_match_ac10 =
    tbl |> declare_term "[x::nat, y]"
        |> add_prim_id (0, [])
        |> add_rewrite [0] ("x", "1::nat")
        |> assert_match (("y", "x * y"), [([0], "y")])
        |> assert_match (("x * y", "x * y"), [([], "x * y")])
        |> add_rewrite [] ("x", "1::nat")
        |> assert_match (("x * y", "x * y"), [([], "x * y")])
        |> done "test_fo_match_ac10"

(* Should not go into infinite loop. *)
val test_fo_match_ac11 =
    tbl |> add_prim_id (0, [])
        |> declare_term "[x::nat, y]"
        |> add_rewrite [] ("y", "x * y")
        |> assert_match (("y", "x * y"), [([], "y")])
        |> add_rewrite [0] ("x", "1::nat")
        |> assert_match (("x * y", "x * y"), [([], "x * y")])
        |> done "test_fo_match_ac11"

val test_fo_match_ac12 =
    tbl |> fold add_prim_id [(0, []), (1, [0])]
        |> declare_term "[p::nat, q, x, y, z]"
        |> add_rewrite [0] ("y", "1::nat")
        |> add_rewrite [1] ("z", "1::nat")
        |> add_rewrite [0] ("p", "q")
        |> assert_match (("(p, x * y)", "(q, x * y)"), [([0], "(p, x * y)")])
        |> assert_match (("(p, x * z)", "(q, x * z)"), [([0], "(p, x * z)")])
        |> assert_match (("(p, x)", "(q, x * y)"), [([0], "(p, x)")])
        |> assert_match (("(p, x)", "(q, x * z)"), [([1], "(p, x)")])
        |> assert_match (("(p, x * y)", "(q, x)"), [([0], "(p, x * y)")])
        |> assert_match (("(p, x * z)", "(q, x)"), [([1], "(p, x * z)")])
        |> done "test_fo_match_ac12"

val test_const_simp =
    tbl |> fold add_prim_id [(0, []), (1, [0]), (2, [0])]
        |> declare_term "[x::nat, y]"
        |> add_rewrite [1] ("x", "1::nat")
        |> add_rewrite [2] ("y", "1::nat")
        |> assert_head_equivs ([], "1::nat") [([], "1::nat")]
        |> assert_head_equivs ([], "x") [([], "x"), ([1], "1::nat")]
        |> add_rewrite [2] ("x", "0::nat")
        |> assert_head_equivs ([], "1::nat") [([], "1::nat"),
                                              ([1, 2], "0::nat")]
        |> done "test_const_simp"

val test_ac_numc =
    tbl |> declare_term "m::nat"
        |> add_rewrite [] ("m", "3::nat")
        |> assert_match (("(?NUMC1::nat) + ?NUMC2", "m + m"),
                         [([], "(3::nat) + 3")])
        |> done "test_ac_numc"

val test_match_type =
    tbl |> assert_match (("image_mset ?f {#}", "{#i. i :# {#}#}"),
                         [([], "{#i. i :# {#}#}")])
        (* sorted [] has concrete type, but not []. *)
        |> assert_match (("sorted []", "sorted []"), [([], "sorted []")])
        |> done "test_match_type"

val test_fo_match_ac13 =
    tbl |> declare_term "[r::rat, s]" |> declare_pat "?r::rat"
        |> assert_match (("?r / 2", "r * inverse 2"), [([], "r / 2")])
        |> assert_match (("?r + ?s - ?s", "r + s + -s"), [([], "r + s - s")])
        |> done "test_fo_match_ac13"

(* Difference between ?NUMC and ?NUMCu, between ?a and ?au. *)
val test_fo_match_ac14 =
    tbl |> declare_term "[k::int, m, n, a, b]"
        |> declare_pat "[?NUMC::int, ?NUMCu, ?a, ?au, ?mu]"
        |> assert_match (("?NUMC * ?m * ?m", "m * m"), [])
        |> assert_match (("?NUMCu * ?m * ?m", "m * m"), [([], "1 * m * m")])
        |> assert_match (("?NUMCu * ?m * ?m", "k * m * m"), [])
        |> assert_match (("?NUMCu * ?m * ?m", "2 * m * m"),
                         [([], "2 * m * m")])
        |> assert_match (("?au * ?b", "b"), [([], "1 * b")])
        |> assert_match (("?au * ?b", "a * b"), [([], "a * b"), ([], "b * a"),
                                                 ([], "1 * (a * b)")])
        |> assert_match (("?mu * ?n", "n"), [([], "1 * n")])
        |> assert_match (("?mu + (-?n)", "-n"), [([], "0 + (-n)")])
        |> assert_match (("?mu + (?n * ?NUMCu)", "a"), [([], "0 + (a * 1)")])
        |> assert_match (("?mu + (?n * ?NUMCu)", "a * 2"),
                         [([], "0 + (a * 2)"), ([], "0 + (a * 2) * 1")])
        |> done "test_fo_match_ac14"

val test_fo_match_quant4 =
    tbl |> declare_term "[a::nat, n]"
        |> assert_match (("(EX i. ?f i < 0, ?f ?n)",
                          "(EX i. i + a < 0, n + a)"),
                         [([], "(EX i. i + a < 0, n + a)")])
        |> done "test_fo_match_quant4"

end;  (* local *)
