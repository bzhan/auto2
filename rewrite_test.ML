(* Unit test for rewrite.ML. *)

local

  open RewriteTable
  val a = @{term "a::nat"}
  val b = @{term "b::nat"}
  val c = @{term "c::nat"}
  val d = @{term "d::nat"}
  val e = @{term "e::nat"}
  val f = @{term "f::(nat => nat => nat)"}
  val g = @{term "g::nat"}
  val fac = f $ a $ c
  val fad = f $ a $ d
  val fbc = f $ b $ c
  val fbd = f $ b $ d
  val ctxt = @{context}

  (* Rewriting information. *)
  val thy = @{theory}
  val thy' = thy |> add_logic_ac_data |> Nat_Arith.add_arith_ac_data
  val ctxt' = Proof_Context.init_global thy'

in

fun add_prim_id id prim_id lat =
    let
      val (prim_id', lat') = BoxID.add_prim_id id lat
      val _ = assert (prim_id = prim_id') "add_prim_id"
    in
      lat'
    end

(* Lattice: 2 -> 1 -> 0 and 3 -> 1. *)
val lattice = BoxID.empty |> add_prim_id [] 0
                          |> add_prim_id [0] 1
                          |> add_prim_id [0] 2
                          |> add_prim_id [1] 3

val init = empty ctxt |> map_lat (K lattice)

(* Conversion between (id, th) used in rewrite.ML and (id, t) used in
   test cases.
 *)
fun to_term_info (id, th) = (id, rhs_of th)
(* Comparison of list of box_ids. *)
val eq_id_list = eq_set (op =)
(* Comparison of list of terms. *)
val eq_term_list = eq_set (op aconv)
(* Comparison of list of (box_id, term) pairs. *)
val eq_info_list = eq_set (eq_pair (op =) (op aconv))

(* info is expected, in box_id * term form, info' is returned value,
   in box_id * thm form (to be printed).
 *)
fun assert_eq_info (info, info') txt tbl =
    if eq_info_list (info, map to_term_info info') then tbl else
    let val _ = tracing ("got " ^ print_infos ctxt info') in raise AUTO2 txt end

fun assert_eq_edges (t1, t2) ids txt tbl =
    let
      val ids' = (equiv_neighs tbl t1)
                     |> map to_term_info
                     |> filter (fn (_, t2') => t2 aconv t2') |> map fst
    in
      if eq_id_list (ids, ids') then tbl else
      let val _ =
              tracing ("got " ^ (string_of_list BoxID.string_of_box_id ids'))
      in raise AUTO2 txt end
    end

fun assert_rewrite id (t, t') txt tbl =
    let val _ = assert (rhs_of (get_rewrite id tbl t) aconv t') txt
    in tbl end

fun assert_rew_info t info txt tbl =
    assert_eq_info (info, get_rewrite_info tbl t) txt tbl

fun assert_srew_info t info txt tbl =
    assert_eq_info (info, get_subterm_rewrite_info tbl t) txt tbl

fun assert_head_rep (id, t) info txt tbl =
    assert_eq_info (info, get_head_rep_with_id_th tbl (id, refl tbl t)) txt tbl

fun assert_equiv id (t, t') txt tbl =
    let val _ = assert (is_equiv id tbl (t, t')) txt in tbl end
fun assert_not_equiv id (t, t') txt tbl =
    let val _ = assert (not (is_equiv id tbl (t, t'))) txt in tbl end

fun assert_simpl_info t info txt tbl =
    assert_eq_info (info, simplify_info tbl t) txt tbl
fun assert_simpl id (t, t') txt tbl =
    let val _ = assert (rhs_of (simplify id tbl t) aconv t') txt
    in tbl end

fun assert_head_equivs (id, u) info txt tbl =
    assert_eq_info (info, (get_head_equiv tbl u)
                              |> maps snd |> map fst
                              |> merge_box_with_info tbl id) txt tbl

fun assert_head_equivs_t t (id, u) info txt tbl =
    assert_eq_info (info, (get_head_equiv_with_t tbl (id, u) t)
                              |> map fst) txt tbl

(* Check th is actually t(env) == u. *)
fun check_info (t, u) txt tbl ((_, inst), th) =
    let
      val t' = subst_term_norm inst t
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of th)
    in
      if lhs aconv t' andalso rhs aconv u then ()
      else let
        val thy = theory_of tbl
        val _ = tracing ("inst does not match th.\nt', u' = " ^
                         (pretty_terms_thy thy [t', u] |> str) ^
                         "\nth = " ^
                         (pretty_term_thy thy (Thm.prop_of th) |> str))
      in raise AUTO2 txt end
    end

fun assert_match (t, u) info txt tbl =
    let
      val info' = fo_table_match [] tbl (t, u)
      val _ = map (check_info (t, u) txt tbl) info'
      val info'' = map (fn ((id, _), th) => (id, meta_sym th)) info'
    in
      assert_eq_info (info, info'') txt tbl
    end

fun assert_match_list pairs info txt tbl =
    let
      val info' = fo_table_match_list [] tbl pairs
      fun check_info_list (instsp, ths) =
          let
            fun check_pair ((t, u), th) = check_info (t, u) txt tbl (instsp, th)
          in
            map check_pair (map snd pairs ~~ ths)
          end
      val _ = map check_info_list info'
      val info'' = map (fn ((id, _), ths) => (id, map meta_sym ths)) info'
      val eq_info_list' = eq_set (eq_pair (op =) (eq_list (op aconv)))
      fun to_term_info' (id, ths) = (id, map rhs_of ths)
    in
      if eq_info_list' (info, map to_term_info' info'') then tbl
      else let val _ = tracing ("got " ^ print_infos' ctxt info'')
           in raise AUTO2 txt end
    end

fun assert_match_diff id (lhs, rhs) (t, u) info txt tbl =
    let
      val tbl' = tbl |> append_rewrite (lhs, rhs)
      val rtype = LAST (tbl', id)
      val info' = fo_table_match [] tbl' (t, u) |> replace_id_for_type rtype
      val _ = map (check_info (t, u) txt tbl) info'
      val info'' = info' |> map (fn ((id, _), th) => (id, meta_sym th))
    in
      assert_eq_info (info, info'') txt tbl
    end

(* count is expected, count is returned value (to be printed). *)
fun assert_count count count' txt tbl =
    if count = count' then tbl else
    let val _ = tracing ("got " ^ string_of_int count') in raise AUTO2 txt end

fun assert_num_match (t, u) count txt tbl =
    let val count' = length (fo_table_match [] tbl (t, u))
    in assert_count count count' txt tbl end

fun assert_num_match_with_id id (t, u) count txt (tbl as {lat, ...}) =
    let val matches = (fo_table_match [] tbl (t, u))
                          |> filter (BoxID.is_eq_descendent lat id o fst o fst)
    in assert_count count (length matches) txt tbl end

(* Modification functions using terms. *)
fun add_equiv' id (t1, t2) tbl =
    add_equiv (id, assume_meta_eq (theory_of tbl) (t1, t2)) tbl
fun add_term' t tbl = add_term ([], t) tbl

fun index_reps tbl =
    let
      fun index_reps_t t =
          fold update_subsimp (get_subterm_rewrite_info tbl t)
    in
      fold index_reps_t (get_all_terms tbl) tbl
    end

val test_equiv_basic =
    let
      fun err n = "test_equiv_basic: " ^ (string_of_int n)
    in
      init |> add_term' a |> add_term' b |> add_term' c |> add_term' d
           |> add_equiv' [1] (a, b) |> assert_eq_edges (a, b) [[1]] (err 0)
           |> add_equiv' [2] (b, c) |> assert_eq_edges (b, c) [[2]] (err 1)
           |> add_equiv' [] (a, b)  |> assert_eq_edges (a, b) [[]] (err 2)
           |> add_equiv' [3] (a, d) |> assert_eq_edges (a, d) [[3]] (err 3)
           |> add_equiv' [2] (a, d) |> assert_eq_edges (a, d) [[2], [3]] (err 4)
           |> add_equiv' [1] (a, d) |> assert_eq_edges (a, d) [[1], [2]] (err 5)
           |> add_equiv' [] (a, d)  |> assert_eq_edges (a, d) [[]] (err 6)
           |> to_string_full |> prefix "test_equiv_basic -- " |> writeln
    end

fun update_simp' id (t1, t2) tbl =
    update_simp (id, assume_meta_eq (theory_of tbl) (t1, t2)) tbl

val test_simp_basic =
    let
      fun err n = "test_simp_basic: " ^ (string_of_int n)
    in
      init |> add_term' a |> add_term' b |> add_term' c |> add_term' d
           |> add_term' e
           |> update_simp' [1] (e, d) |> assert_rewrite [1, 2] (e, d) (err 0)
           |> update_simp' [2] (e, c) |> assert_rewrite [2] (e, c) (err 1)
           |> update_simp' [2] (e, b) |> assert_rewrite [1, 2] (e, b) (err 2)
           |> update_simp' [3] (e, a) |> assert_rewrite [1, 2] (e, b) (err 3)
           |> update_simp' [1] (e, b)
           |> update_simp' [1, 2] (e, a)
           |> assert_rew_info e [([], e), ([3], a), ([2], b), ([1], b),
                                 ([1, 2], a)] (err 4)
           |> to_string_full |> prefix "test_simp_basic -- " |> writeln
    end

val test_head_rep =
    let
      fun err n = "test_head_rep: " ^ (string_of_int n)
    in
      init |> add_term' fbd
           |> update_simp' [1] (d, c)
           |> update_simp' [2] (b, a)
           |> assert_srew_info fbd [([], fbd), ([1], fbc),
                                    ([2], fad), ([1, 2], fac)] (err 0)
           |> index_reps
           |> assert_head_rep ([], fac) [([1, 2], fbd)] (err 1)
           |> assert_head_rep ([], fbc) [([1], fbd)] (err 2)
           |> assert_head_rep ([], fad) [([2], fbd)] (err 3)
           |> assert_head_rep ([], fbd) [([], fbd)] (err 4)
           |> assert_head_rep ([2], fbc) [([1, 2], fbd)] (err 5)
           |> to_string_full |> prefix "test_head_rep -- " |> writeln
    end

val test_head_rep2 =
    let
      fun err n = "test_head_rep2: " ^ (string_of_int n)
    in
      init |> add_term' fbc |> add_term' fad
           |> update_simp' [1] (d, c)
           |> update_simp' [2] (b, a)
           |> index_reps
           |> assert_head_rep ([], fac) [([1], fad), ([2], fbc)] (err 0)
           |> assert_head_rep ([1], fac) [([1], fad), ([1, 2], fbc)] (err 1)
           |> assert_head_rep ([2], fac) [([2], fbc), ([1, 2], fad)] (err 2)
           |> to_string_full |> prefix "test_head_rep2 -- " |> writeln
    end

val test_add_term =
    let
      fun err n = "test_add_term: " ^ (string_of_int n)
    in
      init |> add_rewrite [1] (d, c)
           |> add_rewrite [2] (b, a)
           |> index_reps
           |> add_term' fbc |> add_term' fad
           |> assert_head_rep ([], fac) [([1], fad), ([2], fbc)] (err 0)
           |> assert_eq_edges (fad, fbc) [[1, 2]] (err 1)
           |> add_term' fac |> add_term' fbd
           |> assert_head_rep ([], fac) [([], fac), ([1], fad), ([2], fbc),
                                         ([1, 2], fbd)] (err 2)
           |> assert_equiv [1, 2] (fac, fbd) (err 3)
           |> assert_not_equiv [1] (fac, fbd) (err 4)
           |> assert_not_equiv [2] (fac, fbd) (err 5)
           |> to_string_full |> prefix "test_add_term -- " |> writeln
    end

val test_add_rewrite =
    let
      fun err n = "test_add_rewrite: " ^ (string_of_int n)
    in
      init |> add_term' fad
           |> add_rewrite [1] (d, c)
           |> assert_head_rep ([], fac) [([1], fad)] (err 0)
           |> add_term' fbd
           |> assert_head_rep ([], fbc) [([1], fbd)] (err 1)
           |> add_rewrite [2] (a, b)
           |> assert_eq_edges (fad, fbd) [[2]] (err 2)
           |> assert_rew_info fbd [([], fbd), ([1], fbc), ([2], fad),
                                   ([1, 2], fac)] (err 3)
           |> add_term' fbc
           |> assert_head_rep ([], fac) [([1], fad), ([2], fbc),
                                         ([1, 2], fbd)] (err 4)
           |> to_string_full |> prefix "test_add_rewrite -- " |> writeln
    end

val test_simplify =
    let
      fun err n = "test_simplify: " ^ (string_of_int n)
    in
      init |> add_rewrite [0] (fbd, e)
           |> add_rewrite [1] (d, c)
           |> add_rewrite [2] (b, a)
           |> assert_simpl_info fac [([], fac), ([1, 2], e)] (err 0)
           |> assert_simpl_info fad [([], fad), ([1], fac), ([2], e)] (err 1)
           |> assert_simpl_info fbc [([], fbc), ([2], fac), ([1], e)] (err 2)
           |> assert_simpl_info fbd [([], fbd), ([0], e)] (err 3)
           |> assert_simpl [1] (fac, fac) (err 4)
           |> assert_simpl [1, 2] (fac, e) (err 5)
           |> assert_simpl [1] (fad, fac) (err 6)
           |> assert_simpl [2] (fad, e) (err 7)
           |> assert_simpl [1, 2] (fad, e) (err 8)
           |> add_rewrite [] (fbd, e)
           |> assert_simpl_info fbd [([], e)] (err 9)
           |> add_term' fac
           |> assert_equiv [1, 2] (fac, fbd) (err 10)
           |> to_string_full |> prefix "test_simplify -- " |> writeln
    end

val test_simplify2 =
    let
      fun err n = "test_simplify2: " ^ (string_of_int n)
    in
      init |> add_rewrite [2] (b, c)
           |> add_rewrite [3] (a, b)
           |> add_rewrite [1] (c, d)
           |> assert_simpl_info c [([], c), ([2], b), ([2, 3], a)] (err 0)
           |> assert_simpl_info d [([], d), ([1], c), ([1, 2], b),
                                   ([2, 3], a)] (err 1)
           |> to_string_full |> prefix "test_simplify2 -- " |> writeln
    end

val test_simplify3 =
    let
      fun err n = "test_simplify3: " ^ (string_of_int n)
    in
      init |> add_rewrite [0] (e, c) |> add_rewrite [0] (g, d)
           |> add_rewrite [1] (e, b) |> add_rewrite [1] (g, a)
           |> add_rewrite [] (e, g)
           |> assert_simpl_info e [([], e), ([0], c), ([1], a)] (err 0)
           |> assert_simpl_info g [([], e), ([0], c), ([1], a)] (err 1)
           |> to_string_full |> prefix "test_simplify3 -- " |> writeln
    end

val test_head_equivs =
    let
      fun err n = "test_head_equivs: " ^ (string_of_int n)
    in
      init |> add_rewrite [0] (fbd, e)
           |> add_rewrite [1] (d, c)
           |> add_rewrite [2] (b, a)
           |> assert_head_equivs ([], c) [([], c), ([1], d)] (err 0)
           |> assert_head_equivs ([], fbd) [([], fbd), ([0], e)] (err 1)
           |> assert_head_equivs ([1], fbc) [([1], fbc), ([1], e)] (err 2)
           |> assert_head_equivs ([], fbc) [([], fbc), ([1], e)] (err 3)
           |> assert_head_equivs ([], fac) [([], fac), ([1, 2], e)] (err 4)
           |> add_term' fac
           |> assert_head_equivs ([], fbd) [([], fbd), ([0], e)] (err 5)
           |> assert_head_equivs ([], fac) [([], fac), ([1, 2], e)] (err 6)
           |> assert_head_equivs ([], fbc) [([], fbc), ([1], e)] (err 7)
           |> to_string_full |> prefix "test_head_equivs -- " |> writeln
    end

val test_head_equivs2 =
    let
      fun err n = "test_head_equivs2: " ^ (string_of_int n)
    in
      init |> add_rewrite [2] (b, c)
           |> add_rewrite [3] (a, b)
           |> assert_head_equivs ([], b) [([], b), ([2], c), ([3], a)] (err 0)
           |> add_rewrite [1] (c, d)
           |> assert_head_equivs ([], b) [([], b), ([2], c), ([3], a),
                                          ([1, 2], d)] (err 1)
           |> to_string_full |> prefix "test_head_equivs2 -- " |> writeln
    end

val test_head_equivs3 =
    let
      fun err n = "test_head_equivs3: " ^ (string_of_int n)
    in
      init |> add_rewrite [] (b, a)
           |> add_rewrite [1] (fbd, e)
           |> add_rewrite [2] (fad, e)
           (* Both fbd and fad are ok in the result. *)
           |> assert_head_equivs ([], fad) [([], fbd), ([1], e),
                                            ([2], e)] (err 0)
           |> assert_head_equivs ([], fbd) [([], fad), ([1], e),
                                            ([2], e)] (err 1)
           |> to_string_full |> prefix "test_head_equivs3 -- " |> writeln
    end

val test_head_equivs4 =
    let
      fun err n = "test_head_equivs4: " ^ (string_of_int n)
    in
      init |> add_rewrite [1] (b, a)
           |> add_rewrite [] (fbc, e)
           |> add_rewrite [2] (fac, e)  (* Note fbc ~ fac under 2. *)
           |> assert_head_equivs ([], fbc) [([], fbc), ([], e),
                                            ([2], fac)] (err 0)
           |> assert_head_equivs ([], fac) [([], fac), ([1], e), ([2], e),
                                            ([2], fbc)] (err 1)
           |> to_string_full |> prefix "test_head_equivs4 -- " |> writeln
    end

(* Simplify with nat variables. *)
val test_simplify_nat =
    let
      fun err n = "test_simplify_nat: " ^ (string_of_int n)
      val tbl =
          init |> add_rewrite [] (@{term "(a::nat)+b"}, @{term "(b::nat)+a"})
               |> add_rewrite [] (@{term "a::nat"}, @{term "c::nat"})
      val bplusc = @{term "(b::nat)+c"}
      val aplusb = @{term "(a::nat)+b"}
    in
      tbl |> assert_simpl [] (bplusc, aplusb) (err 0)
          |> assert_equiv [] (bplusc, aplusb) (err 1)
          |> to_string |> prefix "test_simplify_nat -- " |> writeln
    end

val test_fo_match =
    let
      fun err n = "test_fo_match: " ^ (string_of_int n)
      val tbl = init |> add_rewrite [] (@{term "(c::nat)*d + c*e"},
                                        @{term "(c::nat)*(d+e)"})
      val trm = @{term "(a::nat) + c*(d+e)"}
      val pat = @{term_pat "(?a::nat) + (?b + ?c)"}
      val ans = @{term "(a::nat) + (c*d + c*e)"}
    in
      tbl |> assert_match (pat, trm) [([], ans)] (err 0)
          |> to_string |> prefix "test_fo_match -- " |> writeln
    end

val test_fo_match2 =
    let
      fun err n = "test_fo_match2: " ^ (string_of_int n)
      val tbl = init |> add_rewrite [] (@{term "k::nat"}, @{term "l::nat"})
      val trm = @{term "(k::nat) + l"}
      val pat = @{term_pat "(?a::nat) + ?a"}
      val ans = @{term "(k::nat) + k"}
    in
      tbl |> assert_match (pat, trm) [([], ans)] (err 0)
          |> to_string |> prefix "test_fo_match2 -- " |> writeln
    end

val test_fo_match_list =
    let
      fun err n = "test_fo_match_list: " ^ (string_of_int n)
      val k = @{term "k::nat"}
      val l = @{term "l::nat"}
      val va = @{term_pat "?a::nat"}
      val vab = @{term_pat "(?a::nat) + b"}
      val tbl = init |> add_rewrite [] (k, l)
    in
      tbl |> (assert_match_list [(false, (va, k)), (false, (va, l))]
                                [([], [k, k])] (err 0))
          |> assert_match_list [(false, (va, k)), (true, (va, l))] [] (err 1)
          |> (assert_match_list [(true, (va, k)), (false, (va, l))]
                                [([], [k, k])] (err 2))
          |> (assert_match_list
                  [(true, (vab, @{term "(k::nat) + b"})),
                   (true, (vab, @{term "(l::nat) + b"}))]
                  [([], [@{term "(k::nat) + b"}, @{term "(k::nat) + b"}])]
                  (err 3))
          |> to_string |> prefix "test_fo_match_list -- " |> writeln
    end

val test_fo_match_diff =
    let
      fun err n = "test_fo_match_diff: " ^ (string_of_int n)
      val n = @{term "n::nat"}
      val k = @{term "k::nat"}
      val g = @{term "g::nat => nat => bool"}
      val gnk = g $ n $ k
      val gnn = g $ n $ n
      val va = @{term_pat "?a::nat"}
      val vb = @{term_pat "?b::nat"}
      val gva = g $ va $ va
      val gvavb = g $ va $ vb
      val tbl' = init |> append_rewrite (n, k)
    in
      (tbl' |> assert_head_equivs ([], n) [([], n), ([4], k)] (err 0)
            |> assert_match (gva, gnk) [([4], gnn)] (err 1)
            |> assert_match (gvavb, gnk) [([], gnk)] (err 2)
            |> to_string |> prefix "test_fo_match_diff -- " |> writeln,
       init |> assert_match_diff [] (n, k) (gva, gnk) [([], gnn)] (err 3)
            |> assert_match_diff [] (n, k) (gvavb, gnk) [] (err 4)
            |> to_string |> prefix "test_fo_match_diff' -- " |> writeln)
    end

(* Quantifiers. *)
val test_fo_match_quant =
    let
      fun err n = "test_fo_match_quant: " ^ (string_of_int n)
      val trm = @{term "EX m k. (n::nat) = m * k & 1 < m"}
      val pat = @{term_pat "EX (x::nat) (y::nat). ?A x y & ?B x"}
    in
      init |> assert_match (pat, trm) [([], trm)] (err 0)
           |> to_string |> prefix "test_fo_match_quant -- " |> writeln
    end

(* Quantifiers, a corner case. *)
val test_fo_match_quant2 =
    let
      fun err n = "test_fo_match_quant2: " ^ (string_of_int n)
      val dvd = Const ("Rings.dvd_class.dvd", @{typ "nat => nat => bool"})
      val trm = Abs ("x", natT, Abs ("x", natT, dvd $ (Bound 0) $ (Bound 1)))
      val pat = @{term_pat
                      "%(x::nat). %(y::nat). (?a::(nat => nat => bool)) x y"}
      val pat2 = @{term_pat "%(x::nat). %(y::nat). (?a::(nat => bool)) x"}
    in
      init |> assert_match (pat, trm) [([], trm)] (err 0)
           |> assert_match (pat2, trm) [] (err 1)
           |> to_string |> prefix "test_fo_match_quant2 -- " |> writeln
    end

(* Multiple matches. *)
val test_fo_match_mult =
    let
      fun err n = "test_fo_match_mult: " ^ (string_of_int n)
      val tbl = init |> add_rewrite [] (@{term "(a::nat)+(b+c)"},
                                        @{term "((a::nat)+b)+c"})
                     |> add_rewrite [] (@{term "(b::nat)+c"},
                                        @{term "(c::nat)+b"})
                     |> add_rewrite [] (@{term "(a::nat)+(c+b)"},
                                        @{term "(((a::nat)+c)+b)"})
      val pat = @{term_pat "(?a::nat) + ?b"}
      val trm = @{term "(a::nat)+b+c"}
      (* a+(b+c) and a+(c+b) both acceptable. *)
      val ans = [@{term "(a::nat)+(c+b)"}, @{term "((a::nat)+b)+c"},
                 @{term "((a::nat)+c)+b"}]
    in
      tbl |> assert_match (pat, trm) (map (pair []) ans) (err 0)
          |> to_string |> prefix "test_fo_match_mult -- " |> writeln
    end

(* Quantifiers, match diff. *)
val test_fo_match_quant3 =
    let
      fun err n = "test_fo_match_quant3: " ^ (string_of_int n)
      val n = @{term "n::nat"}
      val zero = @{term "0::nat"}
      val pat = @{term_pat "EX (k::nat). k dvd (0::nat) & ?A k"}
      val trm = @{term     "EX (p::nat). p dvd (n::nat) & (prime (p::nat))"}
      val ans = @{term     "EX (p::nat). p dvd (0::nat) & (prime (p::nat))"}
    in
      init |> assert_match_diff [] (n, zero) (pat, trm) [([], ans)] (err 0)
           |> to_string |> prefix "test_fo_match_quant3 -- " |> writeln
    end

(* More match diff tests. *)
val test_fo_match_diff2 =
    let
      fun err n = "test_fo_match_diff2: " ^ (string_of_int n)
      val lhs = @{term "(b::nat)*(c+d)"}
      val rhs = @{term "(b::nat)*c+b*d"}
      val pat = @{term_pat "(?a::nat) + (?b + ?c)"}
      val trm = @{term "(a::nat) + b*(c+d)"}
      val ans = @{term "(a::nat) + (b*c+b*d)"}
    in
      init |> add_rewrite [0] (lhs, rhs)
           |> assert_match (pat, trm) [([0], ans)] (err 0)
           |> assert_match_diff [] (lhs, rhs) (pat, trm) [([], ans)] (err 1)
           |> to_string |> prefix "test_fo_match_diff2 -- " |> writeln
    end

val test_fo_match_diff3 =
    let
      fun err n = "test_fo_match_diff3: " ^ (string_of_int n)
      val a = @{term "a::nat"}
      val b = @{term "b::nat"}
      val pat = @{term_pat "(?a::nat) = ?a"}
      val trm = @{term "(a::nat) = b"}
      val ans = @{term "(a::nat) = a"}
    in
      init |> assert_match_diff [] (a, b) (pat, trm) [([], ans)] (err 0)
           |> add_rewrite [] (b, a)
           |> assert_match_diff [] (a, b) (pat, trm) [] (err 1)
           |> to_string |> prefix "test_fo_match_diff3 -- " |> writeln
    end

val test_fo_match_eq =
    let
      fun err n = "test_fo_match_eq: " ^ (string_of_int n)
      val pat = @{term_pat "?A = ?A"}
      val pat2 = @{term_pat "EX a. ?A a = ?A a"}
    in
      init |> add_rewrite [] (@{term "x::nat"}, @{term "y::nat"})
           |> (assert_match (pat, @{term "(x::nat) = y"})
                            [([], @{term "(x::nat) = x"})] (err 0))
           |> (assert_match (pat2, @{term "EX a. (x::nat) + a = y + a"})
                            [([], @{term "EX a. (x::nat) + a = x + a"})]
                            (err 1))
           |> (assert_match (pat2, @{term "EX a. (x::nat) + a = z + a"})
                            [] (err 2))
           |> to_string |> prefix "test_fo_match_eq -- " |> writeln
    end

val ring_thms = (@{thms add_ac} @ @{thms mult_ac} @ [@{thm ring_distribs(1)}])
                    |> map (pair [])

(* Find all rewrites. *)
val test_rewrite_all =
    let
      fun err n = "test_rewrite_all: " ^ (string_of_int n)
      val pat = @{term_pat "(?a::nat) + ?b + ?c + ?d"}
      val trm = @{term "(a::nat) + b + c + d"}
    in
      init |> RewriteAll.rewrite_all ring_thms trm
           |> assert_num_match (pat, trm) 24 (err 0)
           |> K "omitted" |> prefix "test_rewrite_all -- " |> writeln
    end

val add_thms
    = [([1], @{thm add_ac(1)}), ([1], obj_sym @{thm add_ac(1)}),
       ([2], @{thm add_ac(2)})]

(* Find all rewrites using different subset of rewriting rules.
   - Associativity only: a+b+c+d, a+(b+c)+d, a+b+(c+d).
   - Commutativity only: a+b+c+d, c+(a+b)+d.
   - Both: C(4,2) * 3! = 36.
 *)
val test_rewrite_all2 =
    let
      fun err n = "test_rewrite_all2: " ^ (string_of_int n)
      val pat = @{term_pat "(?a::nat) + ?b + ?c"}
      val trm = @{term "(a::nat) + b + c + d"}
    in
      init |> RewriteAll.rewrite_all add_thms trm
           |> assert_head_equivs ([1], @{term "(a::nat) + b"})
           [([1], @{term "(a::nat) + b"}), ([1, 2], @{term "(b::nat) + a"})]
           (err 0)
           |> assert_num_match_with_id [1] (pat, trm) 3 (err 1)
           |> assert_num_match_with_id [2] (pat, trm) 2 (err 2)
           |> assert_num_match_with_id [1, 2] (pat, trm) 36 (err 3)
           |> K "omitted" |> prefix "test_rewrite_all2 -- " |> writeln
    end

(* Test on matching of AC functions. *)

val test_fo_match_ac =
    let
      fun err n = "test_fo_match_ac: " ^ (string_of_int n)
      val tbl = empty ctxt'
      val trm = @{term "gcd (m::nat) n"}
      val pat = @{term_pat "gcd (?a::nat) ?b"}
      val ans = [@{term "gcd (m::nat) n"}, @{term "gcd (n::nat) m"}]
    in
      tbl |> assert_match (pat, trm) (map (pair []) ans) (err 0)
          |> to_string |> prefix "test_fo_match_ac -- " |> writeln
    end

val test_fo_match_ac2 =
    let
      fun err n = "test_fo_match_ac2: " ^ (string_of_int n)
      val tbl = empty ctxt'
      val trm = @{term "(prime (p::nat), gcd n p)"}
      val pat = @{term_pat "(prime (?a::nat), gcd ?a ?b)"}
      val ans = @{term "(prime (p::nat), gcd p n)"}
    in
      tbl |> assert_match (pat, trm) [([], ans)] (err 0)
          |> to_string |> prefix "test_fo_match_ac2 -- " |> writeln
    end

(* AC functions with more than two terms. *)
val test_fo_match_ac3 =
    let
      fun err n = "test_fo_match_ac3: " ^ (string_of_int n)
      val tbl = empty ctxt'
      val trm = @{term "(a::nat) + b + c + d + e"}
      val pat = @{term_pat "(?a::nat) + c + e + a + b"}
      val ans = @{term "(d::nat) + c + e + a + b"}
    in
      tbl |> assert_match (pat, trm) [([], ans)] (err 0)
          |> to_string |> prefix "test_fo_match_ac3 -- " |> writeln
    end

(* AC functions with more than two terms, combined with table match. *)
val test_fo_match_ac4 =
    let
      fun err n = "test_fo_match_ac4: " ^ (string_of_int n)
      val tbl = (empty ctxt')
                    |> add_rewrite [] (@{term "a::nat"}, @{term "b::nat"})
                    |> add_rewrite [] (@{term "c::nat"}, @{term "d::nat"})
      val trm = @{term "(a::nat) + d + e"}
      val pat = @{term_pat "(?a::nat) + b + c"}
      val ans = @{term "(e::nat) + b + c"}
    in
      tbl |> assert_match (pat, trm) [([], ans)] (err 0)
          |> to_string |> prefix "test_fo_match_ac4 -- " |> writeln
    end

(* Matching schematic variables to more than one term. *)
val test_fo_match_ac5 =
    let
      fun err n = "test_fo_match_ac5: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> (assert_match
                  (@{term_pat "(c::nat) + ?a"}, @{term "(c::nat) + k + l"})
                  [([], @{term_pat "(c::nat) + (k + l)"})] (err 0))
          |> (assert_match
                  (@{term_pat "?a + (n::nat)"}, @{term "k + l + (n::nat)"})
                  [([], @{term_pat "(k + l) + (n::nat)"})] (err 1))
          |> (assert_match
                  (@{term_pat "((?a::nat) + ?b, ?b)"},
                   @{term "((a::nat) + b + c + d, b + d)"})
                  [([], @{term "((a::nat) + c + (b + d), b + d)"})] (err 2))
          (* Tricky since pattern has no specified type. *)
          |> (assert_match_diff
                  [] (@{term "k::nat"}, @{term "2::nat"})
                  (@{term_pat "?a * 2"}, @{term "(k::nat) * m"})
                  [([], @{term "(m::nat) * 2"})] (err 3))
          (* As well test handling of units here. *)
          |> (assert_match_diff
                  [] (@{term "k::nat"}, @{term "1::nat"})
                  (@{term_pat "?a * 1"}, @{term "(k::nat) * m"})
                  [([], @{term "(m::nat) * 1"})] (err 4))
          |> assert_num_match (@{term_pat "~ (?A | ?B)"},
                               @{term "~ (A | B | C)"}) 6 (err 5)
          |> to_string |> prefix "test_fo_match_ac5 -- " |> writeln
    end

(* More AC tests. *)
val test_fo_match_ac6 =
    let
      fun err n = "test_fo_match_ac6: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> assert_match (@{term_pat "(?a::nat) + (?b + ?c)"},
                           @{term "(k::nat) + m + n"}) [] (err 0)
          |> add_rewrite [] (@{term "(a::nat) + b * (c + d)"},
                             @{term "(a::nat) + b * c + b * d"})
          |> (assert_match
                  (@{term_pat "((?a::nat) + ?b + ?c, ?a::nat, ?b::nat)"},
                   @{term "((a::nat) + b * (c + d), a::nat, (b::nat) * c)"})
                  [([], @{term "((a::nat) + b * c + b * d,
                                a::nat, (b::nat) * c)"})] (err 1))
          |> to_string |> prefix "test_fo_match_ac6 -- " |> writeln
    end

(* Count of matchings on five terms. *)
val test_fo_match_ac7 =
    let
      fun err n = "test_fo_match_ac7: " ^ (string_of_int n)
      val p1 = @{term_pat "(?a::nat)"}
      val p2 = @{term_pat "(?a::nat) + ?b"}
      val p3 = @{term_pat "(?a::nat) + ?b + ?c"}
      val p4 = @{term_pat "(?a::nat) + ?b + ?c + ?d"}
      val p5 = @{term_pat "(?a::nat) + ?b + ?c + ?d + ?e"}
      val trm = @{term "(a::nat) + b + c + d + e"}
      val tbl = empty ctxt'
    in
      tbl |> assert_num_match (p1, trm) 1 (err 0)
          |> assert_num_match (p2, trm) 30 (err 1)
          |> assert_num_match (p3, trm) 150 (err 2)
          |> assert_num_match (p4, trm) 240 (err 3)
          |> assert_num_match (p5, trm) 120 (err 4)
          |> to_string |> prefix "test_fo_match_ac7 -- " |> writeln
    end

val ring_thms' = [([], @{thm ring_distribs(1)})]

(* Use of distributive law and reverse associative law only. *)
val test_fo_match_ac8 =
    let
      fun err n = "test_fo_match_ac8: " ^ (string_of_int n)
      val p1 = @{term_pat "(?a::nat)"}
      val p2 = @{term_pat "(?a::nat) + ?b"}
      val p3 = @{term_pat "(?a::nat) + ?b + ?c"}
      val p4 = @{term_pat "(?a::nat) + ?b + ?c + ?d"}
      val p5 = @{term_pat "(?a::nat) + ?b + ?c + ?d + ?e"}
      val trm = @{term "(a::nat) + b + c * (d + e) + f"}
      val tbl = empty ctxt'
    in
      tbl |> RewriteAll.rewrite_all ring_thms' trm
          |> assert_equiv [] (@{term "(c::nat) * d + c * e"},
                              @{term "(c::nat) * (d + e)"}) (err 0)
          |> assert_num_match (p1, trm) 1 (err 1)
          |> assert_num_match (p2, trm) 30 (err 2)
          |> assert_num_match (p3, trm) 150 (err 3)
          |> assert_num_match (p4, trm) 240 (err 4)
          |> assert_num_match (p5, trm) 120 (err 5)
          |> to_string |> prefix "test_fo_match_ac8 -- " |> writeln
    end

val test_get_ac_head_equivs =
    let
      fun err n = "test_get_ac_head_equivs: " ^ (string_of_int n)
      val tbl = empty ctxt' |> map_lat (K lattice)
    in
      tbl |> add_rewrite [1] (@{term "x::nat"}, @{term "(p::nat) * z"})
          |> add_rewrite [2] (@{term "y::nat"}, @{term "(q::nat) * z"})
          |> assert_head_equivs ([], @{term "(x::nat) * y"})
          [([], @{term "(x::nat) * y"}), ([1], @{term "(p::nat) * y * z"}),
           ([2], @{term "(q::nat) * x * z"}),
           ([1, 2], @{term "(p::nat) * q * z * z"})] (err 0)
          |> add_rewrite [1] (@{term "u::nat"}, @{term "1::nat"})
          |> add_rewrite [2] (@{term "v::nat"}, @{term "1::nat"})
          |> (assert_head_equivs_t (@{term "a*b"}) ([], @{term "(u::nat) * v"})
                                   [([], @{term "(u::nat) * v"})] (err 1))
          |> (assert_head_equivs_t (@{term "u"}) ([], @{term "(u::nat) * v"})
                                   [([2], @{term "u::nat"})] (err 2))
          |> (assert_head_equivs_t (@{term "1"}) ([], @{term "(u::nat) * v"})
                                   [([1, 2], @{term "1::nat"})] (err 3))
          |> to_string |> prefix "test_get_ac_head_equivs -- " |> writeln
    end

(* Expanding one of the AC terms for matching. *)
val test_fo_match_ac9 =
    let
      fun err n = "test_fo_match_ac9: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> add_rewrite [] (@{term "x::nat"}, @{term "(p::nat) * z"})
          |> (assert_match (@{term_pat "(p::nat) * ?q"},
                            @{term_pat "(x::nat) * y"})
                           [([], @{term "(p::nat) * (y * z)"})] (err 0))
          |> to_string |> prefix "test_fo_match_ac9 -- " |> writeln
    end

val test_ac_equiv =
    let
      fun err n = "test_ac_equiv: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> add_rewrite [] (@{term "n::nat"}, @{term "m * k::nat"})
          |> add_rewrite [] (@{term "1::nat"}, @{term "k::nat"})
          |> add_rewrite [] (@{term "1 * m::nat"}, @{term "m::nat"})
          |> assert_equiv [] (@{term "m::nat"}, @{term "n::nat"}) (err 0)
          |> to_string |> prefix "test_ac_equiv -- " |> writeln
    end

(* Some tests about handling units. *)
val test_fo_match_ac10 =
    let
      fun err n = "test_fo_match_ac10: " ^ (string_of_int n)
      val tbl = empty ctxt' |> map_lat (K lattice)
    in
      tbl |> add_rewrite [0] (@{term "x::nat"}, @{term "1::nat"})
          |> (assert_match (@{term "y::nat"}, @{term "(x::nat) * y"})
                           [([0], @{term "y::nat"})]) (err 0)
          |> (assert_match (@{term "(x::nat) * y"}, @{term "(x::nat) * y"})
                           [([], @{term "(x::nat) * y"})]) (err 1)
          |> add_rewrite [] (@{term "x::nat"}, @{term "1::nat"})
          |> (assert_match (@{term "(x::nat) * y"}, @{term "(x::nat) * y"})
                           [([], @{term "(x::nat) * y"})]) (err 2)
          |> to_string |> prefix "test_fo_match_ac10 -- " |> writeln
    end

(* Should not go into infinite loop. *)
val test_fo_match_ac11 =
    let
      fun err n = "test_fo_match_ac11: " ^ (string_of_int n)
      val tbl = empty ctxt' |> map_lat (K lattice)
    in
      tbl |> add_rewrite [] (@{term "y::nat"}, @{term "(x::nat) * y"})
          |> (assert_match (@{term_pat "y::nat"},
                            @{term_pat "(x::nat) * y"})
                           [([], @{term "y::nat"})]) (err 0)
          |> add_rewrite [0] (@{term "x::nat"}, @{term "1::nat"})
          |> (assert_match (@{term_pat "(x::nat) * y"},
                            @{term_pat "(x::nat) * y"})
                           [([], @{term "(x::nat) * y"})]) (err 1)
          |> to_string |> prefix "test_fo_match_ac11 -- " |> writeln
    end

val test_fo_match_ac12 =
    let
      fun err n = "test_fo_match_ac12: " ^ (string_of_int n)
      val tbl = empty ctxt' |> map_lat (K lattice)
    in
      tbl |> add_rewrite [0] (@{term "y::nat"}, @{term "1::nat"})
          |> add_rewrite [1] (@{term "z::nat"}, @{term "1::nat"})
          |> add_rewrite [0] (@{term "p::nat"}, @{term "q::nat"})
          |> (assert_match (@{term "((p::nat), (x::nat) * y)"},
                            @{term "((q::nat), (x::nat) * y)"})
                           [([0], @{term "((p::nat), (x::nat) * y)"})] (err 0))
          |> (assert_match (@{term "((p::nat), (x::nat) * z)"},
                            @{term "((q::nat), (x::nat) * z)"})
                           [([0], @{term "((p::nat), (x::nat) * z)"})] (err 1))
          |> (assert_match (@{term "((p::nat), (x::nat))"},
                            @{term "((q::nat), (x::nat) * y)"})
                           [([0], @{term "((p::nat), (x::nat))"})] (err 2))
          |> (assert_match (@{term "((p::nat), (x::nat))"},
                            @{term "((q::nat), (x::nat) * z)"})
                           [([1], @{term "((p::nat), (x::nat))"})] (err 3))
          |> (assert_match (@{term "((p::nat), (x::nat) * y)"},
                            @{term "((q::nat), (x::nat))"})
                           [([0], @{term "((p::nat), (x::nat) * y)"})] (err 4))
          |> (assert_match (@{term "((p::nat), (x::nat) * z)"},
                            @{term "((q::nat), (x::nat))"})
                           [([1], @{term "((p::nat), (x::nat) * z)"})] (err 5))
          |> to_string |> prefix "test_fo_match_ac12 -- " |> writeln
    end

val test_const_simp =
    let
      fun err n = "test_const_simp: " ^ (string_of_int n)
      val tbl = empty ctxt' |> map_lat (K lattice)
      val x = @{term "x::nat"}
      val y = @{term "y::nat"}
      val one = @{term "1::nat"}
      val zero = @{term "0::nat"}
    in
      tbl |> add_rewrite [1] (x, one)
          |> add_rewrite [2] (y, one)
          |> assert_head_equivs ([], one) [([], one)] (err 0)
          |> assert_head_equivs ([], x) [([], x), ([1], one)] (err 1)
          |> add_rewrite [2] (x, zero)
          |> assert_head_equivs ([], one) [([], one), ([1, 2], zero)] (err 2)
          |> to_string |> prefix "test_const_simp -- " |> writeln
    end

val test_ac_numc =
    let
      fun err n = "test_ac_numc: " ^ (string_of_int n)
      val tbl = (empty ctxt')
                    |> add_rewrite [] (@{term "m::nat"}, @{term "3::nat"})
    in
      tbl |> (assert_match
                  (@{term_pat "(?NUMC1::nat) + ?NUMC2"},
                   @{term "(m::nat) + m"})
                  [([], @{term "(3::nat) + 3"})] (err 0))
          |> to_string |> prefix "test_ac_numc -- " |> writeln
    end

val test_match_type =
    let
      fun err n = "test_match_type: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> (assert_match (@{term_pat "image_mset ?f {#}"},
                            @{term "{#i. i :# {#}#}"})
                           [([], @{term "{#i. i :# {#}#}"})] (err 0))
          |> (assert_match (@{term_pat "sorted []"}, @{term "sorted []"})
                           [([], @{term "sorted []"})] (err 1))
          |> to_string |> prefix "test_match_type -- " |> writeln
    end

val test_fo_match_ac13 =
    let
      fun err n = "test_fo_match_ac13: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> (assert_match (@{term_pat "(?r::rat) / 2"},
                            @{term "(r::rat) * inverse 2"})
                           [([], @{term "(r::rat) / 2"})] (err 0))
          |> (assert_match (@{term_pat "(?r::rat) + ?s - ?s"},
                            @{term "(r::rat) + s + -s"})
                           [([], @{term "(r::rat) + s - s"})] (err 1))
          |> to_string |> prefix "test_fo_match_ac13 -- " |> writeln
    end

(* Difference between ?NUMC and ?NUMCu, between ?a and ?au. *)
val test_fo_match_ac14 =
    let
      fun err n = "test_fo_match_ac14: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> (assert_match (@{term_pat "(?NUMC::nat) * ?m * ?m"},
                            @{term "(m::nat) * m"}) [] (err 0))
          |> (assert_match (@{term_pat "(?NUMCu::nat) * ?m * ?m"},
                            @{term "(m::nat) * m"})
                           [([], @{term "(1::nat) * m * m"})] (err 1))
          |> (assert_match (@{term_pat "(?NUMCu::nat) * ?m * ?m"},
                            @{term "(k::nat) * m * m"}) [] (err 2))
          |> (assert_match (@{term_pat "(?NUMCu::nat) * ?m * ?m"},
                            @{term "(2::nat) * m * m"})
                           [([], @{term "(2::nat) * m * m"})] (err 3))
          |> (assert_match (@{term_pat "(?au::nat) * ?b"},
                            @{term "b::nat"})
                           [([], @{term "(1::nat) * b"})] (err 4))
          |> (assert_match (@{term_pat "(?au::nat) * ?b"},
                            @{term "(a::nat) * b"})
                           [([], @{term "(a::nat) * b"}),
                            ([], @{term "(b::nat) * a"}),
                            ([], @{term "(1::nat) * (a * b)"})] (err 5))
          |> (assert_match (@{term_pat "(?mu::int) * ?n"},
                            @{term "n::int"})
                           [([], @{term "(1::int) * n"})] (err 6))
          |> (assert_match (@{term_pat "(?mu::int) + (-?n)"},
                            @{term "-(n::int)"})
                           [([], @{term "(0::int) + (-n)"})] (err 7))
          |> (assert_match (@{term_pat "(?mu::int) + (?n * ?NUMCu)"},
                            @{term "a::int"})
                           [([], @{term "(0::int) + (a * 1)"})] (err 8))
          |> (assert_match (@{term_pat "(?mu::int) + (?n * ?NUMCu)"},
                            @{term "(a::int) * 2"})
                           [([], @{term "(0::int) + (a * 2)"}),
                            ([], @{term "(0::int) + (a * 2) * 1"})] (err 9))
          |> to_string |> prefix "test_fo_match_ac14 -- " |> writeln
    end

val test_fo_match_quant4 =
    let
      fun err n = "test_fo_match_quant4: " ^ (string_of_int n)
      val tbl = empty ctxt'
    in
      tbl |> (assert_match (@{term_pat "(EX i. ?f i < 0, ?f ?n)"},
                            @{term "(EX i. i + a < 0, n + a)"})
                           [([], @{term "(EX i. i + a < 0, n + a)"})] (err 0))
          |> to_string |> prefix "test_fo_match_quant4 -- " |> writeln
    end

end;  (* local *)
