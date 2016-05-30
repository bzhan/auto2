(* Unit test for logic_steps.ML. *)

local

  open Logic_ProofSteps
  val ctxt = @{context}
  val thy = @{theory}

in

val test_not_ex_forall =
    let
      val ctxt' = ctxt |> Variable.auto_fixes (Free ("n", natT))
      val test = test_conv ctxt' (not_ex_forall_cv ctxt') "test_not_ex_forall"

      val test_data = [
        (* Simple EX and ALL *)
        ("~(EX x y. P x y)", "ALL x y. ~ P x y"),
        ("~(ALL x y. P x y)", "EX x y. ~ P x y"),
        ("~(EX x. ALL y. EX z. P x y z)", "ALL x. EX y. ALL z. ~ P x y z"),
        ("~(EX x y. ~ P x y)", "ALL x y. P x y"),
        ("~(EX x. ~ (EX y. P x y))", "ALL x. EX y. P x y"),

        (* EX with &, and ALL with -->, but not inequalities. *)
        ("~(EX x. P x & Q x)", "ALL x. ~(P x & Q x)"),
        ("~(ALL x. P x --> Q x)", "EX x. ~(P x --> Q x)"),

        (* EX with &, and ALL with -->, with inequalities. *)
        ("~(EX x>k. P x)", "ALL x>k. ~ P x"),
        ("~(ALL x>k. P x)", "EX x>k. ~ P x"),
        ("~(EX x>k. EX y>k. P x y)", "ALL x>k. ALL y>k. ~ P x y"),
        ("~(ALL x>k. ALL y>k. P x y)", "EX x>k. EX y>k. ~ P x y"),
        ("~(EX x>k. x < n)", "ALL x>k. x >= n"),
        ("~(ALL x>k. x < n)", "EX x>k. x >= n")
      ]
    in
      map test test_data
    end

val test_analyze_disj_th =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term_pat "[A::bool, B, C]"},
            @{term_pat "[x::nat, y, ?x, ?y]"},
            @{term_pat "[P::(nat => bool), Q]"},
            @{term_pat "[R::(nat => nat => bool)]"},
            @{term_pat "[S::(nat set), T]"}]

      fun test is_active (t_str, sz, res_str) =
          let
            val (t, res) = (read_term ctxt' t_str, read_pat ctxt' res_str)
            val th = assume_thm ctxt' (HOLogic.mk_Trueprop t)
            val (is_active', sz', th') = analyze_disj_th ctxt' th
          in
            if is_active <> is_active' orelse sz <> sz' then
              let
                val _ = trace_t_ctxt
                            ctxt' "Wrong is_active or sz output. Input: " t
                val _ = tracing ("Got is_active = " ^
                                 (string_of_bool is_active'))
                val _ = tracing ("Got sz = " ^ (string_of_int sz'))
              in
                raise AUTO2 "test_analyze_disj_th"
              end
            else if not (res aconv (prop_of' th')) then
              let
                val _ = trace_t_ctxt ctxt' "Input:" t
                val _ = trace_t_ctxt ctxt' "Expected:" res
                val _ = trace_t_ctxt ctxt' "Actual:" (prop_of' th')
              in
                raise AUTO2 "test_analyze_disj_th"
              end
            else ()
          end

      val test_data_active = [
        ("~ (A & B & ~C)", 3, "~A | ~B | C"),
        ("~(EX x. P x & Q x)", 2, "~P ?x | ~Q ?x"),
        ("~(EX x. P x & (EX y. R x y))", 2, "~P ?x | ~R ?x ?y")
      ]

      val test_data_non_active = [
        ("ALL x. P x --> Q x", 2, "~ P ?x | Q ?x"),
        ("ALL x y. R x y --> R y x", 2, "~R ?x ?y | R ?y ?x"),
        ("ALL x. R x y --> R y x", 2, "~R ?x y | R y ?x"),
        ("ALL x. P x --> (ALL y. Q y --> R x y)", 3,
         "~ P ?x | ~ Q ?y | R ?x ?y"),
        ("A --> (ALL x. P x --> Q x)", 2, "~A | (ALL x. P x --> Q x)"),
        ("ALL x:S. P x", 2, "~ ?x : S | P ?x"),
        ("ALL x:S. ALL y:T. R x y", 3, "~ ?x : S | ~ ?y : T | R ?x ?y"),
        ("A --> B | C", 2, "~A | B | C"),
        ("A --> ~(B & C)", 2, "~A | ~(B & C)"),
        ("ALL x. A", 1, "A"),
        ("ALL x. A --> P x", 2, "~A | P ?x")
      ]
    in
      map (test true) test_data_active @
      map (test false) test_data_non_active
    end

val test_normalize_disj_cv =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            @{term_pat "[A::bool, B, C]"},
            @{term_pat "[x::nat, y, ?x, ?y]"},
            @{term_pat "[P::(nat => bool), Q]"},
            @{term_pat "[R::(nat => nat => bool)]"},
            @{term_pat "[S::(nat set), T]"}]

      val test =
          test_conv ctxt' (normalize_disj_cv ctxt') "test_normalize_disj_cv"

      val test_data = [
        ("ALL x. P x --> Q x", "ALL x. ~P x | Q x"),
        ("EX x. P x & Q x", "EX x. P x & Q x"),
        ("~(EX x. P x)", "ALL x. ~P x"),
        ("~(EX x. P x & Q x)", "ALL x. ~P x | ~Q x"),
        ("~(EX x. P x & (EX y. R x y))", "ALL x y. ~P x | ~R x y"),
        ("ALL x:S. P x", "ALL x. ~(x : S) | P x"),
        ("ALL x:S. ALL y:T. R x y", "ALL x y. ~(x : S) | ~(y : T) | R x y"),
        ("~(EX x:S. EX y:T. R x y)", "ALL x y. ~(x : S) | ~(y : T) | ~R x y"),

        (* Also works with schematic variables inside. *)
        ("ALL x. ?P x --> ?Q x", "ALL x. ~?P x | ?Q x"),
        ("~(EX x. ?P x & Q x)", "ALL x. ~?P x | ~Q x")
      ]
    in
      map test test_data
    end

val test_match_update =
    let
      val x = Free ("x", natT)
      val y = Free ("y", natT)
      val A = Free ("A", boolT)
      val B = Free ("B", natT --> boolT)
      val D = Free ("D", boolT)
      val ctxt' = ctxt |> fold Variable.declare_term [x, y, A, B, D]

      val tbl = RewriteTable.empty ctxt'
      val rtype = RewriteTable.SINGLE tbl
      val tbl2 = tbl |> RewriteTable.add_rewrite []
                     (assume_eq thy (@{term "x::nat"}, @{term "y::nat"}))
      val rtype2 = RewriteTable.SINGLE tbl2
      val st = Status.empty_status ctxt'

      fun disj_to_ritem th =
          let
            val subs = ACUtil.dest_ac_r disj_ac (prop_of' th)
            val tname =
                HOLogic.mk_tuple (@{term False} :: @{term False} :: subs)
          in
            Fact (TY_DISJ, tname, th)
          end

      fun read_prop str = str |> read_pat ctxt' |> HOLogic.mk_Trueprop

      fun updt_to_thm updt =
          case updt of
              Update.AddItems {raw_items, ...} => map get_thm_raw raw_items
            | Update.ResolveBox {th, ...} => [th]
            | _ => []

      fun test_updt rtype (disj_str, t_str, res_strs) =
          let
            val disj_th = assume_thm ctxt' (read_prop disj_str)
            val th = assume_thm ctxt' (read_prop t_str)
            val res_ts = map read_prop res_strs
            val items = [mk_box_item ([], 0, disj_to_ritem disj_th),
                         mk_box_item ([], 0, Update.thm_to_ritem th)]
            val updts = apply_prfstep rtype st items (hd match_update_prfsteps)
            val res_ts' = maps updt_to_thm updts |> map Thm.prop_of
          in
            if eq_set (op aconv) (res_ts, res_ts') then ()
            else let
              val _ = trace_t_ctxt ctxt' "Input disj:" (prop_of' disj_th)
              val _ = trace_t_ctxt ctxt' "Input t:" (prop_of' th)
              val _ = trace_tlist_ctxt ctxt' "Expected:" res_ts
              val _ = trace_tlist_ctxt ctxt' "Actual:" res_ts'
            in
              raise AUTO2 "test_match_update"
            end
          end

      val data1 = [("B x | B y | ~A", "A", ["B x | B y"]),
                   ("B x | B y | ~A", "~B x", ["B y | ~A"]),
                   ("B x | B y | ~A", "~B y", ["B x | ~A"])]
      val _ = map (test_updt rtype) data1

      val data2 = [("B x | B y | ~A", "~B x", ["B x | ~A", "B y | ~A"]),
                   ("B x | B y | ~A", "D", []),
                   ("B x | B y", "~B x", ["B x", "B y"])]
      val _ = map (test_updt rtype2) data2
    in
      ()
    end

end
