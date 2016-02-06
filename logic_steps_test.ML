(* Unit test for logic_steps.ML. *)

local

  open Logic_ProofSteps
  val ctxt = @{context}

in

val test_normalize_pred_comm =
    let
      val test = test_conv ctxt normalize_pred_comm_conv
                           "test_normalize_pred_comm"

      val _ = test ("EX i j. ka = p ^ i & y = p ^ j",
                    "EX i j. ka = p ^ i & y = p ^ j")
      val _ = test ("EX i j. ka = p ^ j & y = p ^ i",
                    "EX j i. ka = p ^ j & y = p ^ i")
      val _ = test ("ka = p ^ j & y = p ^ i",
                    "ka = p ^ j & y = p ^ i")
    in () end

val test_swap_quantifiers =
    let
      fun test1 counts = test_conv ctxt (swap_foralls_imps_conv counts ctxt)
                                   "test_swap_forall_imp"
      fun test2 counts = test_conv ctxt (swap_exs_conjs_conv counts ctxt)
                                   "test_swap_ex_conj"

      (* Swapping ALL and --> *)
      val _ = test1 [1] ("!n. P --> Q n", "P --> (!n. Q n)")
      val _ = test1 [2] ("!n. P --> Q --> R n", "P --> Q --> (!n. R n)")
      val _ = test1 [0, 1] ("!m n. P m --> Q m n", "!m. P m --> (!n. Q m n)")
      val _ = test1 [0, 2] ("!m n. P m --> Q m --> R m n",
                            "!m. P m --> Q m --> (!n. R m n)")
      val _ = test1 [1, 1] ("!m n. P --> Q m --> R m n",
                            "P --> (!m. Q m --> (!n. R m n))")
      val _ = test1 [1, 0] ("!m n. P --> Q m --> R m n",
                            "P --> (!m n. Q m --> R m n)")

      (* Swapping EX and & *)
      val _ = test2 [1] ("EX n. P & Q n", "P & (EX n. Q n)")
      val _ = test2 [0, 1] ("EX m n. P m & Q m n", "EX m. P m & (EX n. Q m n)")

    in () end

val test_not_ex_forall =
    let
      val test = test_conv ctxt (not_ex_forall_cv ctxt) "test_not_ex_forall"

      (* Simple EX and ALL *)
      val _ = test ("~(EX x y. P x y)", "!x y. ~ P x y")
      val _ = test ("~(!x y. P x y)", "EX x y. ~ P x y")
      val _ = test ("~(EX x. !y. EX z. P x y z)",
                    "!x. EX y. !z. ~ P x y z")
      val _ = test ("~(EX x y. ~ P x y)", "!x y. P x y")
      val _ = test ("~(EX x. ~ (EX y. P x y))", "!x. EX y. P x y")

      (* EX with &, and ALL with -->, but not inequalities. *)
      val _ = test ("~(EX x. P x & Q x)", "!x. ~(P x & Q x)")
      val _ = test ("~(!x. P x --> Q x)", "EX x. ~(P x --> Q x)")

      (* EX with &, and ALL with -->, with inequalities. *)
      val _ = test ("~(EX x>k. P x)", "ALL x>k. ~ P x")
      val _ = test ("~(ALL x>k. P x)", "EX x>k. ~ P x")
      val _ = test ("~(EX x>k. EX y>k. P x y)", "ALL x>k. ALL y>k. ~ P x y")
      val _ = test ("~(ALL x>k. ALL y>k. P x y)", "EX x>k. EX y>k. ~ P x y")
      val _ = test ("~(EX x>k. x<(a::nat))", "ALL x>k. x>=(a::nat)")
      val _ = test ("~(ALL x>k. x<(a::nat))", "EX x>k. x>=(a::nat)")
    in () end

val test_analyze_disj_th =
    let
      fun test (t_str, (is_active, res_str)) =
          let
            val t = Syntax.read_term ctxt t_str
            val res = Proof_Context.read_term_pattern ctxt res_str
            val th = assume_thm ctxt (HOLogic.mk_Trueprop t)
            val (is_active', th') = analyze_disj_th ctxt th
          in
            if is_active <> is_active' then
              let
                val _ = trace_t_ctxt ctxt "Wrong is_active output. Input: " t
              in () end
            else if not (res aconv (prop_of' th')) then
              let
                val _ = trace_t_ctxt ctxt "Input:" t
                val _ = trace_t_ctxt ctxt "Expected:" res
                val _ = trace_t_ctxt ctxt "Actual:" (prop_of' th')
              in
                raise AUTO2 "test_analyze_disj_th"
              end
            else ()
          end

      val test_data = [
        ("A --> B --> ~C & D --> (E | F)", (false, "C | E | F | ~A | ~B | ~D")),
        ("~ (A & B & ~C)", (true, "C | ~A | ~B")),
        ("A --> (!(x::nat). B x --> C x)",
         (false, "~A | (!(x::nat). B x --> C x)")),
        ("!(x::nat). A x --> B x", (false, "B (?x::nat) | ~ A ?x")),
        ("!(x::nat) (y::nat). A x y --> B y x",
         (false, "B (?y::nat) (?x::nat) | ~A ?x ?y")),
        ("!(x::nat). A x (y::nat) --> B y x",
         (false, "B (y::nat) (?x::nat) | ~A ?x y")),
        ("A --> False", (false, "~A")),
        ("A --> B --> False", (false, "~A | ~B"))]
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
                     (@{term "x::nat"}, @{term "y::nat"})
      val rtype2 = RewriteTable.SINGLE tbl2
      val st = Status.empty_status ctxt'

      fun disj_to_ritem th =
          let
            val subs = ACUtil.dest_ac disj_ac (prop_of' th)
            val tname = HOLogic.mk_tuple subs
          in
            Fact (TY_DISJ, tname, th)
          end

      fun read_prop str = str |> Proof_Context.read_term_pattern ctxt'
                              |> HOLogic.mk_Trueprop

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
