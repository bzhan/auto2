(* Unit test for logic_steps.ML. *)

local

  open Logic_ProofSteps
  val ctxt = @{context}

in

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
                val _ = trace_tlist_ctxt ctxt "input, expected, actual "
                                         [t, res, prop_of' th']
              in () end
            else ()
          end

      val test_data = [
        ("A --> B --> ~C & D --> (E | F)", (false, "~A | ~B | C | ~D | E | F")),
        ("~ (A & B & ~C)", (true, "~A | ~B | C")),
        ("A --> (!(x::nat). B x --> C x)",
         (false, "~A | (!(x::nat). B x --> C x)")),
        ("!(x::nat). A x --> B x", (false, "~A (?x::nat) | B ?x")),
        ("!(x::nat) (y::nat). A x y --> B y x",
         (false, "~A (?x::nat) (?y::nat) | B ?y ?x")),
        ("!(x::nat). A x (y::nat) --> B y x",
         (false, "~A (?x::nat) (y::nat) | B y ?x"))]
    in
      map test test_data
    end

val test_disj =
    let
      fun err n = "test_disj: " ^ (string_of_int n)
      val ctxt = @{context}
      val tval = @{prop "~A | B (x::nat) | B (y::nat)"}
      val tval2 = @{prop "B (x::nat) | B (y::nat)"}
      val t1 = @{prop "A"}
      val t2 = @{prop "~(B (x::nat))"}
      val t3 = @{prop "~(B (y::nat))"}
      val t4 = @{prop "D"}

      val tbl = RewriteTable.empty ctxt
      val rtype = RewriteTable.SINGLE tbl
      val tbl2 = tbl |> RewriteTable.add_rewrite []
                     (@{term "x::nat"}, @{term "y::nat"})
      val rtype2 = RewriteTable.SINGLE tbl2
      val st = Status.empty_status ctxt

      val {func, ...} = disj_update_gen (
            eq_update, "disj_update", K true, ItemIO_Data.univ_filt) |> hd

      fun test_updt tval t rtype res_ts txt =
          let
            val sval = assume_thm ctxt tval
            val th = assume_thm ctxt t
            val items =
                [mk_box_item ([], 0, Fact (TY_DISJ, [prop_of' sval], sval)),
                 mk_box_item ([], 0, thm_to_ritem_ctxt ctxt th)]
            val updts = func items rtype st
            fun updt_to_thm updt =
                case updt of Update.AddItems {raw_items, ...} =>
                             map get_thm_raw raw_items
                           | Update.ResolveBox {th, ...} => [th]
                           | _ => []
            val res_ts' = maps updt_to_thm updts |> map Thm.prop_of
          in
            if eq_set (op aconv) (res_ts, res_ts') then ()
            else raise AUTO2CT (txt, map (cert ctxt) res_ts')
          end

      val _ = test_updt tval t1 rtype [@{prop "B(x::nat) | B(y::nat)"}] (err 0)
      val _ = test_updt tval t2 rtype [@{prop "B(y::nat) | ~A"}] (err 1)
      val _ = test_updt tval t3 rtype [@{prop "B(x::nat) | ~A"}] (err 2)
      val _ = test_updt tval t2 rtype2 [@{prop "~A"}] (err 3)
      val _ = test_updt tval t4 rtype2 [] (err 4)
      val _ = test_updt tval2 t2 rtype2 [@{prop "False"}] (err 5)
    in
      ()
    end

end
