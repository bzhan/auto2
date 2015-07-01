(* Unit test for logic_steps.ML. *)

val ctxt = @{context}

val test_imp_to_disj_cv =
    let
      fun err n = "test_imp_to_disj_cv: " ^ (string_of_int n)
      fun test_prop ct res txt =
          let val res' = Thm.rhs_of (Logic_ProofSteps.imp_to_disj_cv ctxt ct)
          in if res aconvc res' then ()
             else let val _ = trace_t_ctxt ctxt "got " (Thm.term_of res')
                  in raise AUTO2 txt end
          end

      val _ = test_prop
              @{cprop "A --> B --> ~C & D --> (E | F)"}
              @{cprop "~A | ~B | C | ~D | E | F"} (err 0)
      val _ = test_prop @{cprop "~(A & B & ~C)"} @{cprop "~A | ~B | C"} (err 1)
      val _ = test_prop
              @{cprop "A --> (!x. B x --> C x)"}
              @{cprop "~A | (!x. B x --> C x)"} (err 2)
    in
      ()
    end

val test_disj_mut =
    let
      fun err n = "test_disj_mut: " ^ (string_of_int n)
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

      val updt_fn = get_mut_update @{theory} Logic_ProofSteps.DISJ_MUT
      fun to_box_item (id, th) = mk_box_item (id, 0, Fact th)
      fun test_updt tval t rtype res_ts txt =
          let
            val sval = assume_thm ctxt tval
            val th = assume_thm ctxt t
            val res = updt_fn ([], sval) rtype (to_box_item ([], th)) st
            val res_ts' = res |> map snd |> map Thm.prop_of
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

      val concl_fn = get_mut_concl @{theory} Logic_ProofSteps.DISJ_MUT_ACTIVE
      val updt1 = concl_fn ([], assume_thm ctxt @{prop "False"}) st
      val _ = assert (length updt1 = 1) (err 6)
      val _ = case the_single updt1 of Update.ResolveBox _ => ()
                                     | _ => raise AUTO2 (err 7)
    in
      ()
    end
