(* Unit test for normalizer.ML. *)

val test_normalize =
    let
      val thy = @{theory} |> add_logic_ac_data
      val ctxt = Proof_Context.init_global thy
      fun test (str, strs) =
          let
            val t = read_term ctxt str
            val ts = map (read_term ctxt) strs
            val ritem =
                Update.thm_to_ritem (assume_thm ctxt (HOLogic.mk_Trueprop t))
            val ritems' = normalize ctxt ritem
            val ts' = map (HOLogic.dest_Trueprop o Thm.prop_of o get_thm_raw)
                          ritems'
          in
            if length ts = length ts' andalso
               eq_set (op aconv) (ts, ts') then ()
            else let
              val _ = trace_t_ctxt ctxt "Input:" t
              val _ = trace_tlist_ctxt ctxt "Expected:" ts
              val _ = trace_tlist_ctxt ctxt "Actual:" ts'
            in
              raise AUTO2 "test_normalize"
            end
          end

      val test_data = [
        ("A | C | D | B", ["A | B | C | D"]),
        ("P a = True", ["(P a)::bool"]),
        ("P a = False", ["~ (P a)"]),
        ("A & B & C", ["A::bool", "B::bool", "C::bool"]),
        ("~ (A | B | C)", ["~ A", "~ B", "~ C"]),
        ("~ ~ (~ A & (~ ~ B))", ["~ A", "B::bool"])
      ]
    in
      map test test_data
    end
