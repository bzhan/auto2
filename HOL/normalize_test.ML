(* Unit test for normalizer.ML. *)

val test_normalize =
    let
      val ctxt = @{context}
      fun test (str, strs) =
          let
            val t = Syntax.read_term ctxt str
            val ts = map (Syntax.read_term ctxt) strs
            val ritem =
                Update.thm_to_ritem (assume_thm ctxt (mk_Trueprop t))
            val ritems' = Normalizer.normalize ctxt ritem
            val ts' = map (dest_Trueprop o Thm.prop_of o BoxItem.get_thm_raw)
                          ritems'
          in
            if length ts = length ts' andalso
               eq_set (op aconv) (ts, ts') then ()
            else let
              val _ = trace_t_ctxt ctxt "Input:" t
              val _ = trace_tlist_ctxt ctxt "Expected:" ts
              val _ = trace_tlist_ctxt ctxt "Actual:" ts'
            in
              raise Fail "test_normalize"
            end
          end

      val test_data = [
        ("A & B & C", ["A::bool", "B::bool", "C::bool"]),
        ("~ (A | B | C)", ["~ A", "~ B", "~ C"]),
        ("~ ~ (~ A & (~ ~ B))", ["~ A", "B::bool"])
      ]
    in
      map test test_data
    end
