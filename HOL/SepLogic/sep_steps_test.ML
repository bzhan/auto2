(* Unit test for sep_steps.ML. *)

local
  open SepUtil
  val ctxt = @{context}
in

val test_normalize_assn =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            Free ("P", assnT), Free ("S", natT --> assnT),
            Free ("T", natT --> assnT)]
      val test = test_conv ctxt' (normalize_assn_cv ctxt') "normalize_assn"

      val test_data = [
        ("P * (Q * R)", "P * Q * R"),
        ("P * \<up>(b)", "P * \<up>(b)"),
        ("\<up>(b) * P", "P * \<up>(b)"),
        ("P * \<up>(b) * Q", "P * Q * \<up>(b)"),
        ("\<up>(b) * (P * \<up>(c)) * Q", "P * Q * \<up>(b) * \<up>(c)"),
        ("EXA x. S x", "EXA x. S x"),
        ("(EXA x. S x) * P", "EXA x. S x * P"),
        ("P * (EXA x. S x)", "EXA x. P * S x"),
        ("(EXA x. S x) * (EXA y. T y)", "EXA x y. S x * T y"),
        ("EXA x. S x * \<up>(B x) * T x", "EXA x. S x * T x * \<up>(B x)")
      ]
    in
      map test test_data
    end

val test_normalize_mod =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            Free ("P", assnT), Free ("S", natT --> assnT),
            Free ("T", natT --> assnT)]
      val test = test_conv ctxt' (normalize_mod_cv ctxt') "normalize_mod"

      val test_data = [
        ("h |= (P * \<up>(b))", "(h |= P) & b"),
        ("h |= (\<up>(b) * P)", "(h |= P) & b"),
        ("h |= (EXA x. S x)", "EX x. h |= S x"),
        ("h |= ((EXA x. S x) * (EXA y. T y))", "EX x y. h |= S x * T y"),
        ("h |= \<up>(b)", "(h |= emp) & b"),
        ("h |= (EXA x. S x * \<up>(b x))", "EX x. h |= S x & b x")
      ]
    in
      map test test_data
    end

val test_use_prec_thms =
    let
      val ctxt' =
          ctxt |> fold Variable.auto_fixes [
            Free ("h", pheapT), Free ("p", @{typ "nat ref"}),
            Free ("x", @{typ "nat"}), Free ("y", @{typ "nat"})]
      val tbl = RewriteTable.empty ctxt'

      fun test (base_str, ex_str) =
          let
            val (t1, t2) = (Syntax.read_term ctxt' base_str,
                            Syntax.read_term ctxt' ex_str)
            val (th1, th2) =
                apply2 (Thm.assume o Thm.cterm_of ctxt' o mk_Trueprop) (t1, t2)
            (* Just run it to see that all asserts passed. *)
            val _ = SepLogic.use_prec_thms tbl th1 th2
          in
            ()
          end

      val test_data = [
        ("h |= sngr_assn p x", "EX x. h |= sngr_assn p x * \<up>(x = 3)"),
        ("h |= sngr_assn p x", "EX l. h |= \<up>(x = 3) * sngr_assn p x"),
        ("h |= sngr_assn p x * sngr_assn q y",
         "EX x y. h |= sngr_assn p x * sngr_assn q y * \<up>(x = y + y)")
      ]
    in
      map test test_data
    end

end
