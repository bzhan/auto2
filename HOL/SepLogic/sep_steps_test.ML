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
      val test = Util.test_conv ctxt' (AssnNorm.normalize_assn_cv ctxt')
                                "normalize_assn"

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
        ("EXA x. S x * \<up>(B x) * T x", "EXA x. S x * T x * \<up>(B x)"),
        ("P * true * true", "P * true"),
        ("true * P * true", "P * true"),
        ("true * P * true * \<up>(b)", "P * true * \<up>(b)")
      ]
    in
      map test test_data
    end

val test_normalize_mod =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            Free ("P", assnT), Free ("S", natT --> assnT),
            Free ("T", natT --> assnT)]
      val test = Util.test_conv ctxt' (SepLogic.normalize_mod_cv ctxt')
                                "normalize_mod"

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

val test_normalize_hoare =
    let
      val ctxt' = ctxt |> fold Variable.auto_fixes [
            Free ("P", assnT), Free ("S", natT --> assnT),
            Free ("T", natT --> assnT)]
      val test = Util.test_conv ctxt' (SepLogic.normalize_hoare_cv ctxt')
                                "normalize_hoare"

      val test_data = [
        ("<P * \<up>(b)> c <Q>", "<P * \<up>(b)> c <Q>"),
        ("b --> <P> c <Q>", "<P * \<up>(b)> c <Q>"),
        ("b1 --> b2 --> <P> c <Q>", "<P * \<up>(b2) * \<up>(b1)> c <Q>"),
        ("b1 --> <P * \<up>(b2)> c <Q>", "<P * \<up>(b2) * \<up>(b1)> c <Q>")
      ]
    in
      map test test_data
    end

end
