(* Testing of rings.ML. *)

local
  val ctxt = @{context}
  val thy = @{theory}
  open Ring_Arith
in

val test_distrib =
    let
      val test = test_conv ctxt (distrib_conv thy) "test_distrib"
      val test_terms = test_conv ctxt (distrib_terms_conv thy)
                                 "test_distrib_terms"
      val _ = test ("(a::nat) * b", "(a::nat) * b")
      val _ = test ("(a::nat) * (b + c)", "(a::nat) * b + a * c")
      val _ = test ("((a::nat) + b) * (c + d)",
                    "(a::nat) * c + a * d + b * c + b * d")

      val _ = test ("(a::int) * b", "(a::int) * b")
      val _ = test ("((a::int) + -b) * (c + -d)",
                    "(a::int) * c + -(a * d) + -(b * c) + b * d")

      val _ = test_terms ("(a::int) * (b + c) + b * (c + -a)",
                          "(a::int) * b + a * c + b * c + -(b * a)")
      val _ = test_terms ("(a::int) + -((b + c) * d)",
                          "(a::int) + -(b * d) + -(c * d)")
      val _ = test_terms ("(a::int) + -((b + -c) * d)",
                          "(a::int) + -(b * d) + c * d")
    in
      ()
    end

end
