(* Testing of rings.ML. *)

local
  val ctxt = @{context}
  val thy = @{theory}
  open Ring_Arith
in

val test_distrib =
    let
      val test = test_conv ctxt (distrib_conv thy) "test_distrib"
      val test_data = [
        ("(a::nat) * b", "(a::nat) * b"),
        ("(a::nat) * (b + c)", "(a::nat) * b + a * c"),
        ("((a::nat) + b) * (c + d)", "(a::nat) * c + a * d + b * c + b * d"),
        ("(a::int) * b", "(a::int) * b"),
        ("((a::int) - b) * (c - d)",
         "(a::int) * c + -(a * d) + -(b * c) + b * d"),
        ("((a::int) + 1) * b", "(a::int) * b + b"),
        ("((a::int) - 1) * (b - c)", "(a::int) * b + -(a * c) + -b + c")
      ]
    in
      map test test_data
    end

end
