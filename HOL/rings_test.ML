(* Unit test for rings *)

local

  val ts = map (fn x => Free (x, natT)) ["a", "b", "c", "m", "n"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

fun test_term ctxt f err_str (str1, str2) =
    let
      val (t1, t2) = (Proof_Context.read_term_pattern ctxt str1,
                      Proof_Context.read_term_pattern ctxt str2)
      val t2' = f t1
    in
      if t2 aconv t2' then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" t2'
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        ("a + 1 + 2", "a + 3"),
        ("1 + c + 2 + b + a + 3", "a + b + c + 6"),
        ("a * 2 * 3", "a * 6"),
        ("(2::nat) * 3", "6::nat"),
        ("(2::nat) * 3 * 5", "30::nat"),
        ("2 * a * 3 * b * 5 * c", "a * b * c * 30"),
        ("a * 2 + a * 3", "a * 5"),
        ("a + a", "a * 2"),
        ("a + 2 * a", "a * 3"),
        ("a + b + a + c + c", "a * 2 + b + c * 2"),
        ("Suc a", "a + 1"),
        ("Suc (a + b + 1)", "a + b + 2"),
        ("Suc (Suc a + Suc b)", "a + b + 3")
      ]
    in
      map (Util.test_conv ctxt NatRing.norm_full "norm_full") test_data @
      map (test_term ctxt NatRing.norm_ring_term "norm_ring_term") test_data
    end

end
