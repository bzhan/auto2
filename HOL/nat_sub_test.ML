(* Unit test for nat_sub *)

local

  val ts = map (fn x => Free (x, natT)) ["a", "b", "c", "m", "n"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

fun test_norm_t err_str (str1, str2) =
    let
      val (t1, t2) = apply2 (Syntax.read_term ctxt) (str1, str2)
      val (ct1, ct2) = apply2 (Thm.cterm_of ctxt) (t1, t2)
      val (p1, m1, n1) = NatSub.norm_minus_ct ct1
      val (p2, m2, n2) = NatSub.norm_minus_ct ct2
    in
      if eq_list (op aconvc) (p1, p2) andalso
         eq_list (op aconvc) (m1, m2) andalso n1 = n2 then ()
      else let
        val _ = trace_tlist ctxt "Inputs" [t1, t2]
        val _ = trace_tlist ctxt "p1" (map Thm.term_of p1)
        val _ = trace_tlist ctxt "m1" (map Thm.term_of m1)
        val _ = trace_tlist ctxt "p2" (map Thm.term_of p2)
        val _ = trace_tlist ctxt "m2" (map Thm.term_of m2)
        val _ = tracing ("n1 " ^ string_of_int n1)
        val _ = tracing ("n2 " ^ string_of_int n2)
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        (* No repeated terms. *)
        ("a", "a"),
        ("a + b", "a + b"),
        ("a - b", "a - b"),
        ("a - b + c", "a + c - b"),
        ("a - b - c", "a - (b + c)"),
        ("a - b + (c - d)", "a + c - (b + d)"),
        ("a - b - (c - d)", "a + d - (b + c)"),
        ("a + b + c - d - e - f", "a + b + c - (d + e + f)"),
        ("a - b + c - d + e - f", "a + c + e - (b + d + f)"),

        (* Numerical constants (on one side only). *)
        ("0::nat", "0::nat"),
        ("2::nat", "2::nat"),
        ("a + 2 + 3", "a + 5"),
        ("a - b - 2 - 3", "a - (b + 5)"),
        ("2 + 3 + a", "a + 5"),
        ("a - 2 - b - 3", "a - (b + 5)"),
        ("0 + a - 0 - b", "a - b"),

        (* Cancellation needed. *)
        ("a - a", "(0::nat)"),
        ("a + b - a", "b"),
        ("a + b - a - c", "b - c"),
        ("a + b - a - b", "0::nat"),
        ("a + b + c - a - b", "c"),
        ("c + (b + (b + a - b) - b)", "a + c"),

        (* Cancellation of constants needed. *)
        ("a + 5 - b - 3", "a + 2 - b"),
        ("a + 3 - b - 5", "a - (b + 2)"),
        ("a + 5 - b - 5", "a - b"),
        ("a - 5 - (b - 3)", "a - (b + 2)"),
        ("a - 3 - (b - 5)", "(a + 2) - b"),
        ("a + 5 - 3", "a + 2"),
        ("5 - a - 3", "2 - a"),
        ("3 - a - 3", "0 - a"),
        ("(5::nat) - 3", "2::nat"),
        ("(3::nat) - 3", "0::nat")
      ]
    in
      map (WfTerm.test_wfconv ctxt NatSub.fheads NatSub.norm_minus "test") test_data @
      map (test_norm_t "test_norm") test_data
    end

end
