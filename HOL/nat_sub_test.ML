(* Unit test for nat_sub *)

local

  val ts = map (fn x => Free (x, natT)) ["a", "b", "c", "m", "n"]
  val ctxt = fold Util.declare_free_term ts @{context}

in

val fheads = NatSub.fheads
val wfterm_of = WfTerm.cterm_to_wfterm_assume fheads o Thm.cterm_of ctxt

(* Apply wfcv on the term given by str_t, and compare the result to
   the term given by str_res.
 *)
fun test_wfconv wfcv err_str (str1, str2) =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val wft = wfterm_of t1
      val th = snd (wfcv wft)
               handle Fail err =>
                      let val _ = trace_t ctxt "Input:" t1 in
                        raise Fail (err ^ " -- " ^ err_str)
                      end
    in
      if t1 aconv (Util.lhs_of th) andalso t2 aconv (Util.rhs_of th) then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" (Thm.prop_of th)
      in
        raise Fail err_str
      end
    end

val test =
    let
      val test_data = [
        (* No repeated terms. *)
        ("a", "a - 0"),
        ("a + b", "a + b - 0"),
        ("a - b", "a - b"),
        ("a - b + c", "a + c - b"),
        ("a - b - c", "a - (b + c)"),
        ("a - b + (c - d)", "a + c - (b + d)"),
        ("a - b - (c - d)", "a + d - (b + c)"),
        ("a + b + c - d - e - f", "a + b + c - (d + e + f)"),
        ("a - b + c - d + e - f", "a + c + e - (b + d + f)"),

        (* Numerical constants (on one side only). *)
        ("0::nat", "(0::nat) - 0"),
        ("2::nat", "(2::nat) - 0"),
        ("a + 2 + 3", "a + 5 - 0"),
        ("a - b - 2 - 3", "a - (b + 5)"),
        ("2 + 3 + a", "a + 5 - 0"),
        ("a - 2 - b - 3", "a - (b + 5)"),
        ("0 + a - 0 - b", "a - b"),

        (* Cancellation needed. *)
        ("a - a", "(0::nat) - 0"),
        ("a + b - a", "b - 0"),
        ("a + b - a - c", "b - c"),
        ("a + b - a - b", "(0::nat) - 0"),
        ("a + b + c - a - b", "c - 0"),

        (* Cancellation of constants needed. *)
        ("a + 5 - b - 3", "a + 2 - b"),
        ("a + 3 - b - 5", "a - (b + 2)"),
        ("a + 5 - b - 5", "a - b"),
        ("a + 5 - 3", "a + 2 - 0"),
        ("5 - a - 3", "2 - a"),
        ("3 - a - 3", "0 - a"),
        ("(5::nat) - 3", "(2::nat) - 0"),
        ("(3::nat) - 3", "(0::nat) - 0")
      ]
    in
      map (test_wfconv NatSub.norm_minus "test") test_data
    end

end
