(* Testing of rings.ML. *)

local
  val ctxt = @{context}
  val ctxt' = ctxt |> fold Variable.auto_fixes [
        @{term_pat "[a::int, b, c]"}, @{term_pat "[r::rat, s, t]"}]
  open Ring_Arith
in

val test_fold_add_rat =
    let
      val test = test_conv ctxt' fold_add_rat "fold_add_rat"
      val test_data = [
        ("2 + 3::int", "5::int"),
        ("1 + -Fract 3 2", "-inverse 2::rat"),
        ("1 + -Fract 5 2", "-Fract 3 2::rat"),
        ("1 + of_rat (-Fract 3 2)::'a::field_char_0",
         "- (inverse 2)::'a::field_char_0"),
        ("1 + (-inverse 2)::'a::field_char_0", "inverse 2::'a::field_char_0")
      ]
    in
      map test test_data
    end

val test_fold_mult_rat =
    let
      val test = test_conv ctxt' fold_mult_rat "fold_mult_rat"
      val test_data = [
        ("2 * 3::int", "6::int"),
        ("1 * (inverse 0)::rat", "0::rat"),
        ("0 * (-1)::rat", "0::rat")
      ]
    in
      map test test_data
    end

val test_norm_mult_monomial =
    let
      val test = test_conv ctxt' norm_mult_monomial "norm_mult_monomial"
      val test_data = [
        ("2 * 3::int", "6::int"),
        ("(-1) * (-1)::int", "1::int"),
        ("1 * a", "a"),
        ("a * 1", "a"),
        ("2 * a", "a * 2"),
        ("a * 2", "a * 2"),
        ("a * b", "a * b"),
        ("b * a", "a * b"),
        ("b * c * a", "a * b * c"),
        ("a * b * c", "a * b * c"),
        ("a * (b * c)", "a * b * c"),
        ("c * (a * b)", "a * b * c"),
        ("(c * 2) * (a * b * -1)", "a * b * c * (-2)"),
        ("(a * -1) * (b * -1)", "a * b"),
        ("(a * b * c) * (a * b * c)", "a^2 * b^2 * c^2"),
        ("a * 0", "0::int"),
        ("0 * a", "0::int"),
        ("r * inverse 2 * 2", "r"),
        ("r * inverse 2 * 3", "r * Fract 3 2"),
        ("(inverse 2) * (2::rat)", "1::rat"),
        ("r * (-3) * (-2)", "r * 6"),
        ("r * inverse s * inverse s", "r * (inverse s)^2"),
        ("x * 2 * 3::'a::ring_1", "x * 6::'a::ring_1"),
        ("x * 2 * 3::'a::field_char_0", "x * 6::'a::field_char_0"),
        ("x * 2 * (inverse 3)::'a::field_char_0",
         "x * of_rat (Fract 2 3)::'a::field_char_0")
      ]
    in
      map test test_data
    end

val test_norm_add_polynomial =
    let
      val test = test_conv ctxt' norm_add_polynomial "norm_add_polynomial"
      val test_data = [
        ("a + a", "a * 2"),
        ("a + b", "a + b"),
        ("(a + b) + a * 2", "a * 3 + b"),
        ("(a + 2) + (3 + b)", "a + b + 5"),
        ("2 + 3::int", "5::int"),
        ("a + a * -1", "0::int"),
        ("a + b + a * -1", "b"),
        ("(a + 2) + (a * -1 + 3)", "5::int"),
        ("a + (a * -1 + b)", "b"),
        ("a + (a * -1 + 3)", "3::int"),
        ("(a + b + c) + (a + b + c)", "a * 2 + b * 2 + c * 2"),
        ("r * Fract 3 2 + r * Fract 2 3", "r * Fract 13 6"),
        ("r * Fract 3 2 + r * Fract (-3) 2", "0::rat"),
        ("r + -0", "r"),
        ("x + x::'a::ring_1", "x * 2::'a::ring_1"),
        ("x + x::'a::field_char_0", "x * 2::'a::field_char_0"),
        ("x + x * (inverse 3)::'a::field_char_0",
         "x * (of_rat (Fract 4 3))::'a::field_char_0")
      ]
    in
      map test test_data
    end

val test_norm_mult_polynomials =
    let
      val test = test_conv ctxt' norm_mult_polynomials "norm_mult_polynomials"
      val test_data = [
        ("a * b", "a * b"),
        ("a * (b * -1)", "a * b * -1"),
        ("(a + b) * c", "a * c + b * c"),
        ("a * (b + c)", "a * b + a * c"),
        ("(a + b) * (a + c)", "a * b + a * c + b * c + a^2"),
        ("(a + b * -1) * (c * -1)", "a * c * -1 + b * c"),
        ("(a * -1) * (b * -1 + c)", "a * b + a * c * -1"),
        ("(a + b + c) * (a + b)", "a * b * 2 + a * c + b * c + a^2 + b^2"),
        ("a * (a + 1)", "a + a^2"),
        ("r * 2 * inverse 2", "r")
      ]
    in
      map test test_data
    end

val test_norm_full =
    let
      val test = test_conv ctxt' norm_full "norm_full"
      val test_data = [
        ("-a", "a * -1"),
        ("a * b", "a * b"),
        ("a * -b", "a * b * -1"),
        ("a + (b + c)", "a + b + c"),
        ("-a * -b", "a * b"),
        ("(a + b) * (a + b)", "a * b * 2 + a^2 + b^2"),
        ("(a + b) * (a - b)", "a^2  + b^2 * -1"),
        ("(a + 1) * (a - 1)", "a^2 + -1"),
        ("(a + 3) * (a - 2)", "a + a^2 + -6"),
        ("(a + 2 * b) * (a + 3 * b)", "a * b * 5 + a^2 + b^2 * 6"),
        ("(a + b) * a * b", "a * b^2 + a^2 * b"),
        ("a * (a + b) * b", "a * b^2 + a^2 * b"),
        ("(a + b) * (a - b) * c", "a^2 * c + b^2 * c * -1"),
        ("2 * (a + b)", "a * 2 + b * 2"),
        ("2 * (a + 1)", "a * 2 + 2"),
        ("-1 * (a - 1)", "a * -1 + 1"),
        ("(a + 1) * (a + 1) * (a + 1)", "a * 3 + a^2 * 3 + a^3 + 1"),
        ("a + b * (c + a * b)", "a + b * c + a * b^2"),
        ("(a + b)^2", "a * b * 2 + a^2 + b^2"),
        ("(a + b)^3", "a^3 + b^3 + a * b^2 * 3 + a^2 * b * 3"),
        ("a + b + 2 * b - 3 * b - a", "0::int"),
        ("r * Fract 3 2 * 2 + r * 3", "r * 6"),
        ("r * Fract 3 2 - r * Fract 3 4 - r * Fract 3 4", "0::rat"),
        ("r * Fract 3 2 - r - r * inverse 2", "0::rat"),
        ("(r + s) * inverse 2 + (r - s) * inverse 2", "r"),
        ("(2::int) ^ n - 0", "(2::int) ^ n"),
        ("(1::rat) / 2", "inverse (2::rat)"),
        ("(3::rat) / 5", "Fract 3 5"),
        ("r / 2", "r * inverse 2"),
        ("r * (s + 1) / 2", "r * inverse 2 + r * s * inverse 2"),
        ("x - (x - y)::'a::comm_ring_1", "y::'a::comm_ring_1"),
        ("x * -1 + y + (x - y)::'a::comm_ring_1", "0::'a::comm_ring_1"),
        ("(x::'a::field_char_0) - (x * inverse 2 + y)",
         "(x::'a::field_char_0) * inverse 2 + y * -1")
      ]
    in
      map test test_data
    end

val test_polynomial_terms =
    let
      fun test (str_t, strs) =
          let
            val t = read_term ctxt' str_t
            val ts = map (read_term ctxt') strs
            val ts' = polynomial_terms t
          in
            if length ts = length ts' andalso forall (op aconv) (ts ~~ ts')
            then () else
            let
              val _ = trace_t_ctxt ctxt' "Input:" t
              val _ = trace_tlist_ctxt ctxt' "Expected:" ts
              val _ = trace_tlist_ctxt ctxt' "Actual:" ts'
            in
              raise AUTO2 "test_polynomial_terms"
            end
          end

      val test_data = [
        ("a^2", ["a"]),
        ("a + b * 3", ["a", "b"]),
        ("a * b + a + b", ["a", "b"]),
        ("a + b * c + (a + b)^2", ["a", "b", "c", "a + b"]),
        ("a ^ k", ["a ^ k"]),
        ("a + 1", ["a"]),
        ("r * inverse 3 + s * 2", ["r", "s"]),
        ("r * inverse s", ["r", "inverse s"]),
        ("r * s * inverse s", ["r", "s", "inverse s"])
      ]
    in
      map test test_data
    end

val test_cancel_inverse =
    let
      fun test (str_t, str_t') =
          let
            val t = read_term ctxt' str_t
            val a = dest_arg t
            val T = fastype_of t
            val prop = (mk_eq (a, HOLogic.mk_number T 0))
                           |> get_neg |> mk_Trueprop
            val neq0_th = assume_thm ctxt' prop
          in
            test_conv ctxt' (cancel_inverse_polynomial neq0_th)
                      "test_cancel_inverse" (str_t, str_t')
          end

      val test_data = [
        ("r * s", "r * s"),
        ("inverse r * r", "1::rat"),
        ("r * inverse s * s", "r"),
        ("inverse s * r * s", "r"),
        ("(inverse r + inverse s) * s", "s * inverse r + 1"),
        ("inverse (r + s) * (r + s)", "1::rat"),
        ("(r + inverse (r + s)) * (r + s)", "r * s + r^2 + 1"),
        ("(inverse r + inverse (r + s)) * (r + s)",
         "r * inverse r + s * inverse r + 1"),
        ("(inverse r + inverse (r + s)) * r", "r * inverse (r + s) + 1")
      ]
    in
      map test test_data
    end

val test_split_polynomial_by_sign =
    let
      val test = test_conv ctxt' split_polynomial_by_sign
                           "split_polynomial_by_sign"
      val test_data = [
        ("a", "a - 0"),
        ("a * -1", "0 - a"),
        ("a + b * -1", "a - b"),
        ("a + b", "a + b - 0"),
        ("a * -1 + b * -1", "0 - (a + b)"),
        ("a * -1 + b", "b - a"),
        ("(2 ^ n)::rat", "(2 ^ n - 0)::rat")
      ]
    in
      map test test_data
    end

end
