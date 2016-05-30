(* Unit test for rat_arith.ML. *)

local

  val ctxt = @{context}
  val thy = @{theory}
  open Rat_Arith

in

val test_shift_neg_cv =
    let
      val ctxt' = ctxt |> Variable.declare_term @{term "a::int"}
      val test = test_conv ctxt' (shift_neg_cv thy) "test_shift_neg_cv"

      val test_data = [
        (* Test for shifting once. *)
        ("a < b", "a < b"),
        ("a < b + (-c)", "a + c < b"),
        ("a + (-c) < b", "a < b + c"),
        ("a <= b", "a <= b"),
        ("a <= b + (-c)", "a + c <= b"),
        ("a + (-c) <= b", "a <= b + c"),
        ("-a < b", "0 < b + a"),
        ("a < -b", "a + b < 0"),
        ("-a < 0", "0 < a"),
        ("0 < -a", "a < 0"),

        (* Test for shifting multiple times. *)
        ("-a < -b", "b < a"),
        ("0 < -a + -b", "a + b < 0"),
        ("-a + -b < 0", "0 < a + b")
      ]
    in
      map test test_data
    end

val test_rewrite_with_coeff =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [
            @{term "a::int"}, @{term "r::('a::linordered_field)"}]
      val test = test_conv ctxt' (rewrite_with_coeff thy)
                           "test_rewrite_with_coeff"

      val test_data = [
        ("a", "a * 1"),
        ("-a", "a * (-1)"),
        ("2 * a", "a * 2"),
        ("-(2 * a)", "a * (-2)"),
        ("-(inverse 3 * r)", "r * (- inverse 3)"),
        ("-(r * s)", "r * s * (-1)"),
        ("1::int", "1 * 1::int"),
        ("(-1)::int", "1 * (-1)::int"),
        ("(inverse 2)::rat", "1 * (inverse 2)::rat")
      ]
    in
      map test test_data
    end

fun equiv_fn ctxt (u, v) =
    if u aconv v then SOME (Thm.reflexive (cert ctxt u))
    else NONE

val test_combine_terms_once =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [
            @{term "a::int"}, @{term "r::rat"},
            @{term "x::('a::linordered_field)"}]
      val test = test_conv ctxt' (combine_terms_once (equiv_fn ctxt') ctxt')
                           "test_combine_terms_once"

      val test_data = [
        ("a * 1 + a * 1", "a * 2"),
        ("a * 1 + a * (-1)", "0::int"),
        ("r * 1 + r * (inverse 2)", "r * Fract 3 2"),
        ("r * 1 + r * (- inverse 2)", "r * inverse 2"),
        ("a * 1 + b * 1 + a * 1", "b * 1 + a * 2"),
        ("a * 1 + b * 1 + a * (-1)", "(b::int) * 1"),
        ("x * 1 + x * (- inverse 2)", "x * inverse 2")
      ]
    in
      map test test_data
    end

val test_combine_terms_gen =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [
            @{term "a::int"}, @{term "r::rat"},
            @{term "x::('a::linordered_field)"}]
      val test = test_conv ctxt' (combine_terms_gen (equiv_fn ctxt') ctxt')
                           "test_combine_terms_gen"

      val test_data = [
        ("a + a", "a * 2"),
        ("a + (-a)", "0::int"),
        ("r + r * inverse 2", "r * Fract 3 2"),
        ("r + -(r * inverse 2)", "r * inverse 2"),
        ("a + b + a", "b + a * 2"),
        ("a + b + (-a)", "b::int"),
        ("a", "a"),
        ("a + b", "a + b"),
        ("r + r * (inverse 2) + r * (inverse 3)", "r * Fract 11 6"),
        ("(-r) + r * inverse 2", "-(r * inverse 2)"),
        ("x + -(x * inverse 2)", "x * inverse 2"),
        ("x + (-x)", "0::('a::linordered_field)"),
        ("x + (-x) + y + (-z)", "(y::('a::linordered_field)) + (-z)"),
        ("a + a + 0", "a * 2"),
        ("r * inverse 2 + r * inverse 2", "r")
      ]
    in
      map test test_data
    end

val test_combine_terms_ineq =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [
            @{term "a::int"}, @{term "r::rat"},
            @{term "x::('a::linordered_field)"}]
      val test = test_conv ctxt' (combine_terms_ineq_cv (equiv_fn ctxt') ctxt')
                           "test_combine_terms_ineq"

      val test_data = [
        ("a < a * 2", "0 < a"),
        ("r < r * inverse 2", "r * inverse 2 < 0"),
        ("r * inverse 2 + s * inverse 2 < r", "s * inverse 2 < r * inverse 2"),
        ("x * inverse 2 <= x", "0 <= x * inverse 2"),
        ("a + b < a * 2 + c + 0", "b < c + a")
      ]
    in
      map test test_data
    end

end
