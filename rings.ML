(* Algebraic manipulation for rings. *)

signature RING_ARITH =
sig
  val mk_rat: typ -> Rat.rat -> term
  val fold_add_rat: conv
  val fold_mult_rat: conv
  val norm_mult_monomial: conv
  val norm_add_polynomial: conv
  val norm_mult_polynomials: conv
  val norm_full: conv
  val polynomial_terms: term -> term list
  val cancel_inverse_polynomial: thm -> conv
  val split_polynomial_by_sign: conv
end;

structure Ring_Arith : RING_ARITH =
struct

fun is_plus t =
    case t of
        Const (@{const_name plus}, _) $ _ $ _ => true
      | _ => false

fun is_times t =
    case t of
        Const (@{const_name times}, _) $ _ $ _ => true
      | _ => false

fun mk_rat T r =
    let
      val (n, d) = Rat.quotient_of_rat r
    in
      if n < 0 then
        Const (@{const_name uminus}, T --> T)
              $ mk_rat T (Rat.rat_of_quotient (~n, d))
      else if d = 1 then HOLogic.mk_number T n
      else if T = natT orelse T = intT then
        raise AUTO2 "mk_rat"
      else if T = ratT then
        if n = 1 then
          Const (@{const_name inverse}, T --> T) $ HOLogic.mk_number T d
        else
          Const (@{const_name Fract}, intT --> intT --> T) $
                HOLogic.mk_number intT n $ HOLogic.mk_number intT d
      else
        Const (@{const_name of_rat}, ratT --> T) $ mk_rat ratT r
    end

fun is_zero t = is_numc t andalso dest_numc_rat t = Rat.zero

local
  val ctxt = @{context}
  val ctxt' = ctxt addsimps (@{thms eq_rat} @ @{thms rat_number_expand})
in

val reduce_of_rat_eqs =
    [@{thm Rat.of_rat_1}, @{thm Rat.of_rat_neg_one}, @{thm Rat.of_rat_0},
     @{thm Rat.of_rat_numeral_eq}, @{thm Rat.of_rat_neg_numeral_eq},
     @{thm Rat.of_rat_inverse}, @{thm of_rat_inverse_numeral},
     @{thm of_rat_minus}]

fun rewrite_to_of_rat ct =
    case Thm.term_of ct of
        Const (@{const_name of_rat}, _) $ _ => Conv.all_conv ct
      | _ => Conv.every_conv [
              Conv.try_conv (Conv.arg_conv rewrite_to_of_rat),
              Conv.first_conv (map (rewr_obj_eq o obj_sym) reduce_of_rat_eqs)
            ] ct

fun reduce_of_rat ct =
    Conv.every_conv [
      Conv.try_conv (Conv.first_conv (map rewr_obj_eq reduce_of_rat_eqs)),
      Conv.try_conv (Conv.arg_conv reduce_of_rat)] ct

val reduce_of_int_eqs =
    [@{thm Int.of_int_1}, @{thm of_int_neg_one}, @{thm Int.of_int_0},
     @{thm Int.of_int_numeral}, @{thm Int.of_int_neg_numeral},
     @{thm of_int_minus}]

fun rewrite_to_of_int ct =
    case Thm.term_of ct of
        Const (@{const_name of_int}, _) $ _ => Conv.all_conv ct
      | _ => Conv.first_conv (map (rewr_obj_eq o obj_sym) reduce_of_int_eqs) ct

fun reduce_of_int ct =
    Conv.every_conv (map (Conv.try_conv o rewr_obj_eq) reduce_of_int_eqs) ct

(* Fold addition of constants c1 + c2. *)
fun fold_add_rat ct =
    let
      val t = Thm.term_of ct
      val T = fastype_of t
      val c1 = dest_numc_rat (dest_arg1 t)
      val c2 = dest_numc_rat (dest_arg t)
      val thy = Thm.theory_of_cterm ct
    in
      if T = natT orelse T = intT orelse T = ratT then
        (HOLogic.mk_eq (t, mk_rat T (Rat.add c1 c2)))
            |> prove_by_simp ctxt' [] |> to_meta_eq
      else if Sign.of_sort thy (T, @{sort field_char_0}) then
        let
          val sum = mk_rat ratT (Rat.add c1 c2)
          val t' = Const (@{const_name plus}, ratT --> ratT --> ratT)
                         $ mk_rat ratT c1 $ mk_rat ratT c2
          val th = prove_by_simp ctxt' [] (HOLogic.mk_eq (t', sum))
        in
          Conv.every_conv [
            Conv.binop_conv rewrite_to_of_rat,
            rewr_obj_eq (obj_sym @{thm Rat.of_rat_add}),
            Conv.arg_conv (rewr_obj_eq th),
            reduce_of_rat] ct
        end
      else if Sign.of_sort thy (T, @{sort ring_1}) then
        let
          val sum = mk_rat intT (Rat.add c1 c2)
          val t' = Const (@{const_name plus}, intT --> intT --> intT)
                         $ mk_rat intT c1 $ mk_rat intT c2
          val th = prove_by_simp ctxt' [] (HOLogic.mk_eq (t', sum))
        in
          Conv.every_conv [
            Conv.binop_conv rewrite_to_of_int,
            rewr_obj_eq (obj_sym @{thm Int.of_int_add}),
            Conv.arg_conv (rewr_obj_eq th),
            reduce_of_int] ct
        end
      else raise AUTO2 "fold_add_rat: unexpected type."
    end

(* Fold multiplication of constants c1 * c2. *)
fun fold_mult_rat ct =
    let
      val t = Thm.term_of ct
      val T = fastype_of t
      val c1 = dest_numc_rat (dest_arg1 t)
      val c2 = dest_numc_rat (dest_arg t)
      val thy = Thm.theory_of_cterm ct
    in
      if T = natT orelse T = intT orelse T = ratT then
        (HOLogic.mk_eq (t, mk_rat T (Rat.mult c1 c2)))
            |> prove_by_simp ctxt' [] |> to_meta_eq
      else if Sign.of_sort thy (T, @{sort field_char_0}) then
        let
          val prod = mk_rat ratT (Rat.mult c1 c2)
          val t' = Const (@{const_name times}, ratT --> ratT --> ratT)
                         $ mk_rat ratT c1 $ mk_rat ratT c2
          val th = prove_by_simp ctxt' [] (HOLogic.mk_eq (t', prod))
        in
          Conv.every_conv [
            Conv.binop_conv rewrite_to_of_rat,
            rewr_obj_eq (obj_sym @{thm Rat.of_rat_mult}),
            Conv.arg_conv (rewr_obj_eq th),
            reduce_of_rat] ct
        end
      else if Sign.of_sort thy (T, @{sort ring_1}) then
        let
          val prod = mk_rat intT (Rat.mult c1 c2)
          val t' = Const (@{const_name times}, intT --> intT --> intT)
                         $ mk_rat intT c1 $ mk_rat intT c2
          val th = prove_by_simp ctxt' [] (HOLogic.mk_eq (t', prod))
        in
          Conv.every_conv [
            Conv.binop_conv rewrite_to_of_int,
            rewr_obj_eq (obj_sym @{thm Int.of_int_mult}),
            Conv.arg_conv (rewr_obj_eq th),
            reduce_of_int] ct
        end
      else raise AUTO2 "fold_mult_rat: unexpected type."
    end

end  (* local ctxt = @{context}. *)

(* An atom is a term that is not a numeric constant, and whose head is
   not plus, minus, uminus, or times.

   A monomial is either a numeric constant, or a product of atoms,
   followed by a numeric constant.

   A polynomial is a sum of monomials, each with a unique body.
 *)

(* Assume t is not a numeric constant. Return a if t = a^n where n is
   a numeric constant. Otherwise return t.
 *)
fun extract_atom_body t =
    case t of
        Const (@{const_name power}, _) $ A $ B => if is_numc B then A else t
      | _ => t

(* Comparison on bodies of atoms. Numeric constants are equal to each
   other and larger than powers. For two powers a^m and b^n, return
   the comparison between a and b.
 *)
fun compare_atom_body (t1, t2) =
    if is_numc t1 then
      if is_numc t2 then EQUAL else GREATER
    else
      if is_numc t2 then LESS
      else Term_Ord.term_ord (extract_atom_body t1, extract_atom_body t2)

(* Rewrite m without constant powers to m^1. *)
fun normalize_power ct =
    let
      val rewr_power1 = rewr_obj_eq (obj_sym @{thm power_one_right})
    in
      case Thm.term_of ct of
          Const (@{const_name power}, _) $ _ $ B =>
          if is_numc B then Conv.all_conv ct else rewr_power1 ct
        | _ => rewr_power1 ct
    end

(* Given ct of form t1 * t2, where the bodies of t1 and t2 are EQUAL,
   perform the natural multiplication.
 *)
fun join_atom ct =
    if is_numc (dest_arg (Thm.term_of ct)) then fold_mult_rat ct
    else Conv.every_conv [Conv.binop_conv normalize_power,
                          rewr_obj_eq @{thm semiring_normalization_rules(26)},
                          Conv.arg_conv fold_add_rat] ct

(* Attempt to apply mult_1_right. *)
val try_reduce_mult1 =
    Conv.try_conv (rewr_obj_eq @{thm mult_1_right})

(* Attempt to apply add_0 and add_0_right. *)
val try_reduce_add0 =
    Conv.try_conv (
      rewr_obj_eq @{thm add_0} else_conv rewr_obj_eq @{thm add_0_right})

(* Perform the multiplication (a_1 * ... * a_n) * a, where each a_i
   and a are atoms.
 *)
fun norm_mult_atom ct =
    let
      val (arg1, arg2) = ct |> Thm.term_of |> dest_binop |> snd
    in
      if is_zero arg1 then  (* 0 * x *)
        rewr_obj_eq @{thm mult_zero_left} ct
      else if is_zero arg2 then  (* x * 0 *)
        rewr_obj_eq @{thm mult_zero_right} ct
      else if is_times arg1 then
        case compare_atom_body (dest_arg arg1, arg2) of
            EQUAL => Conv.every_conv [rewr_obj_eq @{thm mult_ac(1)},
                                      Conv.arg_conv join_atom,
                                      try_reduce_mult1] ct
          | LESS => try_reduce_mult1 ct
          | GREATER => Conv.every_conv [
                        rewr_obj_eq @{thm semiring_normalization_rules(16)},
                        Conv.arg1_conv norm_mult_atom] ct
      else
        case compare_atom_body (arg1, arg2) of
            EQUAL => join_atom ct
          | LESS => try_reduce_mult1 ct
          | GREATER => Conv.every_conv [rewr_obj_eq @{thm mult.commute},
                                        try_reduce_mult1] ct
    end

(* Perform the multiplication (a_1 * ... * a_n) * (b_1 * ... * b_n),
   where each a_i and b_i are atoms.
 *)
fun norm_mult_monomial ct =
    if is_times (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [
        rewr_obj_eq (obj_sym @{thm mult_ac(1)}),
        Conv.arg1_conv norm_mult_monomial,
        norm_mult_atom] ct
    else
      norm_mult_atom ct

(* Assume t is not a numeric constant. Return a if t = a * c where c
   is a numeric constant. Otherwise return t.
 *)
fun extract_monomial_body t =
    case t of
        Const (@{const_name times}, _) $ A $ B => if is_numc B then A else t
      | _ => t

(* Comparison on bodies of monomials. Numeric constants are equal to
   each other and larger than monomials. For two monomials x*c1 and
   y*c2, return the comparison between x and y.
 *)
fun compare_monomial_body (t1, t2) =
    if is_numc t1 then
      if is_numc t2 then EQUAL else GREATER
    else
      if is_numc t2 then LESS
      else Term_Ord.term_ord (
          extract_monomial_body t1, extract_monomial_body t2)

(* Rewrite m without constant coefficients to m * 1. *)
fun normalize_monomial ct =
    let
      val rewr_mult1 = rewr_obj_eq (obj_sym @{thm mult_1_right})
    in
      case Thm.term_of ct of
          Const (@{const_name times}, _) $ _ $ B =>
          if is_numc B then Conv.all_conv ct else rewr_mult1 ct
        | _ => rewr_mult1 ct
    end

(* Given ct of form t1 + t2, where the bodies of t1 and t2 are EQUAL,
   perform the natural addition. Note if the result is a * 0, it
   should be reduced to 0, and if the result is a * 1, it should be
   reduced to a.
 *)
fun join_monomial ct =
    if is_numc (dest_arg (Thm.term_of ct)) then fold_add_rat ct
    else Conv.every_conv [
        Conv.binop_conv normalize_monomial,
        rewr_obj_eq (obj_sym @{thm ring_distribs(1)}),
        Conv.arg_conv fold_add_rat,
        try_reduce_mult1,
        Conv.try_conv (rewr_obj_eq @{thm mult_zero_right})] ct

(* Addition between a polynomial and a monomial. Input is of the form
   (a_1 + ... + a_n) + a, where a_1, ... a_n are guaranteed to have
   different bodies, compare the body of a to that of each of
   a_i. Merge with any matches.
 *)
fun norm_add_monomial ct =
    let
      val (arg1, arg2) = ct |> Thm.term_of |> dest_binop |> snd
    in
      if is_zero arg1 then  (* 0 + x *)
        Conv.every_conv [
          Conv.try_conv (Conv.arg1_conv (rewr_obj_eq @{thm minus_zero})),
          rewr_obj_eq @{thm add_0}] ct
      else if is_zero arg2 then  (* x + 0 *)
        Conv.every_conv [
          Conv.try_conv (Conv.arg_conv (rewr_obj_eq @{thm minus_zero})),
          rewr_obj_eq @{thm add_0_right}] ct
      else if is_plus arg1 then
        case compare_monomial_body (dest_arg arg1, arg2) of
            EQUAL => Conv.every_conv [rewr_obj_eq @{thm add_ac(1)},
                                      Conv.arg_conv join_monomial,
                                      try_reduce_add0] ct
          | LESS => Conv.all_conv ct
          | GREATER => Conv.every_conv [
                        rewr_obj_eq @{thm semiring_normalization_rules(23)},
                        Conv.arg1_conv norm_add_monomial,
                        try_reduce_add0] ct
      else
        case compare_monomial_body (arg1, arg2) of
            EQUAL => join_monomial ct
          | LESS => Conv.all_conv ct
          | GREATER => rewr_obj_eq @{thm add.commute} ct
    end

(* Perform the addition (a_1 + ... + a_n) + (b_1 + ... + b_n), where
   each a_i and b_i are monomials.
 *)
fun norm_add_polynomial ct =
    if is_plus (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [
        rewr_obj_eq (obj_sym @{thm add_ac(1)}),
        Conv.arg1_conv norm_add_polynomial,
        norm_add_monomial] ct
    else
      norm_add_monomial ct

(* Multiplication between a polynomial and a monomial. *)
fun norm_mult_poly_monomial ct =
    if is_plus (dest_arg1 (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq @{thm ring_distribs(2)},
                       Conv.arg1_conv norm_mult_poly_monomial,
                       Conv.arg_conv norm_mult_monomial,
                       norm_add_polynomial] ct
    else
      norm_mult_monomial ct

(* Multiplication between two polynomials. *)
fun norm_mult_polynomials ct =
    if is_plus (dest_arg (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq @{thm ring_distribs(1)},
                       Conv.arg1_conv norm_mult_polynomials,
                       Conv.arg_conv norm_mult_poly_monomial,
                       norm_add_polynomial] ct
    else
      norm_mult_poly_monomial ct

(* Reduce a^0 to 1 and a^n to a * a^(n-1). *)
fun reduce_power ct =
    let
      val n = dest_arg (Thm.term_of ct)
    in
      if not (is_numc n) then Conv.no_conv ct
      else if dest_numc n = 0 then rewr_obj_eq @{thm power_0} ct
      else Conv.every_conv [
          rewr_obj_eq ((Nat_Arith.nat_neq_th (dest_numc n) 0)
                           RS @{thm power_ge_0}),
          Conv.arg_conv (Conv.arg_conv Nat_Arith.nat_fold_conv)] ct
    end

(* Full normalization procedure. *)
fun norm_full ct =
    if is_numc (Thm.term_of ct) then
      Conv.all_conv ct
    else
      case Term.head_of (Thm.term_of ct) of
          Const (@{const_name times}, _) =>
          (Conv.binop_conv norm_full then_conv norm_mult_polynomials) ct
        | Const (@{const_name plus}, _) =>
          (Conv.binop_conv norm_full then_conv norm_add_polynomial) ct
        | Const (@{const_name uminus}, _) =>
          (rewr_obj_eq @{thm ring_normalization_rules(1)}
                            then_conv norm_full) ct
        | Const (@{const_name minus}, _) =>
          (rewr_obj_eq @{thm diff_conv_add_uminus} then_conv norm_full) ct
        | Const (@{const_name divide}, _) =>
          (rewr_obj_eq @{thm divide_inverse} then_conv norm_full) ct
        | Const (@{const_name power}, _) =>
          Conv.try_conv (reduce_power then_conv norm_full) ct
        | _ => Conv.all_conv ct

(* Return the list of terms that appear in a polynomial. *)
fun atom_terms t =
    if is_numc t then [] else [extract_atom_body t]

fun monomial_terms t =
    if is_times t then
      atom_terms (dest_arg t) @ monomial_terms (dest_arg1 t)
    else atom_terms t

fun polynomial_terms' t =
    if is_plus t then
      monomial_terms (dest_arg t) @ polynomial_terms' (dest_arg1 t)
    else monomial_terms t

fun polynomial_terms t =
    t |> polynomial_terms' |> distinct (op aconv) |> sort Term_Ord.term_ord

(* Apply the rule r ~= 0 ==> r * inverse r = 1 on polynomials. This
   reduces to applying the rule on monomials. Here ct is of form x *
   a, where x is a monomial / polynomial, and th shows a ~= 0.
 *)

(* This function fails if inverse a is not found in the monomial t. *)
fun cancel_inverse_monomial' th ct =
    let
      val (m, a) = ct |> Thm.term_of |> dest_binop |> snd
      val T = fastype_of a
      val inv_a = Const (@{const_name inverse}, T --> T) $ a
    in
      if is_times m then
        if dest_arg m aconv inv_a then
          Conv.every_conv [
            rewr_obj_eq @{thm mult_ac(1)},
            Conv.arg_conv (rewr_obj_eq (th RS @{thm left_inverse})),
            rewr_obj_eq @{thm mult_1_right}] ct
        else
          Conv.every_conv [
            rewr_obj_eq @{thm semiring_normalization_rules(16)},
            Conv.arg1_conv (cancel_inverse_monomial' th),
            norm_mult_atom] ct
      else
        if m aconv inv_a then
          rewr_obj_eq (th RS @{thm left_inverse}) ct
        else
          Conv.no_conv ct
    end

(* First try to cancel, then use norm_full if fails. *)
fun cancel_inverse_monomial th ct =
    Conv.first_conv [cancel_inverse_monomial' th, norm_full] ct

(* Here m is a polynomial a_1 + ... + a_n. Attempt to cancel on each
   of the terms. Note similarity to norm_mult_polynomials.
 *)
fun cancel_inverse_polynomial th ct =
    if is_plus (dest_arg1 (Thm.term_of ct)) then
      Conv.every_conv [rewr_obj_eq @{thm ring_distribs(2)},
                       Conv.arg1_conv (cancel_inverse_polynomial th),
                       Conv.arg_conv (cancel_inverse_monomial th),
                       norm_add_polynomial] ct
    else
      cancel_inverse_monomial th ct

(* Given a normalized polynomial, write it in the form A - B, where A
   and B both have all positive coefficients.
 *)
fun split_polynomial_by_sign ct =
    if is_plus (Thm.term_of ct) then
      Conv.every_conv [
        Conv.arg1_conv split_polynomial_by_sign,
        Conv.arg_conv normalize_monomial,
        Conv.first_conv [
          Conv.every_conv [
            rewr_obj_eq @{thm split_by_sign2},
            Conv.arg_conv (Conv.arg_conv try_reduce_mult1),
            Conv.arg_conv try_reduce_add0],
          Conv.every_conv [
            rewr_obj_eq @{thm split_by_sign1},
            Conv.arg1_conv (Conv.arg_conv try_reduce_mult1),
            Conv.arg1_conv try_reduce_add0]]] ct
    else
      Conv.first_conv [
        Conv.every_conv [
          rewr_obj_eq @{thm split_by_sign4},
          Conv.arg_conv try_reduce_mult1],
        Conv.every_conv [
          rewr_obj_eq (obj_sym @{thm diff_0_right}),
          Conv.arg1_conv try_reduce_mult1]] ct

end  (* structure Ring_Arith. *)
