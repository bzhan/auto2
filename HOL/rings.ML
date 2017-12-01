(* Normalization in natural numbers *)

signature NAT_RING =
sig
  val norm_mult_atom: conv
  val norm_mult_monomial: conv

  val dest_monomial: term -> term * int
  val norm_monomial: conv
  val combine_monomial: conv
  val norm_add_monomial: conv
  val norm_add_polynomial: conv
  val norm_mult_poly_monomial: conv
  val norm_mult_polynomials: conv
  val norm_full: conv
end;

structure NatRing : NAT_RING =
struct

val mult_1 = @{thm mult_1}  (* 1 * a = a *)
val mult_1_right = @{thm mult_1_right}  (* a * 1 = a *)
val mult_0 = @{thm mult_0}  (* 0 * a = 0 *)
val mult_0_right = @{thm mult_0_right}  (* a * 0 = 0 *)
val add_0 = @{thm add_0}  (* 0 + a = a *)
val add_0_right = @{thm add_0_right}  (* a + 0 = a *)
val distrib_r = @{thm nat_distrib(1)}  (* (m + n) * k = m * k + n * k *)
val distrib_l = @{thm nat_distrib(2)}  (* a * (b + c) = a * b + a * c *)
val times_ac_info = Nat_Arith.times_ac_on_typ @{theory} natT
val plus_ac_info = Nat_Arith.plus_ac_on_typ @{theory} natT
val is_numc = UtilArith.is_numc
val is_plus = Nat_Arith.is_plus
val nat_fold_conv = Nat_Arith.nat_fold_conv

fun is_times t =
    case t of
        Const (@{const_name times}, _) $ _ $ _ => true
      | _ => false

fun is_zero t =
    case t of
        Const (@{const_name zero_class.zero}, _) => true
      | _ => false

fun is_one t =
    case t of
        Const (@{const_name one_class.one}, _) => true
      | _ => false

fun is_Suc t =
    case t of
        Const (@{const_name Suc}, _) $ _ => true
      | _ => false

fun compare_atom (t1, t2) =
    if is_numc t1 andalso is_numc t2 then EQUAL
    else if is_numc t1 then GREATER
    else if is_numc t2 then LESS
    else Term_Ord.term_ord (t1, t2)

fun norm_mult_atom ct =
    let
      val t = Thm.term_of ct
      val (arg1, arg2) = Util.dest_binop_args t
    in
      if is_one arg1 then rewr_obj_eq mult_1 ct
      else if is_one arg2 then rewr_obj_eq mult_1_right ct
      else if is_zero arg1 then rewr_obj_eq mult_0 ct
      else if is_zero arg2 then rewr_obj_eq mult_0_right ct
      else if is_times arg1 then
        case compare_atom (dest_arg arg1, arg2) of
            GREATER => Conv.every_conv [ACUtil.swap_cv times_ac_info,
                                        Conv.arg1_conv norm_mult_atom] ct
          | EQUAL =>
            if is_numc (dest_arg arg1) andalso is_numc arg2 then
              Conv.every_conv [ACUtil.assoc_cv times_ac_info,
                               Conv.arg_conv nat_fold_conv] ct
            else
              Conv.all_conv ct
          | _ => Conv.all_conv ct
      else
        case compare_atom (arg1, arg2) of
            GREATER => ACUtil.comm_cv times_ac_info ct
          | EQUAL =>
            if is_numc arg1 andalso is_numc arg2 then
              nat_fold_conv ct
            else
              Conv.all_conv ct
          | _ => Conv.all_conv ct
    end

fun norm_mult_monomial ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_times arg2 then
        Conv.every_conv [ACUtil.assoc_sym_cv times_ac_info,
                         Conv.arg1_conv norm_mult_monomial,
                         norm_mult_atom] ct
      else
        norm_mult_atom ct
    end

(* Destruct t into the form arg * coeff, where coeff is a constant. *)
fun dest_monomial t =
    if is_times t andalso is_numc (dest_arg t) then
      (dest_arg1 t, UtilArith.dest_numc (dest_arg t))
    else if is_numc t then
      (Nat_Arith.mk_nat 1, UtilArith.dest_numc t)
    else
      (t, 1)

(* Normalize ct into the form arg * coeff.

   Example: a * 4 == a * 4, a == a * 1, 4 == 1 * 4.
 *)
fun norm_monomial ct =
    let
      val t = Thm.term_of ct
    in
      if is_times t andalso is_numc (dest_arg t) then
        Conv.all_conv ct
      else if is_numc t then
        rewr_obj_eq (obj_sym @{thm mult_1}) ct
      else
        rewr_obj_eq (obj_sym @{thm mult_1_right}) ct
    end

fun compare_monomial (t1, t2) =
    let
      val (arg1, _) = dest_monomial t1
      val (arg2, _) = dest_monomial t2
    in
      if is_one arg1 andalso is_one arg2 then EQUAL
      else if is_one arg1 then GREATER
      else if is_one arg2 then LESS
      else Term_Ord.term_ord (arg1, arg2)
    end

fun combine_monomial ct =
    Conv.every_conv [Conv.binop_conv norm_monomial,
                     rewr_obj_eq (obj_sym distrib_l),
                     Conv.arg_conv nat_fold_conv] ct

fun norm_add_monomial ct =
    let
      val t = Thm.term_of ct
      val (arg1, arg2) = Util.dest_binop_args t
    in
      if is_zero arg1 then rewr_obj_eq add_0 ct
      else if is_zero arg2 then rewr_obj_eq add_0_right ct
      else if is_plus arg1 then
        case compare_monomial (dest_arg arg1, arg2) of
            GREATER => Conv.every_conv [ACUtil.swap_cv plus_ac_info,
                                        Conv.arg1_conv norm_add_monomial] ct
          | EQUAL =>
            if is_numc (dest_arg arg1) andalso is_numc arg2 then
              Conv.every_conv [ACUtil.assoc_cv plus_ac_info,
                               Conv.arg_conv nat_fold_conv] ct
            else
              Conv.every_conv [ACUtil.assoc_cv plus_ac_info,
                               Conv.arg_conv combine_monomial] ct
          | _ => Conv.all_conv ct
      else
        case compare_monomial (arg1, arg2) of
            GREATER => ACUtil.comm_cv plus_ac_info ct
          | EQUAL =>
            if is_numc arg1 andalso is_numc arg2 then
              nat_fold_conv ct
            else
              combine_monomial ct
          | _ => Conv.all_conv ct
    end

fun norm_add_polynomial ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_plus arg2 then
        Conv.every_conv [ACUtil.assoc_sym_cv plus_ac_info,
                         Conv.arg1_conv norm_add_polynomial,
                         norm_add_monomial] ct
      else
        norm_add_monomial ct
    end

fun norm_mult_poly_monomial ct =
    let
      val t = Thm.term_of ct
      val (arg1, _) = Util.dest_binop_args t
    in
      if is_plus arg1 then
        Conv.every_conv [rewr_obj_eq distrib_r,
                         Conv.arg1_conv norm_mult_poly_monomial,
                         Conv.arg_conv norm_mult_monomial,
                         norm_add_polynomial] ct
      else
        norm_mult_monomial ct
    end

fun norm_mult_polynomials ct =
    let
      val t = Thm.term_of ct
      val (_, arg2) = Util.dest_binop_args t
    in
      if is_plus arg2 then
        Conv.every_conv [rewr_obj_eq distrib_l,
                         Conv.arg1_conv norm_mult_polynomials,
                         Conv.arg_conv norm_mult_poly_monomial,
                         norm_add_polynomial] ct
      else
        norm_mult_poly_monomial ct
    end

fun norm_full ct =
    let
      val t = Thm.term_of ct
    in
      if is_plus t then
        Conv.every_conv [Conv.binop_conv norm_full,
                         norm_add_polynomial] ct
      else if is_times t then
        Conv.every_conv [Conv.binop_conv norm_full,
                         norm_mult_polynomials] ct
      else if is_Suc t then
        Conv.every_conv [rewr_obj_eq @{thm Nat.Suc_eq_plus1},
                         norm_full] ct
      else
        Conv.all_conv ct
    end

end;  (* NatRing *)
