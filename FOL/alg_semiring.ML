(* Normalization for semirings *)

signature ALG_SEMIRING =
sig
  type semiring_info
  val norm_mult_atom: semiring_info -> wfconv
  val norm_mult_monomial: semiring_info -> wfconv
  val norm_add_monomial: semiring_info -> wfconv
  val norm_add_polynomial: semiring_info -> wfconv
  val norm_mult_poly_monomial: semiring_info -> wfconv
  val norm_mult_polynomials: semiring_info -> wfconv
  val norm_full: semiring_info -> wfconv
  val semiring_alg_data: thm -> semiring_info

  val compare_monomial: term -> term list * term list -> order
  val mult_polynomial_term:
      term -> term list list * term list list -> term list list
  val norm_atom_list: term -> term -> term list list
  val norm_term: term -> term -> term
  val add_semiring_proofsteps: theory -> theory
end;

structure AlgSemiring : ALG_SEMIRING =
struct

type semiring_info = {
  G: term,
  plus_assoc_l: wfconv,  (* x + (y + z) = (x + y) + z *)
  plus_assoc_r: wfconv,  (* (x + y) + z = x + (y + z) *)
  plus_comm: wfconv,     (* x + y = y + x *)
  zero_l: wfconv,        (* 0 + x = x *)
  times_assoc_l: wfconv, (* x * (y * z) = (x * y) * z *)
  times_assoc_r: wfconv, (* (x * y) * z = x * (y * z) *)
  times_comm: wfconv,    (* x * y = y * x *)
  unit_l: wfconv,        (* 1 * x = x *)
  distrib_l: wfconv,     (* x * (y + z) = x * y + x * z *)
  mult_zero_l: wfconv    (* 0 * x = 0 *)
}

(* (a * b) * c = (a * c) * b. *)
fun swap_times_r info wft =
    let
      val {G, times_assoc_l, times_assoc_r, times_comm, ...} = info
      val (arg1, _) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_times G arg1 then
        WfTerm.every_conv [times_assoc_r, WfTerm.arg_conv times_comm,
                           times_assoc_l] wft
      else
        times_comm wft
    end

(* (a + b) + c = (a + c) + b. *)
fun swap_plus_r info wft =
    let
      val {G, plus_assoc_l, plus_assoc_r, plus_comm, ...} = info
      val (arg1, _) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg1 then
        WfTerm.every_conv [plus_assoc_r, WfTerm.arg_conv plus_comm,
                           plus_assoc_l] wft
      else
        plus_comm wft
    end

(* (a + b) * c = a * c + b * c. *)
fun distrib_r {times_comm, distrib_l, ...} wft =
    WfTerm.every_conv [times_comm, distrib_l, WfTerm.arg1_conv times_comm,
                       WfTerm.arg_conv times_comm] wft

(* a + 0 = a *)
fun zero_r {plus_comm, zero_l, ...} wft =
    WfTerm.every_conv [plus_comm, zero_l] wft

(* a * 1 = a *)
fun unit_r {times_comm, unit_l, ...} wft =
    WfTerm.every_conv [times_comm, unit_l] wft

(* a * 0 = 0 *)
fun mult_zero_r {times_comm, mult_zero_l, ...} wft =
    WfTerm.every_conv [times_comm, mult_zero_l] wft

fun compare_atom (t1, t2) =
    Term_Ord.term_ord (t1, t2)

(* Multiply (a_1 * ... * a_n) * a. *)
fun norm_mult_atom info wft =
    let
      val {G, unit_l, mult_zero_l, times_comm, ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_one G arg1 then unit_l wft
      else if is_one G arg2 then unit_r info wft
      else if is_zero G arg1 then mult_zero_l wft
      else if is_zero G arg2 then mult_zero_r info wft
      else if is_times G arg1 then
        case compare_atom (dest_arg arg1, arg2) of
            GREATER => WfTerm.every_conv [
                        swap_times_r info,
                        WfTerm.arg1_conv (norm_mult_atom info)] wft
          | _ => WfTerm.all_conv wft
      else
        case compare_atom (arg1, arg2) of
            GREATER => times_comm wft
          | _ => WfTerm.all_conv wft
    end

(* Multiply (a_1 * ... * a_n) * (b_1 * ... * b_n). *)
fun norm_mult_monomial info wft =
    let
      val {G, times_assoc_l, ...} = info
      val (_, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_times G arg2 then
        WfTerm.every_conv [times_assoc_l,
                           WfTerm.arg1_conv (norm_mult_monomial info),
                           norm_mult_atom info] wft
      else
        norm_mult_atom info wft
    end

(* Add (a_1 + ... + a_n) + a, where a_i and a are monomials. *)
fun norm_add_monomial info wft =
    let
      val {G, plus_comm, zero_l, ...} = info
      val (arg1, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_zero G arg1 then zero_l wft
      else if is_zero G arg2 then zero_r info wft
      else if is_plus G arg1 then
        case compare_atom (dest_arg arg1, arg2) of
            GREATER => WfTerm.every_conv [
                        swap_plus_r info,
                        WfTerm.arg1_conv (norm_add_monomial info)] wft
          | _ => WfTerm.all_conv wft
      else
        case compare_atom (arg1, arg2) of
            GREATER => plus_comm wft
          | _ => WfTerm.all_conv wft
    end

(* Add (a_1 + ... + a_n) + (b_1 + ... + b_n), where each a_i and b_i
   are monomials.
 *)
fun norm_add_polynomial info wft =
    let
      val {G, plus_assoc_l, ...} = info
      val (_, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg2 then
        WfTerm.every_conv [plus_assoc_l,
                           WfTerm.arg1_conv (norm_add_polynomial info),
                           norm_add_monomial info] wft
      else
        norm_add_monomial info wft
    end

fun norm_mult_poly_monomial info wft =
    let
      val {G, ...} = info
      val (arg1, _) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg1 then
        WfTerm.every_conv [distrib_r info,
                           WfTerm.arg1_conv (norm_mult_poly_monomial info),
                           WfTerm.arg_conv (norm_mult_monomial info),
                           norm_add_polynomial info] wft
      else
        norm_mult_monomial info wft
    end

fun norm_mult_polynomials info wft =
    let
      val {G, distrib_l, ...} = info
      val (_, arg2) = Util.dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg2 then
        WfTerm.every_conv [distrib_l,
                           WfTerm.arg1_conv (norm_mult_polynomials info),
                           WfTerm.arg_conv (norm_mult_poly_monomial info),
                           norm_add_polynomial info] wft
      else
        norm_mult_poly_monomial info wft
    end

(* Full normalization procedure. *)
fun norm_full info wft =
    let
      val {G, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_plus G t then
        WfTerm.every_conv [WfTerm.binop_conv (norm_full info),
                           norm_add_polynomial info] wft
      else if is_times G t then
        WfTerm.every_conv [WfTerm.binop_conv (norm_full info),
                           norm_mult_polynomials info] wft
      else
        WfTerm.all_conv wft
    end

fun semiring_alg_data s_ring_th =
    let
      val _ =
          assert (is_Trueprop (Thm.prop_of s_ring_th) andalso
                  Term.head_of (prop_of' s_ring_th) aconv @{term is_semiring})
                 "semiring_alg_data"
      val G = dest_arg (prop_of' s_ring_th)
      val fheads = [plus_t $ G, uminus_t $ G, times_t $ G]
      fun rewr th = WfTerm.rewr_obj_eq fheads th
      val ab_monoid_th = s_ring_th RS @{thm is_semiringD(2)}
      val monoid_th = s_ring_th RS @{thm is_semiringD(3)}
      val times_comm_th = s_ring_th RS @{thm is_semiringD(4)}
      val distrib_l_th = s_ring_th RS @{thm is_semiringD(5)}
      val mult0_l_th = s_ring_th RS @{thm is_semiringD(6)}
      val add_id_th = ab_monoid_th RS @{thm is_ab_monoidD(2)}
      val plus_comm_th = ab_monoid_th RS @{thm is_ab_monoidD(3)}
      val plus_assoc_th = ab_monoid_th RS @{thm is_ab_monoidD(4)}
      val times_unit_th = monoid_th RS @{thm is_monoidD(1)}
      val times_assoc_th = monoid_th RS @{thm is_monoidD(2)}
    in
      {G = G,
       plus_assoc_l  = rewr (plus_assoc_th  RS @{thm plus_assoc_left}),
       plus_assoc_r  = rewr (plus_assoc_th  RS @{thm plus_assoc_right}),
       plus_comm     = rewr (plus_comm_th   RS @{thm plus_commD}),
       zero_l        = rewr (add_id_th      RS @{thm is_add_idD}),
       times_assoc_l = rewr (times_assoc_th RS @{thm times_assoc_left}),
       times_assoc_r = rewr (times_assoc_th RS @{thm times_assoc_right}),
       times_comm    = rewr (times_comm_th  RS @{thm times_commD}),
       unit_l        = rewr (times_unit_th  RS @{thm is_mult_id_left}),
       distrib_l     = rewr (distrib_l_th   RS @{thm left_distribD}),
       mult_zero_l   = rewr (mult0_l_th     RS @{thm is_zero_multD(1)})}
    end

(* Term simplification on semirings: represent as a list of lists,
   where each list represent a monomial.
 *)

(* Compare two monomials: following the convention in the actual
   simplification, form the monomial, then compare.
 *)
fun compare_monomial G (ls1, ls2) =
    Term_Ord.term_ord (list_times G ls1, list_times G ls2)

(* Multiply two such lists: take the pairwise product, sort within
   each monomial, then sort the list of monomials.
 *)
fun mult_polynomial_term G (ls1, ls2) =
    (Util.all_pairs (ls1, ls2))
        |> map (fn (l1, l2) => sort Term_Ord.term_ord (l1 @ l2))
        |> sort (compare_monomial G)

fun norm_atom_list G t =
    if is_plus G t then
      sort (compare_monomial G)
           (norm_atom_list G (dest_arg1 t) @ norm_atom_list G (dest_arg t))
    else if is_times G t then
      mult_polynomial_term G (norm_atom_list G (dest_arg1 t),
                              norm_atom_list G (dest_arg t))
    else if is_zero G t then []
    else if is_one G t then [[]]
    else [[t]]

fun norm_term G t =
    let
      val ls = norm_atom_list G t
    in
      list_plus G (map (list_times G) ls)
    end

val semiring_norm_info = {
  op_heads = [plus_t, times_t], pred_t = @{term is_semiring},
  norm_t = norm_term, excl_norm_t = [AlgMonoid.norm_term],
  norm_wfcv = norm_full o semiring_alg_data}

val add_semiring_proofsteps =
    fold add_prfstep [
      FOLAlgUtil.alg_norm1_prfstep semiring_norm_info,
      FOLAlgUtil.alg_norm2_prfstep semiring_norm_info
    ]

end  (* structure AlgSemiring *)

val _ = Theory.setup (AlgSemiring.add_semiring_proofsteps)
