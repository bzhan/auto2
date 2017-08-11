(* Normalization for rings *)

signature ALG_COMM_RING =
sig
  type comm_ring_info
  val unit_r: comm_ring_info -> wfconv
  val norm_mult_atom: comm_ring_info -> wfconv
  val norm_mult_monomial: comm_ring_info -> wfconv
  val norm_reduce_unit: comm_ring_info -> wfconv
  val norm_combine_term: comm_ring_info -> wfconv
  val norm_add_monomial: comm_ring_info -> wfconv
  val norm_add_polynomial: comm_ring_info -> wfconv
  val norm_mult_poly_monomial: comm_ring_info -> wfconv
  val norm_mult_polynomials: comm_ring_info -> wfconv
  val norm_full: comm_ring_info -> wfconv
  val comm_ring_alg_data: thm -> comm_ring_info

  type monomial
  val compare_monomial_t: term -> monomial * monomial -> order
  val reduce_atom_list: term -> term list -> term list
  val mult_monomial: term -> monomial * monomial -> monomial
  val reduce_monomial_list: term -> monomial list -> monomial list
  val inv_monomial: term -> monomial -> monomial
  val add_polynomial_list:
      term -> monomial list * monomial list -> monomial list
  val uminus_polynomial_list: monomial list -> monomial list
  val mult_polynomial_list:
      term -> monomial list * monomial list -> monomial list
  val to_monomial: term -> monomial -> term
  val to_polynomial: term -> monomial list -> term
  val inv_polynomial_list: term -> monomial list -> monomial list
  val norm_atom_list: term -> term -> monomial list
  val norm_term: term -> term -> term
  val add_ring_proofsteps: theory -> theory
end;

structure AlgCommRing : ALG_COMM_RING =
struct

type comm_ring_info = {
  G: term,
  rat_info: rat_info,
  plus_assoc_l: wfconv,  (* x + (y + z) = (x + y) + z *)
  plus_assoc_r: wfconv,  (* (x + y) + z = x + (y + z) *)
  plus_comm: wfconv,     (* x + y = y + x *)
  zero_l: wfconv,        (* 0 + x = x *)
  minus: wfconv,         (* x - y = x + -y *)
  times_assoc_l: wfconv, (* x * (y * z) = (x * y) * z *)
  times_assoc_r: wfconv, (* (x * y) * z = x * (y * z) *)
  times_comm: wfconv,    (* x * y = y * x *)
  unit_l: wfconv,        (* 1 * x = x *)
  inv_l: wfconv,         (* inv(x) * x = 1 *)
  inv_inv: wfconv,       (* inv(inv(x)) = x *)
  inv_distrib: wfconv,   (* inv(x * y) = inv(y) * inv(x) *)
  inv_neg: wfconv,       (* inv(-x) = -inv(x) *)
  divide: wfconv,        (* x / y = x * inv(y) *)
  distrib_l: wfconv,     (* x * (y + z) = x * y + x * z *)
  distrib_l': wfconv,    (* x * y + x * z = x * (y + z) *)
  add_mono_l: wfconv,    (* p + p * r = p * (1 + r) *)
  add_mono_same: wfconv, (* p + p = p * 2 *)
  neg_minus_1: wfconv,   (* -p = p * (-1) *)
  mult_zero_l: wfconv,   (* 0 * x = 0 *)
  of_nat_0: wfconv,      (* zero = 0 *)
  of_nat_1: wfconv       (* one = 1 *)
}

fun is_nat_one G t =
    is_of_nat G t andalso dest_of_nat t = 1

fun is_nat_zero G t =
    is_of_nat G t andalso dest_of_nat t = 0

(* (a * b) * c = (a * c) * b. *)
fun swap_times_r info wft =
    let
      val {G, times_assoc_l, times_assoc_r, times_comm, ...} = info
      val (arg1, _) = dest_binop_args (WfTerm.term_of wft)
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
      val (arg1, _) = dest_binop_args (WfTerm.term_of wft)
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

(* a * inv(a) = 1 *)
fun inv_r {times_comm, inv_l, ...} wft =
    WfTerm.every_conv [times_comm, inv_l] wft

(* a * 0 = 0 *)
fun mult_zero_r {times_comm, mult_zero_l, ...} wft =
    WfTerm.every_conv [times_comm, mult_zero_l] wft

(* An atom is either a constant, or of the form a or inv(a). This only
   handles the latter two cases.
 *)
fun dest_atom G t =
    if is_inv G t then dest_arg t else t

(* When comparing atoms, constants are greater than
   non-constants. Non-constants are compared by dest_atom.
 *)
fun compare_atom G (t1, t2) =
    if is_rat G t1 andalso is_rat G t2 then EQUAL
    else if is_rat G t1 then GREATER
    else if is_rat G t2 then LESS
    else Term_Ord.term_ord (dest_atom G t1, dest_atom G t2)

(* Multiply (a_1 * ... * a_n) * a, assume both sides have coefficients
   removed.
 *)
fun norm_mult_atom info wft =
    let
      val {G, rat_info, unit_l, mult_zero_l, times_assoc_r, times_comm,
           inv_l, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_nat_one G arg1 then unit_l wft
      else if is_nat_one G arg2 then unit_r info wft
      else if is_nat_zero G arg1 then mult_zero_l wft
      else if is_nat_zero G arg2 then mult_zero_r info wft
      else if is_times G arg1 then
        case compare_atom G (dest_arg arg1, arg2) of
            GREATER => WfTerm.every_conv [
                        swap_times_r info,
                        WfTerm.arg1_conv (norm_mult_atom info),
                        WfTerm.try_conv unit_l] wft
          | EQUAL =>
            if is_rat G (dest_arg arg1) andalso is_rat G arg2 then
              WfTerm.every_conv [
                times_assoc_r,
                WfTerm.arg_conv (rat_mult rat_info),
                WfTerm.try_conv (unit_r info)] wft
            else if is_inv_pair_l G (dest_arg arg1, arg2) then
              WfTerm.every_conv [
                times_assoc_r, WfTerm.arg_conv inv_l, unit_r info] wft
            else if is_inv_pair_r G (dest_arg arg1, arg2) then
              WfTerm.every_conv [
                times_assoc_r, WfTerm.arg_conv (inv_r info), unit_r info] wft
            else
              WfTerm.all_conv wft
          | LESS => WfTerm.all_conv wft
      else
        case compare_atom G (arg1, arg2) of
            GREATER => times_comm wft
          | EQUAL =>
            if is_inv_pair_l G (arg1, arg2) then inv_l wft
            else if is_inv_pair_r G (arg1, arg2) then inv_r info wft
            else if is_rat G arg1 andalso is_rat G arg2 then
              rat_mult rat_info wft
            else
              WfTerm.all_conv wft
          | LESS => WfTerm.all_conv wft
    end

(* Multiply (a_1 * ... * a_n) * (b_1 * ... * b_n). Assume both sides
   have coefficients removed.
 *)
fun norm_mult_monomial info wft =
    let
      val {G, times_assoc_l, ...} = info
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_times G arg2 then
        WfTerm.every_conv [times_assoc_l,
                           WfTerm.arg1_conv (norm_mult_monomial info),
                           norm_mult_atom info] wft
      else
        norm_mult_atom info wft
    end

(* A monomial monomial may or may not have constants. Return the part
   without constants (the part on the left).
 *)
fun dest_monomial G t =
    if is_times G t andalso is_rat G (dest_arg t)
    then dest_arg1 t else t

fun has_const_monomial G t =
    is_times G t andalso is_rat G (dest_arg t)

(* When comparing atoms, constants are greater than
   non-constants. Non-constants are compared by dest_monomial.
 *)
fun compare_monomial G (t1, t2) =
    if is_rat G t1 andalso is_rat G t2 then EQUAL
    else if is_rat G t1 then GREATER
    else if is_rat G t2 then LESS
    else Term_Ord.term_ord (dest_monomial G t1, dest_monomial G t2)

(* Reduce p * of_nat(1) to p, and p * of_nat(0) to 0. *)
fun norm_reduce_unit info wft =
    let
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
      val r = dest_rat arg2
    in
      if r = rat_one then unit_r info wft
      else if r = rat_zero then mult_zero_r info wft
      else WfTerm.all_conv wft
    end

(* Combine two monomials with same body. *)
fun norm_combine_term info wft =
    let
      val {G, rat_info, plus_comm, distrib_l', add_mono_l,
           add_mono_same, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
      val (b1, b2) = apply2 (has_const_monomial G) (arg1, arg2)
    in
      if b1 andalso b2 then
        WfTerm.every_conv [
          distrib_l', WfTerm.arg_conv (rat_add rat_info),
          norm_reduce_unit info] wft
      else if not b1 andalso b2 then
        WfTerm.every_conv [
          add_mono_l, WfTerm.arg_conv (rat_add rat_info),
          norm_reduce_unit info] wft
      else if b1 andalso not b2 then
        WfTerm.every_conv [
          plus_comm, norm_combine_term info] wft
      else
        add_mono_same wft
    end

(* Add (a_1 + ... + a_n) + a, where a_i and a are monomials. *)
fun norm_add_monomial info wft =
    let
      val {G, rat_info, plus_assoc_r, plus_comm, zero_l, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_nat_zero G arg1 then zero_l wft
      else if is_nat_zero G arg2 then zero_r info wft
      else if is_plus G arg1 then
        case compare_monomial G (dest_arg arg1, arg2) of
            GREATER => WfTerm.every_conv [
                        swap_plus_r info,
                        WfTerm.arg1_conv (norm_add_monomial info),
                        WfTerm.try_conv zero_l] wft
          | EQUAL =>
            if is_rat G (dest_arg arg1) andalso is_rat G arg2 then
              WfTerm.every_conv [
                plus_assoc_r,
                WfTerm.arg_conv (rat_add rat_info),
                WfTerm.try_conv (zero_r info)] wft
            else
              WfTerm.every_conv [
                plus_assoc_r,
                WfTerm.arg_conv (norm_combine_term info),
                WfTerm.try_conv (zero_r info)] wft
          | LESS => WfTerm.all_conv wft
      else
        case compare_monomial G (arg1, arg2) of
            GREATER => plus_comm wft
          | EQUAL =>
            if is_rat G arg1 andalso is_rat G arg2 then
              rat_add rat_info wft
            else
              norm_combine_term info wft
          | LESS => WfTerm.all_conv wft
    end

(* Add (a_1 + ... + a_n) + (b_1 + ... + b_n), where each a_i and b_i
   are monomials.
 *)
fun norm_add_polynomial info wft =
    let
      val {G, plus_assoc_l, ...} = info
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
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
      val (arg1, _) = dest_binop_args (WfTerm.term_of wft)
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
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
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
and norm_full info wft =
    let
      val {G, rat_info, minus, inv_inv, inv_distrib, inv_neg,
           neg_minus_1, divide, of_nat_0, of_nat_1, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_rat G t then
        WfTerm.all_conv wft
      else if is_zero G t then of_nat_0 wft
      else if is_one G t then of_nat_1 wft
      else if is_plus G t then
        WfTerm.every_conv [WfTerm.binop_conv (norm_full info),
                           norm_add_polynomial info] wft
      else if is_times G t then
        WfTerm.every_conv [WfTerm.binop_conv (norm_full info),
                           norm_mult_polynomials info] wft
      else if is_uminus G t then
        WfTerm.every_conv [neg_minus_1, norm_full info] wft
      else if is_minus G t then
        WfTerm.every_conv [minus, norm_full info] wft
      else if is_inv G t then
        if is_rat G (dest_arg t) then
          rat_inv rat_info wft
        else if is_inv G (dest_arg t) then
          WfTerm.every_conv [inv_inv, norm_full info] wft
        else if is_times G (dest_arg t) then
          WfTerm.every_conv [
            inv_distrib,
            WfTerm.binop_conv (norm_full info),
            norm_mult_polynomials info] wft
        else if is_uminus G (dest_arg t) then
          WfTerm.every_conv [inv_neg, norm_full info] wft
        else
          WfTerm.all_conv wft
      else if is_divide G t then
        WfTerm.every_conv [divide, norm_full info] wft
      else
        WfTerm.all_conv wft
    end

fun comm_ring_alg_data c_ring_th =
    let
      val _ = assert (
            is_Trueprop (Thm.prop_of c_ring_th) andalso
            Term.head_of (prop_of' c_ring_th) aconv @{term is_comm_ring})
                     "comm_ring_alg_data"
      val G = dest_arg (prop_of' c_ring_th)
      val fheads = rat_fheads G
      fun rewr th = WfTerm.rewr_obj_eq fheads th
      val ring_th = c_ring_th RS @{thm is_comm_ringD(1)}
      val times_comm_th = c_ring_th RS @{thm is_comm_ringD(2)}
      val abgroup_th = ring_th RS @{thm is_ringD(2)}
      val ab_monoid_th = abgroup_th RS @{thm is_abgroupD(1)}
      val monoid_th = ring_th RS @{thm is_ringD(3)}
      val distrib_l_th = ring_th RS @{thm is_ringD(4)}
      val plus_comm_th = ab_monoid_th RS @{thm is_ab_monoidD(3)}
      val plus_assoc_th = ab_monoid_th RS @{thm is_ab_monoidD(4)}
      val times_assoc_th = monoid_th RS @{thm is_monoidD(2)}
    in
      {G = G,
       rat_info = comm_ring_rat_info c_ring_th,
       plus_assoc_l  = rewr (plus_assoc_th  RS @{thm plus_assoc_left}),
       plus_assoc_r  = rewr (plus_assoc_th  RS @{thm plus_assoc_right}),
       plus_comm     = rewr (plus_comm_th   RS @{thm plus_commD}),
       zero_l        = rewr (ring_th        RS @{thm zero_l'}),
       minus         = rewr (abgroup_th     RS @{thm minusD}),
       times_assoc_l = rewr (times_assoc_th RS @{thm times_assoc_left}),
       times_assoc_r = rewr (times_assoc_th RS @{thm times_assoc_right}),
       times_comm    = rewr (times_comm_th  RS @{thm times_commD}),
       unit_l        = rewr (ring_th        RS @{thm unit_l'}),
       inv_l         = rewr (ring_th        RS @{thm inv_l'}),
       inv_inv       = rewr (monoid_th      RS @{thm unit_inv_inv}),
       inv_distrib   = rewr (c_ring_th      RS @{thm inv_distrib_comm_ring}),
       inv_neg       = rewr (c_ring_th      RS @{thm inv_neg}),
       divide        = rewr (c_ring_th      RS @{thm divideD}),
       distrib_l     = rewr (distrib_l_th   RS @{thm left_distribD}),
       distrib_l'    = rewr (distrib_l_th   RS @{thm left_distribD_back}),
       add_mono_l    = rewr (ring_th        RS @{thm add_monomial_l}),
       add_mono_same = rewr (ring_th        RS @{thm add_monomial_same}),
       neg_minus_1   = rewr (ring_th        RS @{thm neg_is_minus_1}),
       mult_zero_l   = rewr (ring_th        RS @{thm mult_zero_l'}),
       of_nat_0      = rewr (ring_th        RS @{thm of_nat_zero'}),
       of_nat_1      = rewr (ring_th        RS @{thm of_nat_one'})}
    end

(* Term simplification on rings: represent as a list of (l, c), where
   c is the coefficient, and l is the list of factors of a
   monomial. An additive constant a is represented by ([], a).
 *)

type monomial = term list * Rat.rat

(* Compare two monomials, written to agree with the convention for the
   actual simplification.
 *)
fun compare_monomial_t G ((l1, _), (l2, _)) =
    if null l1 andalso null l2 then EQUAL
    else if null l1 then GREATER
    else if null l2 then LESS
    else Term_Ord.term_ord (list_times G l1, list_times G l2)

(* Reducing a monomial: combine a with inv(a). *)
fun reduce_atom_list G l =
    if null l then []
    else let
      val (head, rest) = (hd l, reduce_atom_list G (tl l))
    in
      if null rest then [head]
      else if is_inv_pair_l G (head, hd rest) orelse
              is_inv_pair_r G (head, hd rest) then tl rest
      else head :: rest
    end

(* Multiply two monomials. *)
fun mult_monomial G ((l1, c1), (l2, c2)) =
    ((l1 @ l2) |> sort (compare_atom G) |> reduce_atom_list G, Rat.mult c1 c2)

(* Reduce a list of monomials: combine monomials of the same body. *)
fun reduce_monomial_list G ls =
    if null ls then []
    else let
      val (head, rest) = (hd ls, reduce_monomial_list G (tl ls))
    in
      if null rest then [head]
      else let
        val (l1, c1) = head
        val (l2, c2) = hd rest
      in
        if list_times G l1 aconv list_times G l2 then
          if Rat.add c1 c2 = rat_zero then tl rest
          else (l1, Rat.add c1 c2) :: tl rest
        else head :: rest
      end
    end

fun inv_monomial G (l, c) =
    let
      val _ = assert (c <> rat_zero) "inv_monomial"
      fun inv_atom atom =
          if is_inv G atom then dest_arg atom else inv_t $ G $ atom
    in
      (map inv_atom l, Rat.inv c)
    end

(* Add two lists of (l, c). *)
fun add_polynomial_list G (ls1, ls2) =
    (ls1 @ ls2) |> sort (compare_monomial_t G) |> reduce_monomial_list G

(* Additive inverse of a list of (l, c). *)
fun uminus_polynomial_list ls =
    map (fn (l, c) => (l, Rat.neg c)) ls

(* Multiply two lists of (l, c). *)
fun mult_polynomial_list G (ls1, ls2) =
    (all_pairs (ls1, ls2))
        |> map (fn (l1, l2) => mult_monomial G (l1, l2))
        |> sort (compare_monomial_t G)
        |> reduce_monomial_list G

(* Translate (l, c) to a monomial. *)
fun to_monomial G (l, c) =
    if null l then mk_rat G c
    else if c = rat_one then list_times G l
    else times_t $ G $ list_times G l $ mk_rat G c

(* Translate a list of (l, c) to a polynomial. *)
fun to_polynomial G ls =
    if null ls then mk_rat G rat_zero
    else list_plus G (map (to_monomial G) ls)

fun inv_polynomial_list G ls =
    case ls of
        [] => (* divide by zero *) [([inv_t $ G $ zero_t], rat_one)]
      | [(l, c)] => [inv_monomial G (l, c)]
      | _ => [([inv_t $ G $ to_polynomial G ls], rat_one)]

fun norm_atom_list G t =
    if is_plus G t then
      add_polynomial_list G (norm_atom_list G (dest_arg1 t),
                             norm_atom_list G (dest_arg t))
    else if is_uminus G t then
      uminus_polynomial_list (norm_atom_list G (dest_arg t))
    else if is_minus G t then
      add_polynomial_list G (
        norm_atom_list G (dest_arg1 t),
        uminus_polynomial_list (norm_atom_list G (dest_arg t)))
    else if is_times G t then
      mult_polynomial_list G (norm_atom_list G (dest_arg1 t),
                              norm_atom_list G (dest_arg t))
    else if is_inv G t then
      inv_polynomial_list G (norm_atom_list G (dest_arg t))
    else if is_divide G t then
      mult_polynomial_list G (
        norm_atom_list G (dest_arg1 t),
        inv_polynomial_list G (norm_atom_list G (dest_arg t)))
    else if is_zero G t then []
    else if is_one G t then [([], rat_one)]
    else if is_rat G t then
      if dest_rat t = rat_zero then [] else [([], dest_rat t)]
    else [([t], rat_one)]

fun norm_term G t =
    to_polynomial G (norm_atom_list G t)

val comm_ring_norm_info = {
  op_heads = rat_opheads, pred_t = @{term is_comm_ring},
  norm_t = norm_term, excl_norm_t = [AlgMonoid.norm_term, AlgAbGroup.norm_term],
  norm_wfcv = norm_full o comm_ring_alg_data}

val add_ring_proofsteps =
    fold add_prfstep [
      FOLAlgUtil.alg_norm1_prfstep comm_ring_norm_info,
      FOLAlgUtil.alg_norm2_prfstep comm_ring_norm_info
    ]

end  (* structure AlgCommRing *)

val _ = Theory.setup (AlgCommRing.add_ring_proofsteps)
