(* Normalization for abelian groups *)

val zero_t = @{term zero}
val plus_t = @{term plus}
val plus_ct = @{cterm plus}
val uminus_t = @{term neg}
val uminus_ct = @{cterm neg}
val minus_t = @{term minus}
val minus_ct = @{cterm minus}

fun is_zero G t = t aconv (zero_t $ G)
fun is_plus G t = is_head (plus_t $ G) t
fun is_uminus G t = is_head (uminus_t $ G) t
fun is_uminus_pair_l G (t1, t2) = (t1 aconv uminus_t $ G $ t2)
fun is_uminus_pair_r G (t1, t2) = (t2 aconv uminus_t $ G $ t1)
fun is_minus G t = is_head (minus_t $ G) t

fun list_plus G ts =
    let
      fun list_rev ts =
          case ts of
              [] => zero_t $ G
            | [t] => t
            | t :: ts' => plus_t $ G $ list_rev ts' $ t
    in
      list_rev (rev ts)
    end

signature ALG_ABGROUP =
sig
  type abgroup_info
  val abgroup_add_atom: abgroup_info -> wfconv
  val abgroup_add_monomial: abgroup_info -> wfconv
  val normalize_abgroup: abgroup_info -> wfconv
  val abgroup_alg_data: thm -> abgroup_info

  val reduce_atom_list: term -> term list -> term list
  val add_atom_list: term -> term list * term list -> term list
  val norm_atom_list: term -> term -> term list
  val norm_term: term -> term -> term
  val add_abgroup_proofsteps: theory -> theory
end;

structure AlgAbGroup : ALG_ABGROUP =
struct

type abgroup_info = {
  G: term,
  assoc_l: wfconv,     (* x + (y + z) = (x + y) + z *)
  assoc_r: wfconv,     (* (x + y) + z = x + (y + z) *)
  comm: wfconv,        (* x + y = y + x *)
  zero_l: wfconv,      (* 0 + x = x *)
  neg_zero: wfconv,    (* -0 = 0 *)
  neg_l: wfconv,       (* -x + x = 0 *)
  neg_neg: wfconv,     (* -(-x) = 0 *)
  neg_distrib: wfconv, (* -(x + y) = -x + -y *)
  minus: wfconv        (* x - y = x + -y *)
}

(* (a + b) + c = (a + c) + b. *)
fun swap_plus_r_cv {G, assoc_l, assoc_r, comm, ...} wft =
    let
      val (arg1, _) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg1 then
        WfTerm.every_conv [assoc_r, WfTerm.arg_conv comm, assoc_l] wft
      else
        comm wft
    end

(* a + 0 = a *)
fun zero_r {comm, zero_l, ...} wft =
    WfTerm.every_conv [comm, zero_l] wft

(* a + -a = 0 *)
fun neg_r {comm, neg_l, ...} wft =
    WfTerm.every_conv [comm, neg_l] wft

fun dest_atom G t =
    if is_uminus G t then dest_arg t else t

fun compare_atom G (t1, t2) =
    Term_Ord.term_ord (dest_atom G t1, dest_atom G t2)

(* Add (a_1 + ... + a_n) + a, where a_i and a are atoms. *)
fun abgroup_add_atom info wft =
    let
      val {G, assoc_r, comm, zero_l, neg_l, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_zero G arg1 then zero_l wft
      else if is_zero G arg2 then zero_r info wft
      else if is_plus G arg1 then
        case compare_atom G (dest_arg arg1, arg2) of
            GREATER => WfTerm.every_conv [
                        swap_plus_r_cv info,
                        WfTerm.arg1_conv (abgroup_add_atom info),
                        WfTerm.try_conv zero_l] wft
          | EQUAL =>
            if is_uminus_pair_l G (dest_arg arg1, arg2) then
              WfTerm.every_conv [
                assoc_r, WfTerm.arg_conv neg_l, zero_r info] wft
            else if is_uminus_pair_r G (dest_arg arg1, arg2) then
              WfTerm.every_conv [
                assoc_r, WfTerm.arg_conv (neg_r info), zero_r info] wft
            else
              WfTerm.all_conv wft
          | LESS => WfTerm.all_conv wft
      else
        case compare_atom G (arg1, arg2) of
            GREATER => comm wft
          | EQUAL =>
            if is_uminus_pair_l G (arg1, arg2) then neg_l wft
            else if is_uminus_pair_r G (arg1, arg2) then neg_r info wft
            else WfTerm.all_conv wft
          | LESS => WfTerm.all_conv wft
    end

(* Add (a_1 + ... + a_n) + (b_1 + ... + b_n) *)
fun abgroup_add_monomial info wft =
    let
      val {G, assoc_l, ...} = info
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_plus G arg2 then
        WfTerm.every_conv [
          assoc_l,
          WfTerm.arg1_conv (abgroup_add_monomial info),
          abgroup_add_atom info] wft
      else
        abgroup_add_atom info wft
    end

fun normalize_abgroup info wft =
    let
      val {G, neg_zero, neg_neg, neg_distrib, minus, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_plus G t then
        WfTerm.every_conv [
          WfTerm.binop_conv (normalize_abgroup info),
          abgroup_add_monomial info] wft
      else if is_uminus G t then
        if is_zero G (dest_arg t) then
          neg_zero wft
        else if is_uminus G (dest_arg t) then
          WfTerm.every_conv [neg_neg, normalize_abgroup info] wft
        else if is_plus G (dest_arg t) then
          WfTerm.every_conv [neg_distrib, normalize_abgroup info] wft
        else if is_minus G (dest_arg t) then
          WfTerm.every_conv [WfTerm.arg_conv minus, neg_distrib,
                             normalize_abgroup info] wft
        else
          WfTerm.all_conv wft
      else if is_minus G t then
        WfTerm.every_conv [minus, normalize_abgroup info] wft
      else
        WfTerm.all_conv wft
    end

fun abgroup_alg_data abgroup_th =
    let
      val _ =
          assert (is_Trueprop (Thm.prop_of abgroup_th) andalso
                  Term.head_of (prop_of' abgroup_th) aconv @{term is_abgroup})
                 "abgroup_alg_data"
      val G = dest_arg (prop_of' abgroup_th)
      val fheads = [plus_t $ G, uminus_t $ G, minus_t $ G]
      val rewr = WfTerm.rewr_obj_eq fheads
      val ab_monoid_th = abgroup_th RS @{thm is_abgroupD(1)}
      val add_id_th = ab_monoid_th RS @{thm is_ab_monoidD(2)}
      val plus_comm_th = ab_monoid_th RS @{thm is_ab_monoidD(3)}
      val plus_assoc_th = ab_monoid_th RS @{thm is_ab_monoidD(4)}
    in
      {G = G,
       assoc_l     = rewr (plus_assoc_th RS @{thm plus_assoc_left}),
       assoc_r     = rewr (plus_assoc_th RS @{thm plus_assoc_right}),
       comm        = rewr (plus_comm_th  RS @{thm plus_commD}),
       zero_l      = rewr (add_id_th     RS @{thm is_add_idD}),
       neg_zero    = rewr (abgroup_th    RS @{thm abgroup_neg_zero}),
       neg_l       = rewr (abgroup_th    RS @{thm abgroup_neg_left}),
       neg_neg     = rewr (abgroup_th    RS @{thm abgroup_neg_neg}),
       neg_distrib = rewr (abgroup_th    RS @{thm abgroup_neg_distrib}),
       minus       = rewr (abgroup_th    RS @{thm minusD})}
    end

(* For simplification on terms, we represent a sum of terms as a list. *)

(* Reduce a sorted list of terms *)
fun reduce_atom_list G l =
    if null l then []
    else let
      val (head, rest) = (hd l, reduce_atom_list G (tl l))
    in
      if null rest then [head]
      else if is_uminus_pair_l G (head, hd rest) orelse
              is_uminus_pair_r G (head, hd rest) then tl rest
      else head :: rest
    end

(* Add two lists of terms. Assume the lists themselves are reduced. *)
fun add_atom_list G (l1, l2) =
    (l1 @ l2) |> sort (compare_atom G) |> reduce_atom_list G

(* Compute the uminus of a list. Assume the list is reduced. *)
fun uminus_atom_list G l =
    let
      fun uminus_atom atom =
          if is_uminus G atom then dest_arg atom else uminus_t $ G $ atom
    in
      map uminus_atom l
    end

(* Normalization of a term as a sum of terms. *)
fun norm_atom_list G t =
    if is_plus G t then
      add_atom_list G (norm_atom_list G (dest_arg1 t),
                       norm_atom_list G (dest_arg t))
    else if is_uminus G t then
      uminus_atom_list G (norm_atom_list G (dest_arg t))
    else if is_minus G t then
      add_atom_list G (norm_atom_list G (dest_arg1 t),
                       uminus_atom_list G (norm_atom_list G (dest_arg t)))
    else if is_zero G t then []
    else [t]

fun norm_term G t =
    list_plus G (norm_atom_list G t)

val abgroup_norm_info = {
  op_heads = [plus_t, minus_t, uminus_t], pred_t = @{term is_abgroup},
  norm_t = norm_term, excl_norm_t = [],
  norm_wfcv = normalize_abgroup o abgroup_alg_data}

val add_abgroup_proofsteps =
    fold add_prfstep [
      FOLAlgUtil.alg_norm1_prfstep abgroup_norm_info,
      FOLAlgUtil.alg_norm2_prfstep abgroup_norm_info
    ]

end  (* structure AlgAbGroup *)

val _ = Theory.setup (AlgAbGroup.add_abgroup_proofsteps)
