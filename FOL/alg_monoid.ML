(* Normalization for monoids. *)

val one_t = @{term one}
val times_t = @{term times}
val times_ct = @{cterm times}

fun is_one G t = t aconv (one_t $ G)
fun is_times G t = is_head (times_t $ G) t

fun list_times G ts =
    let
      fun list_rev ts =
          case ts of
              [] => one_t $ G
            | [t] => t
            | t :: ts' => times_t $ G $ list_rev ts' $ t
    in
      list_rev (rev ts)
    end

signature ALG_MONOID =
sig
  type monoid_info
  val monoid_mult_atom: monoid_info -> wfconv
  val monoid_mult_monomial: monoid_info -> wfconv
  val normalize_monoid: monoid_info -> wfconv
  val monoid_alg_data: thm -> monoid_info

  val norm_atom_list: term -> term -> term list
  val norm_term: term -> term -> term
  val add_monoid_proofsteps: theory -> theory
end;

structure AlgMonoid : ALG_MONOID =
struct

type monoid_info = {G: term, assoc_l: wfconv, unit_l: wfconv, unit_r: wfconv}

fun monoid_mult_atom info wft =
    let
      val {G, unit_l, unit_r, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_one G arg1 then unit_l wft
      else if is_one G arg2 then unit_r wft
      else WfTerm.all_conv wft
    end

fun monoid_mult_monomial info wft =
    let
      val {G, assoc_l, ...} = info
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_times G arg2 then
        WfTerm.every_conv [
          assoc_l,
          WfTerm.arg1_conv (monoid_mult_monomial info),
          monoid_mult_atom info] wft
      else
        monoid_mult_atom info wft
    end

fun normalize_monoid info wft =
    let
      val {G, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_times G t then
        WfTerm.every_conv [
          WfTerm.binop_conv (normalize_monoid info),
          monoid_mult_monomial info] wft
      else
        WfTerm.all_conv wft
    end

fun monoid_alg_data th =
    let
      val _ = assert (is_Trueprop (Thm.prop_of th) andalso
                      Term.head_of (prop_of' th) aconv @{term is_monoid})
                     "monoid_alg_data"
      val G = dest_arg (prop_of' th)
      val fheads = [times_t $ G]
      val assoc_l_th = th RS @{thm is_monoidD(2)} RS @{thm times_assoc_left}
      val unit_l_th = th RS @{thm is_monoidD(1)} RS @{thm is_mult_id_left}
      val unit_r_th = th RS @{thm is_monoidD(1)} RS @{thm is_mult_id_right}
      val rewr = WfTerm.rewr_obj_eq fheads
    in
      {G = G, assoc_l = rewr assoc_l_th,
       unit_l = rewr unit_l_th, unit_r = rewr unit_r_th}
    end

(* For simplification on terms, we represent a product of terms as a list. *)

fun norm_atom_list G t =
    if is_times G t then
      norm_atom_list G (dest_arg1 t) @ norm_atom_list G (dest_arg t)
    else if is_one G t then []
    else [t]

fun norm_term G t =
    list_times G (norm_atom_list G t)

val monoid_norm_info = {
  op_heads = [times_t], pred_t = @{term is_monoid}, norm_t = norm_term,
  excl_norm_t = [], norm_wfcv = normalize_monoid o monoid_alg_data}

val add_monoid_proofsteps =
    fold add_prfstep [
      FOLAlgUtil.alg_norm1_prfstep monoid_norm_info,
      FOLAlgUtil.alg_norm2_prfstep monoid_norm_info
    ]

end  (* structure AlgMonoid. *)

val _ = Theory.setup (AlgMonoid.add_monoid_proofsteps)
