(* Normalization for groups *)

val inv_t = @{term inv}

fun is_inv G t = is_head (inv_t $ G) t
fun is_inv_pair_l G (t1, t2) = (t1 aconv inv_t $ G $ t2)
fun is_inv_pair_r G (t1, t2) = (t2 aconv inv_t $ G $ t1)

signature ALG_GROUP =
sig
  type group_info
  val group_mult_atom: group_info -> wfconv
  val group_mult_monomial: group_info -> wfconv
  val normalize_group: group_info -> wfconv
  val group_alg_data: thm -> (term list * wfconv) option

  val reduce_atom_list: term -> term list -> term list
  val mult_atom_list: term -> term list * term list -> term list
  val inv_atom_list: term -> term list -> term list
  val norm_atom_list: term -> term -> term list
  val norm_term: term -> term -> term
  val add_group_proofsteps: theory -> theory
end;

structure AlgGroup : ALG_GROUP =
struct

type group_info = {
  G: term,
  assoc_l: wfconv,    (* x * (y * z) = (x * y) * z *)
  assoc_r: wfconv,    (* (x * y) * z = x * (y * z) *)
  unit_l: wfconv,     (* 1 * x = x *)
  unit_r: wfconv,     (* x * 1 = x *)
  inv_unit: wfconv,   (* inv(1) = 1 *)
  inv_l: wfconv,      (* inv(x) * x = 1 *)
  inv_r: wfconv,      (* x * inv(x) = 1 *)
  inv_inv: wfconv,    (* inv(inv(x)) = x *)
  inv_distrib: wfconv (* inv(x * y) = inv(y) * inv(x) *)
}

fun group_mult_atom info wft =
    let
      val {G, assoc_r, unit_l, unit_r, inv_l, inv_r, ...} = info
      val (arg1, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_one G arg1 then unit_l wft
      else if is_one G arg2 then unit_r wft
      else if is_times G arg1 then
        if is_inv_pair_l G (dest_arg arg1, arg2) then
          WfTerm.every_conv [assoc_r, WfTerm.arg_conv inv_l, unit_r] wft
        else if is_inv_pair_r G (dest_arg arg1, arg2) then
          WfTerm.every_conv [assoc_r, WfTerm.arg_conv inv_r, unit_r] wft
        else
          WfTerm.all_conv wft
      else
        if is_inv_pair_l G (arg1, arg2) then inv_l wft
        else if is_inv_pair_r G (arg1, arg2) then inv_r wft
        else WfTerm.all_conv wft
    end

fun group_mult_monomial info wft =
    let
      val {G, assoc_l, ...} = info
      val (_, arg2) = dest_binop_args (WfTerm.term_of wft)
    in
      if is_times G arg2 then
        WfTerm.every_conv [
          assoc_l,
          WfTerm.arg1_conv (group_mult_monomial info),
          group_mult_atom info] wft
      else
        group_mult_atom info wft
    end

fun normalize_group info wft =
    let
      val {G, inv_unit, inv_distrib, inv_inv, ...} = info
      val t = WfTerm.term_of wft
    in
      if is_times G t then
        WfTerm.every_conv [
          WfTerm.binop_conv (normalize_group info),
          group_mult_monomial info] wft
      else if is_inv G t then
        if is_one G (dest_arg t) then
          inv_unit wft
        else if is_inv G (dest_arg t) then
          WfTerm.every_conv [inv_inv, normalize_group info] wft
        else if is_times G (dest_arg t) then
          WfTerm.every_conv [
            inv_distrib,
            WfTerm.binop_conv (normalize_group info),
            group_mult_monomial info] wft
        else
          WfTerm.all_conv wft
      else
        WfTerm.all_conv wft
    end

fun group_alg_data group_th =
    if not (is_Trueprop (Thm.prop_of group_th)) then NONE
    else if not (Term.head_of (prop_of' group_th) aconv @{term is_group})
    then NONE
    else let
      val G = dest_arg (prop_of' group_th)
      val fheads = [times_t $ G, inv_t $ G]
      fun rewr th = WfTerm.rewr_obj_eq fheads th
      val monoid_th = group_th RS @{thm is_groupD(1)}
      val times_assoc_th = monoid_th RS @{thm is_monoidD(2)}
      val times_unit_th = monoid_th RS @{thm is_monoidD(1)}
      val info = {
        G = G,
        assoc_l     = rewr (times_assoc_th RS @{thm times_assoc_left}),
        assoc_r     = rewr (times_assoc_th RS @{thm times_assoc_right}),
        unit_l      = rewr (times_unit_th  RS @{thm is_mult_id_left}),
        unit_r      = rewr (times_unit_th  RS @{thm is_mult_id_right}),
        inv_unit    = rewr (monoid_th      RS @{thm invD(1)}),
        inv_l       = rewr (monoid_th      RS @{thm invD(2)}),
        inv_r       = rewr (monoid_th      RS @{thm invD(3)}),
        inv_inv     = rewr (monoid_th      RS @{thm unit_inv_inv}),
        inv_distrib = rewr (group_th       RS @{thm inv_distrib_group})
      }
    in
      SOME (fheads, normalize_group info)
    end

(* For simplification on terms, we represent a product of terms as a list. *)

(* Reduce a list of terms *)
fun reduce_atom_list G l =
    if length l = 0 then []
    else let
      val (head, rest) = (hd l, reduce_atom_list G (tl l))
    in
      if length rest = 0 then [head]
      else if is_inv_pair_l G (head, hd rest) orelse
              is_inv_pair_r G (head, hd rest) then tl rest
      else head :: rest
    end

fun mult_atom_list G (l1, l2) =
    (l1 @ l2) |> reduce_atom_list G

(* Compute the inverse of a list *)
fun inv_atom_list G l =
    let
      fun inv_atom atom =
          if is_inv G atom then dest_arg atom else inv_t $ G $ atom
    in
      rev (map inv_atom l)
    end

(* Normalization of a term as a product of terms. *)
fun norm_atom_list G t =
    if is_times G t then
      mult_atom_list G (norm_atom_list G (dest_arg1 t),
                        norm_atom_list G (dest_arg t))
    else if is_inv G t then
      inv_atom_list G (norm_atom_list G (dest_arg t))
    else if is_one G t then []
    else [t]

fun norm_term G t =
    list_times G (norm_atom_list G t)

val add_group_proofsteps =
    fold WfACUtil.add_alg_data [
      ("group", group_alg_data)

    ] #> fold add_prfstep [
      FOLAlgUtil.alg_norm1_prfstep (
        [times_t, inv_t], norm_term, @{term is_group}),

      FOLAlgUtil.alg_norm2_prfstep (
        [times_t, inv_t], norm_term, @{term is_group})
    ]

end  (* structure AlgGroup *)

val _ = Theory.setup (AlgGroup.add_group_proofsteps)
