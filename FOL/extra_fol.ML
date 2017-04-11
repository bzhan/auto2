(* Extra setup for FOL. *)

signature EXTRA_FOL =
sig
  val add_typing_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_typing_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing_rule: thm -> theory -> theory
  val add_typing2_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_typing2_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing2_rule: thm -> theory -> theory

  val add_rewrite_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_rule_back_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_rule_bidir_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory
end;

structure Extra_FOL : EXTRA_FOL =
struct

fun add_typing_rule_cond_gnrc th conds gnrc =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
      val nm = name_of_thm th
    in
      if is_mem concl then
        gnrc |> add_forward_prfstep_cond_gnrc
             th ([K (WithTerm (dest_arg1 concl))] @ conds)
             |> add_fixed_sc_gnrc (nm, 1)
      else
        raise AUTO2 "add_typing_rule: concl is not a membership."
    end

fun add_typing_rule_gnrc th = add_typing_rule_cond_gnrc th []
val add_typing_rule_cond = Context.theory_map oo add_typing_rule_cond_gnrc
fun add_typing_rule th = add_typing_rule_cond th []

fun add_typing2_rule_cond_gnrc th conds gnrc =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      if is_mem concl then
        gnrc |> add_forward_prfstep_cond_gnrc
             th ([K (WithTerm (dest_arg concl))] @ conds)
      else
        raise AUTO2 "add_typing2_rule: concl is not a membership."
    end

fun add_typing2_rule_gnrc th = add_typing2_rule_cond_gnrc th []
val add_typing2_rule_cond = Context.theory_map oo add_typing2_rule_cond_gnrc
fun add_typing2_rule th = add_typing2_rule_cond th []

fun add_rewrite_rule_cond_gnrc th conds gnrc =
    let
      val th = if is_meta_eq (Thm.concl_of th) then to_obj_eq_th th else th
      val (lhs, _) = th |> concl_of' |> strip_conj |> hd |> dest_eq
    in
      if fastype_of lhs = boolT then
        ProofStep_Data.add_rewrite_iff_rule_cond_gnrc th conds gnrc
      else
        ProofStep_Data.add_rewrite_rule_cond_gnrc th conds gnrc
    end

fun add_rewrite_rule_back_cond_gnrc th conds =
    add_rewrite_rule_cond_gnrc (obj_sym_th th) conds

fun add_rewrite_rule_bidir_cond_gnrc th conds =
    (add_rewrite_rule_cond_gnrc th conds)
        #> add_rewrite_rule_back_cond_gnrc th conds

fun add_rewrite_rule_gnrc th = add_rewrite_rule_cond_gnrc th []
fun add_rewrite_rule_back_gnrc th = add_rewrite_rule_back_cond_gnrc th []
fun add_rewrite_rule_bidir_gnrc th = add_rewrite_rule_bidir_cond_gnrc th []

val add_rewrite_rule_cond =
    Context.theory_map oo add_rewrite_rule_cond_gnrc

val add_rewrite_rule_back_cond =
    Context.theory_map oo add_rewrite_rule_back_cond_gnrc

val add_rewrite_rule_bidir_cond =
    Context.theory_map oo add_rewrite_rule_bidir_cond_gnrc

fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th

end  (* structure Extra_FOL *)

open Extra_FOL
