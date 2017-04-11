(* Extra setup for HOL. *)

signature EXTRA_HOL =
sig
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

structure Extra_HOL : EXTRA_HOL =
struct

fun add_rewrite_rule_cond_gnrc th conds gnrc =
    let
      val (lhs, _) = if is_meta_eq (Thm.concl_of th) then
                       Logic.dest_equals (Thm.concl_of th)
                     else dest_eq (concl_of' th)
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

end  (* structure Extra_HOL *)

open Extra_HOL
