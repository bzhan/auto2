(* Extra setup for FOL. *)

signature EXTRA_FOL =
sig
  val add_typing_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing_rule: thm -> theory -> theory
  val add_typing2_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing2_rule: thm -> theory -> theory
end;

structure Extra_FOL : EXTRA_FOL =
struct

fun add_typing_rule_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
      val conds = [with_score 1, K (WithTerm (dest_arg1 concl))] @ conds
    in
      if is_mem concl then
        thy |> add_forward_prfstep_cond th conds
      else
        error "Add typing rule: concl is not a membership."
    end

fun add_typing_rule th = add_typing_rule_cond th []

fun add_typing2_rule_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
    in
      if is_mem concl then
        thy |> add_forward_prfstep_cond th ([K (WithTerm (dest_arg concl))] @ conds)
      else
        error "Add typing rule: concl is not a membership."
    end

fun add_typing2_rule th = add_typing2_rule_cond th []

end  (* structure Extra_FOL *)

open Extra_FOL
