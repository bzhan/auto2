(* Extra setup for FOL. *)

signature EXTRA_FOL =
sig
  val is_mem: term -> bool

  val add_typing_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_typing_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing_rule: thm -> theory -> theory
  val add_typing2_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_typing2_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing2_rule: thm -> theory -> theory
end;

structure Extra_FOL : EXTRA_FOL =
struct

fun is_mem t =
    case t of
        Const (c, _) $ _ $ _ => c = Mem_name
      | _ => false

fun add_typing_rule_cond_gnrc th conds gnrc =
    let
      val concl = th |> strip_horn' |> snd
    in
      if is_mem concl then
        gnrc |> add_forward_prfstep_cond_gnrc
             th ([K (WithTerm (dest_arg1 concl))] @ conds)
      else
        raise AUTO2 "add_typing_rule: concl is not a membership."
    end

fun add_typing_rule_gnrc th = add_typing_rule_cond_gnrc th []
val add_typing_rule_cond = Context.theory_map oo add_typing_rule_cond_gnrc
fun add_typing_rule th = add_typing_rule_cond th []

fun add_typing2_rule_cond_gnrc th conds gnrc =
    let
      val concl = th |> strip_horn' |> snd
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

end  (* structure Extra_FOL *)

open Extra_FOL
