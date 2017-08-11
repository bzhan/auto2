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
  val add_backward_replace_gnrc: thm -> Context.generic -> Context.generic
  val add_backward_replace_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward_replace: thm -> theory -> theory
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
        error "Add typing rule: concl is not a membership."
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
        error "Add typing rule: concl is not a membership."
    end

fun add_typing2_rule_gnrc th = add_typing2_rule_cond_gnrc th []
val add_typing2_rule_cond = Context.theory_map oo add_typing2_rule_cond_gnrc
fun add_typing2_rule th = add_typing2_rule_cond th []

fun add_backward_replace_cond_gnrc th conds gnrc =
    let
      val ctxt = context_of_gnrc gnrc
      val ctxt' = ctxt |> Variable.declare_term (Thm.prop_of th)
      val nm = name_of_thm th
      val concl = concl_of' th
      val conds' = map (fn cond => cond ctxt') conds
      fun prfstep_fn ((id, _), ths) items _ =
          let
            val th' = th |> apply_to_thm (Conv.rewr_conv backward_conv_th)
          in
            [AddItems {
                id = id, sc = SOME 1,
                raw_items = [Update.thm_to_ritem (ths MRS th')]},
             ShadowItem {id = id, item = the_single items}]
          end
          handle THM _ => []
    in
      add_prfstep_custom_gnrc (
        nm, ([WithGoal concl] @ conds'), PRIORITY_SHADOW, prfstep_fn) gnrc
    end

fun add_backward_replace_gnrc th = add_backward_replace_cond_gnrc th []
val add_backward_replace_cond =
    Context.theory_map oo add_backward_replace_cond_gnrc
fun add_backward_replace th = add_backward_replace_cond th []

end  (* structure Extra_FOL *)

open Extra_FOL
