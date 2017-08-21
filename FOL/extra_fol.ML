(* Extra setup for FOL. *)

signature EXTRA_FOL =
sig
  val add_typing_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing_rule: thm -> theory -> theory
  val add_typing2_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_typing2_rule: thm -> theory -> theory
  val add_backward_replace_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward_replace: thm -> theory -> theory
end;

structure Extra_FOL : EXTRA_FOL =
struct

fun add_typing_rule_cond th conds thy =
    let
      val concl = th |> concl_of' |> strip_conj |> hd
      val th_name = name_of_thm th
    in
      if is_mem concl then
        thy |> add_forward_prfstep_cond th ([K (WithTerm (dest_arg1 concl))] @ conds)
            |> add_fixed_sc (th_name, 1)
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

fun add_backward_replace_cond th conds thy =
    let
      val ctxt = Proof_Context.init_global thy
      val ctxt' = ctxt |> Variable.declare_term (Thm.prop_of th)
      val th_name = name_of_thm th
      val concl = concl_of' th
      val conds' = map (fn cond => cond ctxt') conds
      fun prfstep_fn ((id, _), ths) items _ =
          let
            val th' = th |> apply_to_thm (Conv.rewr_conv UtilBase.backward_conv_th)
          in
            [AddItems {
                id = id, sc = SOME 1,
                raw_items = [Update.thm_to_ritem (ths MRS th')]},
             ShadowItem {id = id, item = the_single items}]
          end
          handle THM _ => []
    in
      add_prfstep_custom (
        th_name, ([WithGoal concl] @ conds'), PRIORITY_SHADOW, prfstep_fn) thy
    end

fun add_backward_replace th = add_backward_replace_cond th []

end  (* structure Extra_FOL *)

open Extra_FOL
