(* Using induction rules derived from function definitions. *)

signature SEP_INDUCT =
sig
  val add_hoare_induct_rule: term * thm -> theory -> theory
  val hoare_induct_cmd: Proof.state -> Proof.state
end;

structure SepInduct : SEP_INDUCT =
struct

fun add_hoare_induct_rule (t, ind_th) thy =
    thy |> Induct_ProofSteps.add_induct_data "hoare_induct" (t, ind_th)

fun hoare_induct_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val {prop, ...} = Auto2_Outer.get_head ctxt
      val subgoal = prop |> Auto2_Outer.subgoal_of |> Thm.term_of |> dest_Trueprop
      val (_, c, _) = SepUtil.dest_hoare_triple subgoal
      val (c_head, vars) = Term.strip_comb c
      val arbitraries = (map Free (Term.add_frees subgoal []))
                            |> subtract (op aconv) vars

      val ind_th = the (Induct_ProofSteps.get_term_ind_th thy "hoare_induct" c_head)

      val P = subgoal |> fold mk_obj_all (rev arbitraries)
                      |> fold lambda_abstract (rev vars)

      val (var_P, var_args) = ind_th |> concl_of' |> Term.strip_comb
      val inst = fold (Pattern.match thy) ((var_P, P) :: (var_args ~~ vars))
                      fo_init
      val ind_th =
          ind_th |> subst_thm ctxt inst
                 |> apply_to_thm (Conv.binop_conv (to_meta_all_imp_conv ctxt))

      val assum = hd (Drule.cprems_of ind_th)
      val ind_th =
          ind_th |> send_first_to_hyps
                 |> fold Thm.forall_elim (map (cert ctxt) arbitraries)
                 |> Thm.implies_intr assum

      val t' = case Thm.prop_of ind_th of
                   imp $ A $ B => imp $ rename_abs_term vars A $ B
                 | _ => error "hoare_induct_cmd"
      val ind_th = ind_th |> Thm.renamed_prop t'
                          |> Goal.protect 1
    in
      state |> Proof.map_contexts (Auto2_Outer.set_head_th ind_th)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@hoare_induct"} "Hoare induction"
    (Scan.succeed (
        Toplevel.proof (fn state => hoare_induct_cmd state)))

end  (* structure SepInduct *)

val add_hoare_induct_rule = SepInduct.add_hoare_induct_rule
