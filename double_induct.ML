(* Double induction. Define separately from induction because it needs
   product.
 *)

signature DOUBLE_INDUCT_PROOFSTEPS =
sig
  val check_double_ind_th: thm -> (term * term) * (term list * term)
  val add_prfstep_double_induction: thm -> theory -> theory
  val DOUBLE_INDUCT: (string * string) * induct_info list -> pre_scripts
end;

structure Double_Induct_ProofSteps : DOUBLE_INDUCT_PROOFSTEPS =
struct

(* Check ind_th for a double induction is in the right form. *)
fun check_double_ind_th ind_th =
    let
      val thy = Thm.theory_of_thm ind_th
      fun err str = "check_double_ind_th: " ^ str
      val (cond_base1, (cond_base2, ind_th')) =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst dest_Trueprop
                 |> apsnd (Logic.dest_implies #> apfst dest_Trueprop)

      (* cond_base1 must be of form !n. ?P mb n, where mb is the base
         case for ?m.
       *)
      val err_base_hyp1 =
          err "First base assumption of ind_th must be !n. ?P mb n."
      val inst1 = pattern_fo_match_thy
                      thy (@{term_pat "!n. ?P ?mb n"}, cond_base1)
                  handle Pattern.MATCH => raise AUTO2 err_base_hyp1
      val mb = lookup_inst inst1 "mb"

      (* cond_base2 must be of form !m. ?P m nb, where nb is the base
         case for ?n.
       *)
      val err_base_hyp2 =
          err "Second base assumption of ind_th must be !m. ?P m nb."
      val inst2 = pattern_fo_match_thy
                      thy (@{term_pat "!m. ?P m ?nb"}, cond_base2)
                  handle Pattern.MATCH => raise AUTO2 err_base_hyp2
      val nb = lookup_inst inst2 "nb"
    in
      ((mb, nb), check_strong_ind_prop ind_th')
    end

fun add_prfstep_double_induction ind_th thy =
    let
      val ((mb, nb), (pat_vars, pat_subst)) = check_double_ind_th ind_th
      val ctxt = Proof_Context.init_global thy
      val name = name_of_thm ind_th
      val err = "add_prfstep_double_induction: should have two vars."
      val (pat_var1, pat_var2) =
          the_pair pat_vars handle AUTO2 _ => raise AUTO2 err

      (* Add user invoked proofstep. *)
      val (ty_var1, ty_var2) = apply2 type_of (pat_var1, pat_var2)
      val var1 = Var (("m", 0), ty_var1)
      val var2 = Var (("n", 0), ty_var2)
      val descs = [WithFact (Not $ (mk_eq (var1, mb))),
                   WithFact (Not $ (mk_eq (var2, nb)))]
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^
            (pretty_terms ctxt [pat_var1, pat_var2, pat_subst] |> str))
      val ty = HOLogic.mk_prodT (ty_var1, ty_var2)
    in
      thy |> add_typed_induct_data "double_induct" (ty, ind_th)
    end

fun DOUBLE_INDUCT ((var_spec_str1, var_spec_str2), ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      val (var1, rhs1, eq1) = process_var_spec_str ctxt var_spec_str1
      val (var2, rhs2, eq2) = process_var_spec_str ctxt var_spec_str2
      val ty = HOLogic.mk_prodT (type_of var1, type_of var2)

      val ind_th = the (get_typed_ind_th thy "double_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "DOUBLE_INDUCT: ind_th not found."
      val ((mb, nb), _) = check_double_ind_th ind_th
      val neq0 = mk_Trueprop (
            mk_disj (get_neq0_th (rhs1, mb), get_neq0_th (rhs2, nb)))
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = filter is_Free [rhs1, rhs2] @ arbitraries

      fun callback ((id, neq0_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "DOUBLE_INDUCT: cannot get var context."
            val (_, assums) = the var_ctxt
            val assums' = the_list eq1 @ the_list eq2 @ assums
            val (neq0_th1, neq0_th2) = the_pair (split_not_disj_th neq0_th)

            val p0_th =
                neq0_th1 |> use_var_eq ctxt eq1
                         |> process_neq0_th id (arbitraries, assums') st
                         |> Thm.forall_intr (cert ctxt var2)
                         |> apply_to_thm (to_obj_conv ctxt)
            val p1_th =
                neq0_th2 |> use_var_eq ctxt eq2
                         |> process_neq0_th id (arbitraries, assums') st
                         |> Thm.forall_intr (cert ctxt var1)
                         |> apply_to_thm (to_obj_conv ctxt)
            val var_infos = [(var1, eq1), (var2, eq2)]
            val ritems = apply_induction (the var_ctxt) var_infos ctxt ind_th
                                         [p0_th, p1_th]
          in
            [Update.thm_update (id, neq0_th),
             AddItems {id = id, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [InitAssum neq0], subs = [], cb = callback,
                    end_vars = maps get_new_vars [eq1, eq2]}]
    end

end  (* structure Double_Induct_ProofSteps. *)

open Double_Induct_ProofSteps
