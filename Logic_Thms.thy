(* Setup for proof steps related to logic. *)

theory Logic_Thms
imports Auto2_Base
begin

(* First add proofstep converting any PROP equality to EQ. Then use EQ to match
   equality in all proofsteps. *)
theorem trivial_eq: "A = B \<Longrightarrow> A = B" by simp
setup {* add_gen_prfstep ("trivial_eq",
  [WithItem (TY_PROP, @{term_pat "(?A::?'a) = ?B"}),
   GetFact (@{term_pat "(?A::?'a) = ?B"}, @{thm trivial_eq})]) *}

setup {* fold add_rew_const [@{term "True"}, @{term "False"}] *}
setup {* fold add_th_normalizer
  [("split_conj", K split_conj_th), ("split_not_disj", K split_not_disj_th)] *}

(* AC-property of conj and disj. *)
ML {*
val add_logic_ac_data =
    fold ACUtil.add_ac_data [
      {fname = @{const_name disj}, assoc_r = true,
       assoc_th = @{thm disj_assoc}, comm_th = @{thm disj_commute},
       unit_val = @{term False}, unit_th = @{thm HOL.simp_thms(32)}, unitr_th = true_th,
       uinv_name = "", inv_name = "", double_inv_th = true_th,
       distr_inv_th = true_th, binop_inv_th = true_th, unit_inv_th = true_th},

      {fname = @{const_name conj}, assoc_r = true,
       assoc_th = @{thm conj_assoc}, comm_th = @{thm conj_commute},
       unit_val = @{term True}, unit_th = @{thm HOL.simp_thms(22)}, unitr_th = true_th,
       uinv_name = "", inv_name = "", double_inv_th = true_th,
       distr_inv_th = true_th, binop_inv_th = true_th, unit_inv_th = true_th}]
*}
setup {* add_logic_ac_data *}
ML {*
  val conj_ac = the (ACUtil.get_head_ac_info @{theory} @{term "A \<and> B"})
  val disj_ac = the (ACUtil.get_head_ac_info @{theory} @{term "A \<or> B"})
*}

(* Rewrites A = True to A, etc. *)
theorem neq_True: "(A \<noteq> True) = (\<not>A)" by simp
theorem neq_False: "(A \<noteq> False) = A" by simp
setup {* fold (fn th => add_eq_th_normalizer th #> add_top_eq_th_normalizer th)
  [@{thm HOL.eq_True}, @{thm HOL.eq_False}, @{thm neq_True}, @{thm neq_False}] *}

(* Trivial contradictions. *)
setup {* add_resolve_prfstep @{thm HOL.refl} *}
setup {* add_forward_prfstep @{thm contra_triv} *}

(* Conj. Will be expanded by normalizer. *)
theorem conj_id: "A \<and> B \<Longrightarrow> A \<and> B" by simp
setup {* add_forward_prfstep_cond @{thm conj_id}
  [with_filt (canonical_split_filter @{const_name conj} "A" "B")] *}

(* Disj. Will be expanded by normalizer. *)
theorem disj_id: "A \<or> B \<Longrightarrow> A \<or> B" by simp
setup {* add_backward_prfstep_cond @{thm disj_id}
  [with_filt (canonical_split_filter @{const_name disj} "A" "B")] *}

(* Not. *)
setup {* add_rewrite_rule nn_cancel_th #> add_eq_th_normalizer nn_cancel_th *}
setup {* add_forward_prfstep_cond @{thm HOL.not_sym} [with_filt (not_type_filter "s" boolT)] *}

(* Iff. *)
setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "(?A::bool) = ?B"}, CreateCase @{term_pat "?A::bool"}]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_two_dirs [forward]: "A \<noteq> B \<Longrightarrow> (A \<longrightarrow> \<not>B) \<and> (\<not>A \<longrightarrow> B)" by auto
setup {* add_fixed_sc ("Logic_Thms.iff_two_dirs", 1) *}

(* Implies. *)
setup {* add_forward_prfstep @{thm Meson.not_impD} *}
setup {* add_fixed_sc ("Meson.not_impD", 1) *}
lemma not_conj_to_imp: "\<not>(A \<and> B) \<longleftrightarrow> A \<longrightarrow> \<not>B" by simp  (* used in not_ex_forall_cv *)

(* Quantifiers: normalization *)
theorem forall_or [forward]:
  "(\<forall>x. ((A x \<or> B x) \<longrightarrow> C x)) \<Longrightarrow> ((\<forall>x. A x \<longrightarrow> C x) \<and> (\<forall>x. B x \<longrightarrow> C x))" by blast

theorem contract_not_forall: "\<not>(\<forall>x. P) \<longleftrightarrow> \<not>P" by simp
ML {*
val forall_norm_ths = [
  @{thm all_conj_distrib}, @{thm use_vardef}, @{thm HOL.all_simps(6)},
  @{thm HOL.simp_thms(35)}, @{thm contract_not_forall}]
*}
setup {* fold add_eq_th_normalizer forall_norm_ths *}
setup {* add_backward_prfstep (equiv_backward_th @{thm ex_disj_distrib}) *}
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
setup {* add_backward_prfstep (equiv_backward_th @{thm exists_split}) *}

(* Bounded quantifiers. *)
setup {* add_backward_prfstep (equiv_backward_th @{thm bex_iff}) *}

(* Case analysis. *)
setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
   CreateCase @{term_pat "?cond::bool"}]) *}
theorem if_not_P': "P \<Longrightarrow> (if \<not>P then x else y) = y" by simp
setup {* fold add_rewrite_rule [@{thm HOL.if_P}, @{thm HOL.if_not_P}, @{thm if_not_P'}] *}
setup {* fold add_fixed_sc [("HOL.if_P", 1), ("HOL.if_not_P", 1), ("Logic_Thms.if_not_P'", 1)] *}

(* Hilbert choice. *)
setup {* add_gen_prfstep ("SOME_case_intro",
  [WithTerm @{term_pat "SOME k. ?P k"}, CreateConcl @{term_pat "\<exists>k. ?P k"}]) *}
setup {* add_forward_prfstep_cond @{thm someI} [with_term "SOME x. ?P x"] *}
setup {* add_forward_prfstep_cond @{thm someI_ex} [with_term "SOME x. ?P x"] *}

(* Axiom of choice *)
setup {* add_prfstep_custom ("ex_choice",
  [WithGoal @{term_pat "EX f. !x. ?Q f x"}],
  [Update.ADD_ITEMS],
  (fn ((id, _), ths) => fn _ => fn _ =>
    [Update.thm_update (id, (ths MRS (backward_th @{thm choice})))]
    handle THM _ => []))
*}

(* Extensionality. *)
theorem set_ext [resolve]: "\<forall>a. a \<in> S \<longleftrightarrow> a \<in> T \<Longrightarrow> S = T" by auto
theorem set_pair_ext [resolve]: "\<forall>a b. (a, b) \<in> S \<longleftrightarrow> (a, b) \<in> T \<Longrightarrow> S = T" by auto

(* Least operator. *)
theorem Least_equality' [backward1]:
  "P (x::('a::order)) \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le> y \<Longrightarrow> Least P = x" by (simp add: Least_equality)

(* Pairs. *)
setup {* add_rewrite_rule @{thm fst_conv} *}
setup {* add_rewrite_rule @{thm snd_conv} *}

(* Let. *)
setup {* add_rewrite_rule (to_obj_eq_th @{thm Let_def}) *}

(* Eta contraction *)
setup {* add_prfstep_conv ("eta_contract", [WithTerm @{term_pat "?A"}], Thm.eta_conversion) *}

(* Equivalence relation *)
setup {* add_rewrite_rule @{thm symp_def} *}
setup {* add_rewrite_rule @{thm transp_def} *}

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
