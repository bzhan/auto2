theory Logic_Thms
imports Auto2_Base
begin

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
setup {* fold add_eq_th_normalizer
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
  [WithGoal @{term_pat "(?A::bool) = ?B"},
   CreateCase ([@{term_pat "?A::bool"}], [@{term_pat "?B::bool"}])]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_intro2 [forward]: "A \<longrightarrow> B \<Longrightarrow> \<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<and> B" by simp
setup {* add_fixed_sc ("Logic_Thms.iff_intro2", 1) *}

(* Implies. *)
setup {* add_forward_prfstep @{thm Meson.not_impD} *}
setup {* add_fixed_sc ("Meson.not_impD", 1) *}
lemma not_conj_to_imp: "\<not>(A \<and> B) \<longleftrightarrow> A \<longrightarrow> \<not>B" by simp  (* used in not_ex_forall_cv *)

(* Quantifiers: splitting. *)
setup {* add_forward_prfstep (equiv_forward_th @{thm all_conj_distrib}) *}
theorem forall_or [forward]:
  "(\<forall>x. ((A x \<or> B x) \<longrightarrow> C x)) \<Longrightarrow> ((\<forall>x. A x \<longrightarrow> C x) \<and> (\<forall>x. B x \<longrightarrow> C x))" by blast
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
setup {* add_backward_prfstep (equiv_backward_th @{thm exists_split}) *}
setup {* add_backward_prfstep (equiv_backward_th @{thm ex_disj_distrib}) *}

(* Quantifiers: swapping out of ALL or EX *)
theorem swap_forall_imp: "(\<forall>x. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x. Q x))" by auto
theorem swap_ex_conj: "(\<exists>x. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x. Q x))" by auto

(* (\<forall>x. x = ?t \<longrightarrow> ?P x) = ?P ?t *)
setup {* add_eq_th_normalizer @{thm use_vardef} *}
(* (\<forall>x. ?P \<longrightarrow> ?Q x) = (?P \<longrightarrow> (\<forall>x. ?Q x)) *)
setup {* add_eq_th_normalizer @{thm HOL.all_simps(6)} *}

(* Case analysis. *)
setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
   CreateCase ([@{term_pat "?cond::bool"}], [])]) *}
theorem if_eq: "(if a = a then x else y) = x" by simp
theorem if_not_P': "P \<Longrightarrow> (if \<not>P then x else y) = y" by simp
setup {* fold add_rewrite_rule [@{thm HOL.if_P}, @{thm HOL.if_not_P}, @{thm if_not_P'}] *}
setup {* fold add_fixed_sc [("HOL.if_P", 1), ("HOL.if_not_P", 1), ("Logic_Thms.if_not_P'", 1)] *}

(* Hilbert choice. *)
setup {* add_gen_prfstep ("SOME_case_intro",
  [WithTerm @{term_pat "SOME k. ?P k"},
   CreateCase ([], [@{term_pat "\<exists>k. ?P k"}])]) *}
setup {* add_forward_prfstep_cond @{thm someI} [with_term "SOME x. ?P x"] *}
setup {* add_forward_prfstep_cond @{thm someI_ex} [with_term "SOME x. ?P x"] *}

(* Least operator. *)
theorem Least_equality' [backward1]:
  "P (x::('a::order)) \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le> y \<Longrightarrow> Least P = x" by (simp add: Least_equality)

(* Pairs. *)
setup {* add_rewrite_rule @{thm fst_conv} *}
setup {* add_rewrite_rule @{thm snd_conv} *}

(* Let. *)
setup {* add_rewrite_rule (to_obj_eq_th @{thm Let_def}) *}

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
