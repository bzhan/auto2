theory Logic_Thms
imports Auto2_Base
begin

setup {* fold add_rew_const [@{term "True"}, @{term "False"}] *}
setup {* fold add_th_normalizer
  [("split_conj", K split_conj_th), ("split_not_disj", K split_not_disj_th)] *}

(* AC-property of conj and disj. *)
theorem conj_true_neutral: "(True \<and> A) = A" by simp
theorem disj_false_neutral: "(False \<or> A) = A" by simp
ML {*
val add_logic_ac_data =
    fold add_ac_data [
      {fname = @{const_name disj}, assoc_r = true,
       unit_val = @{term False}, comm_th = @{thm disj_commute},
       assoc_th = @{thm disj_assoc}, unit_th = @{thm disj_false_neutral}},

      {fname = @{const_name conj}, assoc_r = true,
       unit_val = @{term True}, comm_th = @{thm conj_commute},
       assoc_th = @{thm conj_assoc}, unit_th = @{thm conj_true_neutral}}]
*}
setup {* add_logic_ac_data *}

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

(* Iff. *)
setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "(?A::bool) = ?B"},
   CreateCase ([@{term_pat "?A::bool"}], [@{term_pat "?B::bool"}])]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_intro2: "A \<longrightarrow> B \<Longrightarrow> \<not>(A \<longleftrightarrow> B) \<Longrightarrow> \<not>A \<and> B" by simp
setup {* add_forward_prfstep @{thm iff_intro2} *}
setup {* add_fixed_sc ("Logic_Thms.iff_intro2", 1) *}

(* Implies. *)
setup {* add_forward_prfstep @{thm Meson.not_impD} *}
setup {* add_fixed_sc ("Meson.not_impD", 1) *}

(* Quantifiers. *)
theorem exists_intro: "\<not> (\<exists>x. P x \<and> Q x) \<Longrightarrow> P x \<Longrightarrow> \<not> (Q x)" by simp
theorem exists_resolve: "\<not> (\<exists>x. P x) \<Longrightarrow> P x \<Longrightarrow> False" by simp
theorem forall_impl: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x" by simp
setup {* add_rewrite_rule @{thm HOL.not_all} *}

(* Quantifiers: splitting. *)
theorem forall_or: "(\<forall>x. ((A x \<or> B x) \<longrightarrow> C x)) \<Longrightarrow> ((\<forall>x. A x \<longrightarrow> C x) \<and> (\<forall>x. B x \<longrightarrow> C x))" by blast
setup {* add_forward_prfstep @{thm forall_or} *}
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
setup {* add_rewrite_rule @{thm exists_split} *}
theorem exists_split': "(\<exists>y x. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp

(* (\<forall>x. x = ?t \<longrightarrow> ?P x) = ?P ?t *)
setup {* add_eq_th_normalizer @{thm use_vardef} *}
(* (\<forall>x. ?P \<longrightarrow> ?Q x) = (?P \<longrightarrow> (\<forall>x. ?Q x)) *)
setup {* add_eq_th_normalizer @{thm HOL.all_simps(6)} *}

(* Case analysis. *)
setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
   CreateCase ([@{term_pat "?cond::bool"}], [])]) *}
theorem if_true': "(if a = a then yes else no) = yes" by simp
theorem if_false': "cond \<Longrightarrow> (if \<not>cond then yes else no) = no" by simp
setup {* fold add_rewrite_rule [@{thm HOL.if_P}, @{thm HOL.if_not_P}, @{thm if_false'}] *}
setup {* fold add_fixed_sc [("HOL.if_P", 1), ("HOL.if_not_P", 1), ("Logic_Thms.if_false'", 1)] *}

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
