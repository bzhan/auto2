theory Logic_Thms
imports Auto2_Base
begin

setup {* fold add_rew_const [@{term "True"}, @{term "False"}] *}
setup {* fold add_normalizer
  [("split_conj", K split_conj_th), ("split_not_disj", K split_not_disj_th)] *}

(* AC-property of conj and disj. *)
theorem conj_true_neutral: "(True \<and> A) = A" by simp
theorem disj_false_neutral: "(False \<or> A) = A" by simp
ML {*
val add_logic_ac_data =
  add_ac_data {fname = @{const_name disj}, assoc_r = true,
               unit_val = @{term False}, comm_th = @{thm disj_commute},
               assoc_th = @{thm disj_assoc}, unit_th = @{thm disj_false_neutral}} #>
  add_ac_data {fname = @{const_name conj}, assoc_r = true,
               unit_val = @{term True}, comm_th = @{thm conj_commute},
               assoc_th = @{thm conj_assoc}, unit_th = @{thm conj_true_neutral}}
*}
setup {* add_logic_ac_data *}

(* Rewrites A = True to A, etc. *)
theorem simp_eq_True: "(A simp= True) = A" by (simp add: simp_eq_def)
theorem simp_eq_False: "(A simp= False) = (\<not>A)" by (simp add: simp_eq_def)
theorem neq_True: "(A \<noteq> True) = (\<not>A)" by simp
theorem neq_False: "(A \<noteq> False) = A" by simp
setup {* fold add_eq_th_normalizer
  [@{thm HOL.eq_True}, @{thm HOL.eq_False}, @{thm simp_eq_True}, @{thm simp_eq_False},
   @{thm neq_True}, @{thm neq_False}] *}
theorem eq_False': "((\<not>A) = False) = A" by simp

(* Trivial contradictions. *)
setup {* add_resolve_prfstep @{thm HOL.refl} *}
theorem imp_triv: "A \<Longrightarrow> A" by simp
setup {* add_resolve_prfstep @{thm imp_triv} *}

(* Conj. Will be expanded by normalizer. *)
setup {* add_prfstep (prfstep_custom "conj_fact_list"
  [WithFact @{term_pat "?A \<and> ?B"},
   Filter (canonical_split_filter @{const_name conj} "A" "B")]
  (fn ((id, _), ths) => fn _ => [Update.thm_update (id, the_single ths)])) *}

(* Disj. Will be expanded by normalizer. *)
setup {* add_prfstep (prfstep_custom "disj_goal_list"
  [WithGoal @{term_pat "?A \<or> ?B"},
   Filter (canonical_split_filter @{const_name disj} "A" "B")]
  (fn ((id, _), ths) => fn _ => [Update.thm_update (id, the_single ths)])) *}

(* Equality. Invoke special treatment of equality. *)
theorem eq_elim: "C = (A = B) \<Longrightarrow> C \<Longrightarrow> A = B" by simp
setup {* add_forward_prfstep @{thm eq_elim} *}

(* Not. *)
ML {* val nn_cancel_th = @{thm HOL.nnf_simps(6)} *}
setup {* add_simp_rule nn_cancel_th #> add_eq_th_normalizer nn_cancel_th *}

(* Iff. *)
setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "(?A::bool) = ?B"},
   CreateCase ([@{term_pat "?A::bool"}], [@{term_pat "?B::bool"}])]) *}
setup {* add_fixed_sc ("iff_intro1", 25) *}  (* includes the cost of creating a case. *)
theorem iff_intro2: "A \<longrightarrow> B \<Longrightarrow> \<not>(A = B) \<Longrightarrow> \<not>A \<and> B" by simp
setup {* add_forward_prfstep @{thm iff_intro2} *}
setup {* add_fixed_sc ("Logic_Thms.iff_intro2", 1) *}

(* Implies. *)
theorem imp_intro: "\<not>(A \<longrightarrow> B) \<Longrightarrow> A \<and> \<not>B" by simp
setup {* add_forward_prfstep @{thm imp_intro} *}
setup {* add_fixed_sc ("Logic_Thms.imp_intro", 1) *}

(* Quantifiers (proofsteps in ML). *)
theorem exists_intro: "\<not> (\<exists>x. P x \<and> Q x) \<Longrightarrow> P x \<Longrightarrow> \<not> (Q x)" by simp
theorem exists_intro2: "\<not> (\<exists>x y. P x y \<and> Q x y) \<Longrightarrow> P x y \<Longrightarrow> \<not> (Q x y)" by simp
theorem exists_resolve: "\<not> (\<exists>x. P x) \<Longrightarrow> P x \<Longrightarrow> False" by simp
theorem forall_resolve0: "\<forall>x. P x \<Longrightarrow> \<not>(P x) \<Longrightarrow> False" by simp
theorem forall_resolve0': "\<forall>x. \<not>(P x) \<Longrightarrow> P x \<Longrightarrow> False" by simp
theorem forall_resolve: "\<forall>x. P x \<longrightarrow> Q x \<Longrightarrow> P x \<Longrightarrow> Q x" by simp
theorem forall_resolve_opp: "\<forall>x. P x \<longrightarrow> \<not>(Q x) \<Longrightarrow> Q x \<Longrightarrow> \<not>(P x)" by blast
theorem forall_resolve2: "\<forall>x y. P x y \<longrightarrow> Q x y \<Longrightarrow> P x y \<Longrightarrow> Q x y" by blast
theorem forall_eq: "\<forall>x. P x = Q x \<Longrightarrow> P x \<equiv> Q x" by simp
theorem forall_eq': "\<forall>x. P x = Q x \<Longrightarrow> Q x \<equiv> P x" by simp
theorem forall_eq2: "\<forall>x y. P x y = Q x y \<Longrightarrow> P x y \<equiv> Q x y" by simp
theorem forall_eq2': "\<forall>x y. P x y = Q x y \<Longrightarrow> Q x y \<equiv> P x y" by simp

(* Quantifiers: splitting (proofsteps in ML). *)
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
theorem exists_split': "(\<exists>y x. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
theorem forall_split1: "(\<forall>x y. P x \<and> Q y \<longrightarrow> R x y) = (\<forall>x. P x \<longrightarrow> (\<forall>y. Q y \<longrightarrow> R x y))" by smt
theorem forall_split2: "(\<forall>x y. P x \<and> Q y \<longrightarrow> R x y) = (\<forall>y. Q y \<longrightarrow> (\<forall>x. P x \<longrightarrow> R x y))" by smt
theorem forall_or: "(\<forall>x. ((A x \<or> B x) \<longrightarrow> C x)) = ((\<forall>x. A x \<longrightarrow> C x) \<and> (\<forall>x. B x \<longrightarrow> C x))" by blast

(* (\<forall>x. ?t = x \<longrightarrow> ?P x) = ?P ?t *)
setup {* add_eq_th_normalizer use_vardef_th *}
(* (\<forall>x. ?P \<longrightarrow> ?Q x) = (?P \<longrightarrow> (\<forall>x. ?Q x)) *)
setup {* add_eq_th_normalizer @{thm HOL.all_simps(6)} *}

(* Case analysis. *)
setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
   CreateCase ([@{term_pat "?cond::bool"}], [])]) *}
theorem if_true: "cond \<Longrightarrow> (if cond then yes else no) = yes" by (simp add: simp_eq_def)
setup {* add_forward_prfstep_cond @{thm if_true} [with_term "if ?cond then ?yes else ?no"] *}
theorem if_true': "(if a = a then yes else no) = yes" by simp
setup {* add_simp_rule @{thm if_true'} *}
theorem if_false: "\<not>cond \<Longrightarrow> (if cond then yes else no) = no" by simp
setup {* add_forward_prfstep_cond @{thm if_false} [with_term "if ?cond then ?yes else ?no"] *}
theorem if_false': "cond \<Longrightarrow> (if \<not>cond then yes else no) = no" by simp
setup {* add_forward_prfstep_cond @{thm if_false'} [with_term "if \<not> ?cond then ?yes else ?no"] *}
setup {* fold add_fixed_sc [("Logic_Thms.if_true", 1), ("Logic_Thms.if_true'", 1),
                            ("Logic_Thms.if_false", 1), ("Logic_Thms.if_false'", 1)] *}

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
