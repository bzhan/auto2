(* Setup for proof steps related to logic. *)

theory Logic_Thms
imports Auto2_Base
begin

setup {* fold add_th_normalizer
  [("split_conj", K split_conj_th), ("split_not_disj", K split_not_disj_th)] *}

(* AC-property of conj and disj. *)
theorem disj_is_assoc: "is_assoc_fn (op \<or>)" by (simp add: is_assoc_fn_def)
theorem disj_is_comm: "is_comm_fn (op \<or>)" using is_comm_fn_def by blast
theorem disj_has_unit: "is_unit_fn False (op \<or>)" by (simp add: is_unit_fn_def)
theorem conj_is_assoc: "is_assoc_fn (op \<and>)" by (simp add: is_assoc_fn_def)
theorem conj_is_comm: "is_comm_fn (op \<and>)" using is_comm_fn_def by blast
theorem conj_has_unit: "is_unit_fn True (op \<and>)" by (simp add: is_unit_fn_def)

ML {*
val conj_ac_raw =
  {fname = @{const_name conj},
   assoc_th = @{thm conj_is_assoc}, comm_th = @{thm conj_is_comm},
   unit_th = @{thm conj_has_unit}, uinv_th = true_th, inv_th = true_th}
val disj_ac_raw = 
  {fname = @{const_name disj},
   assoc_th = @{thm disj_is_assoc}, comm_th = @{thm disj_is_comm},
   unit_th = @{thm disj_has_unit}, uinv_th = true_th, inv_th = true_th}
val add_logic_ac_data = fold ACUtil.add_ac_data [conj_ac_raw, disj_ac_raw]
val conj_ac = the (ACUtil.inst_ac_info @{theory} boolT conj_ac_raw)
val disj_ac = the (ACUtil.inst_ac_info @{theory} boolT disj_ac_raw)
*}
setup {* add_logic_ac_data *}

(* Other conj and disj *)
theorem conj_same [backward]: "A \<Longrightarrow> A \<and> A" by auto

(* Rewrites P = True to P, etc. *)
setup {* fold add_eq_th_normalizer [@{thm HOL.eq_True}, @{thm HOL.eq_False}] *}

(* Trivial contradictions. *)
setup {* add_resolve_prfstep @{thm HOL.refl} *}
setup {* add_forward_prfstep @{thm contra_triv} *}

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
setup {* fold add_eq_th_normalizer @{thms HOL.simp_thms(35,36)} *}
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
setup {* add_backward_prfstep (equiv_backward_th @{thm exists_split}) *}

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
  PRIORITY_ADD,
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

(* Equivalence relation *)
setup {* add_rewrite_rule @{thm symp_def} *}
setup {* add_rewrite_rule @{thm transp_def} *}

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
