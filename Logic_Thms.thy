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
setup {* add_resolve_prfstep @{thm HOL.TrueI} *}
theorem FalseD' [resolve]: "\<not>False" by simp

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
setup {* add_gen_prfstep ("case_intro_eq_if",
  [WithItem (TY_EQ_IF, @{term_pat "(?t, if ?cond then ?x else ?y)"}),
   CreateCase @{term_pat "?cond::bool"}]) *}
theorem if_not_P': "P \<Longrightarrow> (if \<not>P then x else y) = y" by simp
setup {* fold add_rewrite_rule [@{thm HOL.if_P}, @{thm HOL.if_not_P}, @{thm if_not_P'}] *}
setup {* fold add_fixed_sc [("HOL.if_P", 1), ("HOL.if_not_P", 1), ("Logic_Thms.if_not_P'", 1)] *}

(* THE and \<exists>! *)
setup {* add_forward_prfstep_cond @{thm theI'} [with_term "THE x. ?P x"] *}
setup {* add_backward_prfstep @{thm HOL.ex_ex1I} *}
theorem ex_ex1I' [backward1]: "(\<forall>x y. P x \<longrightarrow> P y \<longrightarrow> x = y) \<Longrightarrow> P x \<Longrightarrow> \<exists>!x. P x" by auto
theorem the1_equality': "P a \<Longrightarrow> \<exists>!x. P x \<Longrightarrow> (THE x. P x) = a" by (simp add: the1_equality)
setup {* add_forward_prfstep_cond @{thm the1_equality'} [with_term "THE x. ?P x"] *}

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
setup {* add_rewrite_rule @{thm case_prod_conv} *}
setup {* add_rewrite_rule_cond @{thm case_prod_beta} [with_cond "?p \<noteq> (?s, ?t)"] *}
theorem pair_inject': "(a, b) = (a', b') \<Longrightarrow> a = a' \<and> b = b'" by simp
setup {* add_forward_prfstep_cond (conj_left_th @{thm pair_inject'}) [with_cond "?a \<noteq> ?a'"] *}
setup {* add_forward_prfstep_cond (conj_right_th @{thm pair_inject'}) [with_cond "?b \<noteq> ?b'"] *}
setup {* add_rewrite_rule_cond @{thm Product_Type.prod.collapse} [with_cond "?prod \<noteq> (fst ?prod, snd ?prod)"] *}

(* Let. *)
setup {* add_rewrite_rule (to_obj_eq_th @{thm Let_def}) *}

(* Equivalence relation *)
setup {* add_rewrite_rule @{thm symp_def} *}
setup {* add_rewrite_rule @{thm transp_def} *}

(* Options *)
theorem option_not_none [forward, backward]: "x \<noteq> None \<Longrightarrow> \<exists>p. x = Some p" by auto
setup {* add_resolve_prfstep @{thm option.distinct(1)} *}
setup {* add_rewrite_rule @{thm Option.option.sel} *}
theorem option_inject' [forward]: "Some i = Some j \<Longrightarrow> i = j" by simp
setup {* fold add_rewrite_rule @{thms Option.option.case} *}
setup {* fold add_fixed_sc [("Option.option.case_1", 1), ("Option.option.case_2", 1)] *}

(* In HOL, every type is non-empty. This can be invoked with CHOOSE "r::'a, ArbVar r" *)
definition ArbVar :: "'a \<Rightarrow> bool" where "ArbVar x = True"
theorem type_nonempty [resolve]: "\<exists>x. ArbVar x" by (simp add: ArbVar_def)

(* Quantifiers and other fundamental proofsteps. *)
ML_file "logic_steps.ML"

end
