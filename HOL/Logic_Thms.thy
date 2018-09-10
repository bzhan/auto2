(*
  File: Logic_Thms.thy
  Author: Bohua Zhan

  Setup for proof steps related to logic.
*)

theory Logic_Thms
imports Auto2_HOL
begin

(* Trivial contradictions. *)
setup {* add_resolve_prfstep @{thm HOL.refl} *}
setup {* add_forward_prfstep @{thm contra_triv} *}
setup {* add_resolve_prfstep @{thm TrueI} *}
theorem FalseD [resolve]: "\<not>False" by simp
lemma exists_triv_eq [resolve]: "\<exists>x. x = x" by auto

(* Not. *)
setup {* add_forward_prfstep_cond @{thm HOL.not_sym} [with_filt (not_type_filter "s" boolT)] *}

(* Iff. *)
setup {* add_gen_prfstep ("iff_intro1",
  [WithGoal @{term_pat "(?A::bool) = ?B"},
   CreateCase @{term_pat "?A::bool"},
   WithScore 25]) *}
theorem iff_goal:
  "A \<noteq> B \<Longrightarrow> A \<Longrightarrow> \<not>B" "A \<noteq> B \<Longrightarrow> B \<Longrightarrow> \<not>A"
  "A \<noteq> B \<Longrightarrow> \<not>A \<Longrightarrow> B" "A \<noteq> B \<Longrightarrow> \<not>B \<Longrightarrow> A"
  "(\<not>A) \<noteq> B \<Longrightarrow> A \<Longrightarrow> B" "A \<noteq> (\<not>B) \<Longrightarrow> B \<Longrightarrow> A" by auto
setup {* fold (fn th => add_forward_prfstep_cond th [with_score 1]) @{thms iff_goal} *}

(* Quantifiers: normalization *)
theorem exists_split: "(\<exists>x y. P x \<and> Q y) = ((\<exists>x. P x) \<and> (\<exists>y. Q y))" by simp
setup {* add_backward_prfstep (equiv_backward_th @{thm exists_split}) *}

(* Case analysis. *)
setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
   CreateCase @{term_pat "?cond::bool"}]) *}
setup {* add_gen_prfstep ("case_intro_fact",
  [WithFact @{term_pat "if ?cond then (?yes::bool) else ?no"},
   CreateCase @{term_pat "?cond::bool"}]) *}
setup {* add_gen_prfstep ("case_intro_goal",
  [WithGoal @{term_pat "if ?cond then (?yes::bool) else ?no"},
   CreateCase @{term_pat "?cond::bool"}]) *}
lemma if_eval':
  "P \<Longrightarrow> (if \<not>P then x else y) = y" by auto
lemma ifb_eval:
  "P \<Longrightarrow> (if P then (x::bool) else y) = x"
  "\<not>P \<Longrightarrow> (if P then (x::bool) else y) = y"
  "P \<Longrightarrow> (if \<not>P then (x::bool) else y) = y" by auto
setup {* fold (fn th => add_rewrite_rule_cond th [with_score 1])
  ([@{thm HOL.if_P}, @{thm HOL.if_not_P}, @{thm if_eval'}] @ @{thms ifb_eval}) *}

(* THE and \<exists>! *)
setup {* add_forward_prfstep_cond @{thm theI'} [with_term "THE x. ?P x"] *}
setup {* add_gen_prfstep ("ex1_case",
  [WithGoal @{term_pat "\<exists>!x. ?P x"}, CreateConcl @{term_pat "\<exists>x. ?P x"}]) *}
theorem ex_ex1I' [backward1]: "\<forall>y. P y \<longrightarrow> x = y \<Longrightarrow> P x \<Longrightarrow> \<exists>!x. P x" by auto
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
  (fn ((id, _), ths) => fn _ => fn _ =>
    let
      val choice = @{thm choice} |> apply_to_thm (Conv.rewr_conv UtilBase.backward_conv_th)
    in
      [Update.thm_update (id, (ths MRS choice))]
    end
    handle THM _ => []))
*}

(* Least operator. *)
theorem Least_equality' [backward1]:
  "P (x::('a::order)) \<Longrightarrow> \<forall>y. P y \<longrightarrow> x \<le> y \<Longrightarrow> Least P = x" by (simp add: Least_equality)

(* Pairs. *)
lemma pair_inj: "(a,b) = c \<longleftrightarrow> a = fst c \<and> b = snd c" by auto
setup {* Normalizer.add_inj_struct_data @{thm pair_inj} *}

setup {* add_rewrite_rule @{thm fst_conv} *}
setup {* add_rewrite_rule @{thm snd_conv} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm prod.simps(1)}) *}
setup {* add_rewrite_rule_cond @{thm surjective_pairing} [with_cond "?t \<noteq> (?a, ?b)"] *}
setup {* Normalizer.add_rewr_normalizer ("rewr_case", (to_meta_eq @{thm case_prod_beta'})) *}

(* Let. *)
setup {* Normalizer.add_rewr_normalizer ("rewr_let", @{thm Let_def}) *}

(* Equivalence relations *)  
setup {* add_forward_prfstep @{thm Relation.symD} *}
setup {* add_backward_prfstep @{thm Relation.symI} *}
setup {* add_forward_prfstep @{thm Relation.transD} *}
setup {* add_backward_prfstep @{thm Relation.transI} *}

(* Options *)
setup {* add_resolve_prfstep @{thm option.distinct(1)} *}
setup {* add_rewrite_rule @{thm Option.option.sel} *}
setup {* add_forward_prfstep @{thm option.collapse} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm option.simps(1)}) *}
setup {* fold (fn th => add_rewrite_rule_cond th [with_score 1]) @{thms Option.option.case} *}

end
