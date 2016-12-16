theory Choice
imports Set
begin

(* Axiom of global choice. *)
axiomatization Choice :: "i \<Rightarrow> i" where
  choice_mem: "\<exists>x. x\<in>S \<Longrightarrow> Choice(S) \<in> S"
setup {* add_gen_prfstep ("Choice_case_intro",
  [WithTerm @{term_pat "Choice(?S)"}, CreateConcl @{term_pat "\<exists>x. x\<in>?S"}]) *}
setup {* add_forward_prfstep_cond @{thm choice_mem} [with_term "Choice(?S)"] *}

(* A more useful version  *)
definition choiceP :: "i \<Rightarrow> (i \<Rightarrow> o) \<Rightarrow> i" where choiceP_def [rewrite]:
  "choiceP(A,P) = Choice({x\<in>A. P(x)})"

syntax
  "_Eps" :: "[pttrn, o, o] => 'a"  ("(3SOME _\<in>_./ _)" [0, 10] 10)
translations
  "SOME x\<in>A. P" == "CONST choiceP(A, \<lambda>x. P)"

lemma someI: "\<exists>x\<in>A. P(x) \<Longrightarrow> (SOME x\<in>A. P(x)) \<in> A \<and> P(SOME x\<in>A. P(x))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "x\<in>A, P(x)" THEN HAVE "x\<in>{x\<in>A. P(x)}" THEN
    HAVE "Choice({x\<in>A. P(x)}) \<in> {x\<in>A. P(x)}") *})

setup {* add_gen_prfstep ("SOME_case_intro",
  [WithTerm @{term_pat "SOME k\<in>?A. ?P(k)"}, CreateConcl @{term_pat "\<exists>k\<in>?A. (?P::i\<Rightarrow>o)(k)"}]) *}
setup {* add_forward_prfstep_cond @{thm someI} [with_term "SOME x\<in>?A. ?P(x)"] *}
setup {* del_prfstep_thm @{thm choiceP_def} *}

end
