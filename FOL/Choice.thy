theory Choice
imports Structure
begin

(* Axiom of global choice. *)
axiomatization Choice :: "i \<Rightarrow> i" where
  choice: "\<exists>x. x\<in>S \<Longrightarrow> Choice(S) \<in> S"
setup {* add_prfstep_check_req ("Choice(S)", "\<exists>x. x\<in>S") *}
setup {* add_forward_prfstep_cond @{thm choice} [with_term "Choice(?S)"] *}

(* A more useful version  *)
definition choiceP :: "i \<Rightarrow> (i \<Rightarrow> o) \<Rightarrow> i" where [rewrite]:
  "choiceP(A,P) = Choice({x\<in>A. P(x)})"

abbreviation choiceP_carrier :: "i \<Rightarrow> (i \<Rightarrow> o) \<Rightarrow> i" where
  "choiceP_carrier(S,P) \<equiv> choiceP(carrier(S),P)"

syntax
  "_Eps" :: "[pttrn, o, o] => 'a"  ("(3SOME _\<in>_./ _)" [0, 10] 10)
  "_Eps_carrier" :: "[pttrn, o, o] => 'a"  ("(3SOME _\<in>._./ _)" [0, 10] 10)
translations
  "SOME x\<in>A. P" == "CONST choiceP(A, \<lambda>x. P)"
  "SOME x\<in>.S. P" == "CONST choiceP_carrier(S, \<lambda>x. P)"

lemma someI: "\<exists>x\<in>A. P(x) \<Longrightarrow> (SOME x\<in>A. P(x)) \<in> A \<and> P(SOME x\<in>A. P(x))"
@proof
  @obtain "x \<in> A" where "P(x)" @then @have "x\<in>{x\<in>A. P(x)}" @then
  @have "Choice({x\<in>A. P(x)}) \<in> {x\<in>A. P(x)}"
@qed
setup {* add_forward_prfstep_cond @{thm someI} [with_term "SOME x\<in>?A. ?P(x)"] *}

setup {* add_prfstep_check_req ("SOME k\<in>A. P(k)", "\<exists>k\<in>A. P(k)") *}
setup {* del_prfstep_thm @{thm choiceP_def} *}

end
