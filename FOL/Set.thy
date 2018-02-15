theory Set
imports Logic_FOL
begin

section \<open>Axiom of extension\<close>

axiomatization where
  extension [backward]: "\<forall>z. z \<in> x \<longleftrightarrow> z \<in> y \<Longrightarrow> x = y"
setup {* add_fixed_sc ("Set.extension@back", 500) *}

section \<open>Axiom of empty set\<close>

axiomatization Empty_set :: "i"  ("\<emptyset>") where
  empty_set [resolve]: "x \<notin> \<emptyset>"

lemma nonempty_mem [backward]: "A \<noteq> \<emptyset> \<Longrightarrow> \<exists>x. x \<in> A" by auto2

section \<open>Axiom schema of specification\<close>

axiomatization Collect :: "[i, i \<Rightarrow> o] \<Rightarrow> i" where
  collect [rewrite]: "x \<in> Collect(A,P) \<longleftrightarrow> (x \<in> A \<and> P(x))"

syntax
  "_Collect" :: "[pttrn, i, o] \<Rightarrow> i"  ("(1{_ \<in> _ ./ _})")
translations
  "{x\<in>A. P}" \<rightleftharpoons> "CONST Collect(A, \<lambda>x. P)"

section \<open>Axiom of pairing\<close>

axiomatization Upair :: "[i, i] \<Rightarrow> i" where
  upair [rewrite]: "x \<in> Upair(y,z) \<longleftrightarrow> (x = y \<or> x = z)"

lemma Upair_nonempty [resolve]: "Upair(a,b) \<noteq> \<emptyset>"
@proof @have "a \<in> Upair(a,b)" @qed

section \<open>Axiom of union\<close>

axiomatization Union :: "i \<Rightarrow> i"  ("\<Union>_" [90] 90) where
  union [rewrite]: "x \<in> \<Union>C \<longleftrightarrow> (\<exists>A\<in>C. x\<in>A)"

section \<open>Subset, and standard properties\<close>

definition subset :: "i \<Rightarrow> i \<Rightarrow> o"  (infixl "\<subseteq>" 50) where [rewrite]:
  "A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. x\<in>B)"

lemma subset_refl [resolve]: "A \<subseteq> A" by auto2
lemma subsetD [forward]: "A \<subseteq> B \<Longrightarrow> c \<in> A \<Longrightarrow> c \<in> B" by auto2
lemma subsetI [backward, forward]: "\<forall>x\<in>A. x \<in> B \<Longrightarrow> A \<subseteq> B" by auto2
setup {* add_fixed_sc ("Set.subsetI@back", 500) *}
setup {* del_prfstep_thm @{thm subset_def} *}

lemma subset_trans [forward,backward1,backward2]:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> C \<Longrightarrow> A \<subseteq> C" by auto2
lemma extension_subset [forward,backward1,backward2]:
  "A \<subseteq> B \<Longrightarrow> B \<subseteq> A \<Longrightarrow> A = B" by auto2
lemma subset_nonempty [forward,backward2]:
  "A \<subseteq> B \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> B \<noteq> \<emptyset>" by auto2

section \<open>Axiom of power set\<close>

axiomatization Pow :: "i \<Rightarrow> i" where
  power [rewrite]: "x \<in> Pow(S) \<longleftrightarrow> x \<subseteq> S"

lemma PowI [typing2]: "x \<subseteq> S \<Longrightarrow> x \<in> Pow(S)" by auto2

(* Cantor's theorem *)
lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) \<noteq> S"
@proof
  @let "S = {x \<in> A. x \<notin> b(x)}"
  @have "\<forall>x\<in>A. b(x) \<noteq> S" @with @case "x \<in> b(x)" @end
@qed

section \<open>General intersection\<close>

definition Inter :: "i \<Rightarrow> i"  ("\<Inter>_" [90] 90) where [rewrite]:
  "\<Inter>(A) = { x \<in> \<Union>(A). \<forall>y\<in>A. x\<in>y}"
setup {* register_wellform_data ("\<Inter>(A)", ["A \<noteq> \<emptyset>"]) *}
setup {* add_prfstep_check_req ("\<Inter>(A)", "A \<noteq> \<emptyset>") *}
  
(* Inter really makes sense only if A \<noteq> \<emptyset>*)
lemma Inter_iff [rewrite]:
  "A \<noteq> \<emptyset> \<Longrightarrow> x \<in> \<Inter>(A) \<longleftrightarrow> (\<forall>y\<in>A. x\<in>y)" by auto2
setup {* del_prfstep_thm @{thm Inter_def} *}

section \<open>Binary union and intersection, subtraction on sets\<close>

definition Un :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<union>" 65) where [rewrite]:
  "A \<union> B = \<Union>(Upair(A,B))"

lemma Un_iff [rewrite]: "c \<in> A \<union> B \<longleftrightarrow> (c \<in> A \<or> c \<in> B)" by auto2
setup {* add_fixed_sc ("Set.Un_iff@eqforward", 500) *}
setup {* del_prfstep_thm @{thm Un_def} *}

lemma UnD1 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> A \<Longrightarrow> c \<in> B" by auto2
lemma UnD2 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<in> A" by auto2
lemma UnI1 [typing2]: "c \<in> A \<Longrightarrow> c \<in> A \<union> B" by auto2
lemma UnI2 [typing2]: "c \<in> B \<Longrightarrow> c \<in> A \<union> B" by auto2
lemma Un_empty [forward]: "A \<union> B = \<emptyset> \<Longrightarrow> A = \<emptyset>" by auto2
lemma Un_commute: "A \<union> B = B \<union> A" by auto2
lemma Un_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)" by auto2
lemma Un_least [backward]: "A \<subseteq> D \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<union> B \<subseteq> D" by auto2

definition Int :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<inter>" 70) where [rewrite]:
  "A \<inter> B = \<Inter>(Upair(A,B))"

lemma Int_iff [rewrite]: "c \<in> A \<inter> B \<longleftrightarrow> (c \<in> A \<and> c \<in> B)" by auto2
setup {* del_prfstep_thm @{thm Int_def} *}
lemma Int_commute: "A \<inter> B = B \<inter> A" by auto2
lemma Int_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)" by auto2
lemma Int_id [rewrite]: "A \<inter> A = A" by auto2
lemma Int_lower1 [resolve]: "A \<inter> B \<subseteq> A" by auto2
lemma Int_lower2 [resolve]: "A \<inter> B \<subseteq> B" by auto2
lemma Int_subset1 [rewrite]: "A \<subseteq> B \<Longrightarrow> A \<inter> B = A" by auto2
lemma Int_subset2 [rewrite]: "A \<subseteq> B \<Longrightarrow> B \<inter> A = A" by auto2

definition Diff :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<midarrow>" 65) where Diff_def[rewrite]:
  "A \<midarrow> B = {x \<in> A. x \<notin> B}"
lemma Diff_iff [rewrite]: "c \<in> A \<midarrow> B \<longleftrightarrow> (c \<in> A \<and> c \<notin> B)" by auto2
setup {* del_prfstep_thm @{thm Diff_def} *}

lemma diff_subset [resolve]: "A \<midarrow> B \<subseteq> A" by auto2

lemma diff_empty [forward]: "A \<midarrow> B = \<emptyset> \<Longrightarrow> A \<subseteq> B"
@proof
  @have "\<forall>x\<in>A. x \<in> B" @with
    @contradiction @have "x \<in> A \<midarrow> B"
  @end
@qed

lemma diff_double [rewrite]: "B \<subseteq> A \<Longrightarrow> A \<midarrow> (A \<midarrow> B) = B" by auto2

lemma compl_eq: "E\<midarrow>A = E\<midarrow>B \<Longrightarrow> A \<subseteq> E \<Longrightarrow> B \<subseteq> E \<Longrightarrow> A = B"
@proof
  @have "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B" @with
    @case "x \<in> A" @with @have "x \<notin> E\<midarrow>A" @end
    @case "x \<in> B" @with @have "x \<notin> E\<midarrow>B" @end
  @end 
@qed
setup {* add_forward_prfstep_cond @{thm compl_eq}
  [with_cond "?A \<noteq> ?B", with_filt (order_filter "A" "B")] *}

lemma inter_compl1 [rewrite]: "(X \<midarrow> A) \<inter> A = \<emptyset>" by auto2
lemma inter_compl2 [rewrite]: "A \<inter> (X \<midarrow> A) = \<emptyset>" by auto2
lemma union_compl1 [rewrite]: "A \<subseteq> X \<Longrightarrow> A \<union> (X \<midarrow> A) = X" by auto2
lemma union_compl2 [rewrite]: "A \<subseteq> X \<Longrightarrow> (X \<midarrow> A) \<union> A = X" by auto2
lemma Int_empty1 [forward]: "A \<inter> B = \<emptyset> \<Longrightarrow> x \<in> A \<Longrightarrow> x \<notin> B"
  @proof @contradiction @have "x \<in> A \<inter> B" @qed
lemma Int_empty2 [forward]: "A \<inter> B = \<emptyset> \<Longrightarrow> x \<in> B \<Longrightarrow> x \<notin> A" by auto2

section \<open>Strict subsets\<close>

definition strict_subset :: "i \<Rightarrow> i \<Rightarrow> o" (infixl "\<subset>" 50) where [rewrite]:
  "A \<subset> B \<longleftrightarrow> (A \<subseteq> B \<and> A \<noteq> B)"

section \<open>Cons, notation for finite sets\<close>

definition cons :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "cons(a, A) = Upair(a,a) \<union> A"

nonterminal "is"
syntax
  "" :: "i \<Rightarrow> is"  ("_")
  "_Enum" :: "[i, is] \<Rightarrow> is"  ("_,/ _")
  "_Finset" :: "is \<Rightarrow> i"  ("{(_)}")
translations
  "{x, xs}" == "CONST cons(x, {xs})"
  "{x}" == "CONST cons(x, \<emptyset>)"

lemma cons_iff: "a \<in> cons(b, A) \<longleftrightarrow> (a = b \<or> a \<in> A)" by auto2
setup {* add_rewrite_rule_cond @{thm cons_iff}
  [with_cond "?a \<noteq> ?b", with_cond "?A \<noteq> \<emptyset>"] *}
lemma mem_singleton [rewrite]: "a \<in> {b} \<longleftrightarrow> a = b" by auto2
lemma not_mem_singleton: "a \<noteq> b \<Longrightarrow> a \<notin> {b}" by auto2
setup {* add_forward_prfstep_cond @{thm not_mem_singleton} [with_term "{?b}"] *}
theorem mem_cons [typing2]: "a \<in> cons(a,S)" by auto2
setup {* del_prfstep_thm @{thm cons_def} *}

theorem subset_cons: "S \<subseteq> cons(a,S)" by auto2
setup {* add_forward_prfstep_cond @{thm subset_cons}
  [with_term "cons(?a,?S)", with_cond "?S \<noteq> \<emptyset>", with_cond "?S \<noteq> {?b}"] *}

theorem mem_cons2 [typing2]: "b \<in> {a,b}" by auto2

lemma Union_singleton [rewrite]: "\<Union>{a} = a" by auto2
lemma singleton_subset [backward]: "x \<in> X \<Longrightarrow> {x} \<subseteq> X" by auto2
lemma diff_singleton_not_mem [rewrite]: "a \<notin> X \<Longrightarrow> X \<midarrow> {a} = X" by auto2
lemma singleton_eq_iff [forward]: "{a} = {b} \<Longrightarrow> a = b" by auto2
lemma cons_nonempty [resolve]: "cons(a, b) \<noteq> \<emptyset>" by auto2
lemma sub_singleton_empty [forward]: "X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> {a} \<Longrightarrow> X = {a}" by auto2
lemma cons_mem [rewrite]: "a \<in> X \<Longrightarrow> cons(a,X) = X" by auto2
lemma cons_minus [rewrite]: "a \<notin> S \<Longrightarrow> cons(a,S) \<midarrow> {a} = S" by auto2

definition succ :: "i \<Rightarrow> i" where [rewrite]:
  "succ(i) = cons(i, i)"

section \<open>Axiom of replacement\<close>

axiomatization Replace :: "[i, i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> i" where replacement [rewrite]:
  "\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z \<Longrightarrow> b \<in> Replace(A,P) \<longleftrightarrow> (\<exists>x\<in>A. P(x,b))"
setup {* add_prfstep_check_req ("Replace(A,P)", "\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z") *}

section \<open>Definite description\<close>

definition The :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "THE " 10) where [rewrite]:
  "(THE x. P(x)) = \<Union>(Replace({\<emptyset>}, \<lambda>x y. P(y)))"

(* When encountering THE x. P(x), first show \<exists>!x. P(x), then can conclude
   THE x. P(x) satisfies P. *)
setup {* add_prfstep_check_req ("THE x. P(x)", "\<exists>!x. P(x)") *}
lemma theI' [forward]: "\<exists>!x. P(x) \<Longrightarrow> P (THE x. P(x))"
  @proof @obtain "a" where "P(a)" @have "(THE x. P(x)) = a" @qed

(* When trying to show (THE x. P(x)) = a, there is an alternative,
   since because we already know term a satisfies predicate P. *)
lemma the_equality [backward]: "\<forall>y. P(y) \<longrightarrow> y = a \<Longrightarrow> P(a) \<Longrightarrow> (THE x. P(x)) = a" by auto2
setup {* del_prfstep_thm @{thm The_def} *}

section \<open>Ordered pairs\<close>

definition Pair :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "Pair(a,b) = {{a}, {a,b}}"

definition fst :: "i \<Rightarrow> i" where [rewrite]:
  "fst(p) = (THE a. \<exists>b. p = Pair(a, b))"

definition snd :: "i \<Rightarrow> i" where [rewrite]:
  "snd(p) = (THE b. \<exists>a. p = Pair(a, b))"

(* For pattern-matching *)
definition split :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}" where
  "split(c) \<equiv> \<lambda>p. c(fst(p), snd(p))"
setup {* Normalizer.add_rewr_normalizer ("rewr_split", @{thm split_def}) *}

(* Patterns -- extends pre-defined type "pttrn" used in abstractions *)
nonterminal patterns
syntax
  "_pattern"  :: "patterns => pttrn"         ("\<langle>_\<rangle>")
  ""          :: "pttrn => patterns"         ("_")
  "_patterns" :: "[pttrn, patterns] => patterns"  ("_,/_")
  "_Tuple"    :: "[i, is] => i"              ("\<langle>(_,/ _)\<rangle>")
translations
  "\<langle>x, y, z\<rangle>"   == "\<langle>x, \<langle>y, z\<rangle>\<rangle>"
  "\<langle>x, y\<rangle>"      == "CONST Pair(x, y)"
  "\<lambda>\<langle>x,y,zs\<rangle>.b" == "CONST split(\<lambda>x \<langle>y,zs\<rangle>.b)"
  "\<lambda>\<langle>x,y\<rangle>.b"    == "CONST split(\<lambda>x y. b)"

lemma pair_eqD [forward]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> a = c \<and> b = d" by auto2
lemma pair_eqI: "a = c \<Longrightarrow> b = d \<Longrightarrow> \<langle>a,b\<rangle> = \<langle>c,d\<rangle>" by auto2
setup {* add_backward_prfstep_cond @{thm pair_eqI} [with_cond "?a \<noteq> ?c", with_cond "?b \<noteq> ?d"] *}
lemma pair_eqI_fst [backward]: "a = c \<Longrightarrow> \<langle>a,b\<rangle> = \<langle>c,b\<rangle>" by auto2
lemma pair_eqI_snd [backward]: "b = d \<Longrightarrow> \<langle>a,b\<rangle> = \<langle>a,d\<rangle>" by auto2

setup {* del_prfstep_thm @{thm Pair_def} *}

lemma fst_conv [rewrite]: "fst(\<langle>a, b\<rangle>) = a" by auto2
setup {* del_prfstep_thm @{thm fst_def} *}

lemma snd_conv [rewrite]: "snd(\<langle>a, b\<rangle>) = b" by auto2
setup {* del_prfstep_thm @{thm snd_def} *}

section \<open>If expressions\<close>

definition If :: "[o, i, i] \<Rightarrow> i"  ("(if (_)/ then (_)/ else (_))" [10] 10)  where [rewrite]:
  "(if P then a else b) = (THE z. P \<and> z=a \<or> \<not>P \<and> z=b)"

lemma if_P [rewrite]: "P \<Longrightarrow> (if P then a else b) = a" by auto2
lemma if_not_P [rewrite]: "\<not>P \<Longrightarrow> (if P then a else b) = b" by auto2
lemma if_not_P' [rewrite]: "P \<Longrightarrow> (if \<not>P then a else b) = b" by auto2
setup {* fold add_fixed_sc (map (rpair 1) ["Set.if_P", "Set.if_not_P", "Set.if_not_P'"]) *}
setup {* del_prfstep_thm @{thm If_def} *}

setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then ?yes else ?no"},
   CreateCase @{term_pat "?cond::o"}]) *}

definition Ifb :: "[o, o, o] \<Rightarrow> o"  ("(ifb (_)/ then (_)/ else (_))" [10] 10)  where [rewrite]:
  "(ifb P then a else b) \<longleftrightarrow> (P \<and> a) \<or> (\<not>P \<and> b)"
 
lemma ifb_P [rewrite]: "P \<Longrightarrow> (ifb P then a else b) \<longleftrightarrow> a" by auto2
lemma ifb_not_P [rewrite]: "\<not>P \<Longrightarrow> (ifb P then a else b) \<longleftrightarrow> b" by auto2
lemma ifb_not_P' [rewrite]: "P \<Longrightarrow> (ifb \<not>P then a else b) \<longleftrightarrow> b" by auto2
setup {* fold add_fixed_sc (map (rpair 1) [
  "Set.ifb_P@eqforward", "Set.ifb_P@invbackward", "Set.ifb_not_P@eqforward",
  "Set.ifb_not_P@invbackward", "Set.ifb_not_P'@eqforward", "Set.ifb_not_P'@invbackward"]) *}
setup {* del_prfstep_thm @{thm Ifb_def} *}

setup {* add_gen_prfstep ("case_intro_bool1",
  [WithFact @{term_pat "ifb ?cond then ?yes else ?no"},
   CreateCase @{term_pat "?cond::o"}]) *}

setup {* add_gen_prfstep ("case_intro_bool2",
  [WithGoal @{term_pat "ifb ?cond then ?yes else ?no"},
   CreateCase @{term_pat "?cond::o"}]) *}

section \<open>Functional form of replacement\<close>

definition RepFun :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "RepFun(A,f) = Replace(A, \<lambda>x y. y = f(x))"

lemma RepFun_iff [rewrite]:
  "y \<in> RepFun(A,f) \<longleftrightarrow> (\<exists>x\<in>A. y = f(x))" by auto2
setup {* del_prfstep_thm @{thm RepFun_def} *}

syntax
  "_RepFun" :: "[i, pttrn, i] => i"  ("(1{_ ./ _ \<in> _})" [51,0,51])
translations
  "{b. x\<in>A}" \<rightleftharpoons> "CONST RepFun(A, \<lambda>x. b)"

lemma repfun_nonempty [backward]: "A \<noteq> \<emptyset> \<Longrightarrow> {b(x). x\<in>A} \<noteq> \<emptyset>"
  @proof @obtain "a \<in> A" @have "b(a) \<in> {b(x). x\<in>A}" @qed

section \<open>Parametrized union and intersection\<close>

definition UnionS :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "UnionS(I,X) = \<Union>{X(a). a\<in>I}"

definition InterS :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "InterS(I,X) = \<Inter>{X(a). a\<in>I}"
setup {* register_wellform_data ("InterS(I,X)", ["I \<noteq> \<emptyset>"]) *}
setup {* add_prfstep_check_req ("InterS(I,X)", "I \<noteq> \<emptyset>") *}

syntax
  "_UNION" :: "[pttrn, i, i] => i"  ("(3\<Union>_\<in>_./ _)" 10)
  "_INTER" :: "[pttrn, i, i] => i"  ("(3\<Inter>_\<in>_./ _)" 10)
translations
  "\<Union>a\<in>I. X" == "CONST UnionS(I, \<lambda>a. X)"
  "\<Inter>a\<in>I. X" == "CONST InterS(I, \<lambda>a. X)"

lemma UnionS_iff [rewrite]:
  "x \<in> (\<Union>a\<in>I. X(a)) \<longleftrightarrow> (\<exists>a\<in>I. x\<in>X(a))" by auto2
lemma UnionSI [typing2]:
  "x \<in> X(a) \<Longrightarrow> a \<in> I \<Longrightarrow> x \<in> (\<Union>a\<in>I. X(a))" by auto2
lemma InterS_iff [rewrite]:
  "I \<noteq> \<emptyset> \<Longrightarrow> x \<in> (\<Inter>a\<in>I. X(a)) \<longleftrightarrow> (\<forall>a\<in>I. x\<in>X(a))" by auto2
setup {* del_prfstep_thm @{thm UnionS_def} *}
setup {* del_prfstep_thm @{thm InterS_def} *}

section {* Sigma *}

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Sigma(A,B) = (\<Union>x\<in>A. \<Union>y\<in>B(x). {\<langle>x,y\<rangle>})"

lemma Sigma_iff [rewrite]:
  "\<langle>a, b\<rangle> \<in> Sigma(A, B) \<longleftrightarrow> a \<in> A \<and> b \<in> B(a)" by auto2

lemma Sigma_split: "p \<in> Sigma(A,B) \<Longrightarrow> p = \<langle>fst(p), snd(p)\<rangle>" by auto2
setup {* add_forward_prfstep_cond @{thm Sigma_split} [with_cond "?p \<noteq> \<langle>?a, ?b\<rangle>"] *}
setup {* del_prfstep_thm @{thm Sigma_def} *}

lemma fst_type: "p \<in> Sigma(A, B) \<Longrightarrow> fst(p) \<in> A" by auto2

lemma snd_type: "p \<in> Sigma(A, B) \<Longrightarrow> snd(p) \<in> B(fst(p))" by auto2

section \<open>Product set\<close>

abbreviation cart_prod :: "[i, i] \<Rightarrow> i"  (infixr "\<times>" 80) where
  "A \<times> B \<equiv> Sigma(A, \<lambda>_. B)"

lemma prod_memI: "a \<in> A \<Longrightarrow> \<forall>b\<in>B. \<langle>a,b\<rangle> \<in> A\<times>B" by auto2
setup {* add_forward_prfstep_cond @{thm prod_memI} [with_term "?A\<times>?B"] *}
setup {* add_fixed_sc ("Set.prod_memI", 500) *}

lemma prod_memI' [backward,backward1,backward2]:
  "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> \<langle>a,b\<rangle> \<in> A \<times> B" by auto2

(* Determining the two sets from the product set. *)
lemma prod_non_zero [forward]: "A \<times> B = \<emptyset> \<Longrightarrow> A = \<emptyset> \<or> B = \<emptyset>" by auto2

lemma prod_subset: "A \<subseteq> C \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<times> B \<subseteq> C \<times> D" by auto2
setup {* add_backward_prfstep_cond @{thm prod_subset} [with_cond "?A \<noteq> ?C", with_cond "?B \<noteq> ?D"] *}
lemma prod_subset1 [backward]: "B \<subseteq> D \<Longrightarrow> A \<times> B \<subseteq> A \<times> D" by auto2
lemma prod_subset2 [backward]: "A \<subseteq> C \<Longrightarrow> A \<times> B \<subseteq> C \<times> B" by auto2

lemma product_eq: "A \<times> B = C \<times> D \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> B \<noteq> \<emptyset> \<Longrightarrow> A = C \<and> B = D" by auto2
setup {* add_forward_prfstep_cond @{thm product_eq} [with_cond "?A \<noteq> ?C", with_cond "?B \<noteq> ?D"] *}
lemma product_eq1 [forward]: "A \<times> B = A \<times> D \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> B = D" by auto2
lemma product_eq2 [forward]: "A \<times> B = C \<times> B \<Longrightarrow> B \<noteq> \<emptyset> \<Longrightarrow> A = C" by auto2

lemma prod_inter [rewrite_back]: "(X \<times> Y) \<inter> (A \<times> B) = (X \<inter> A) \<times> (Y \<inter> B)" by auto2
setup {* add_rewrite_rule_cond @{thm prod_inter} [with_cond "?X \<noteq> ?A", with_cond "?Y \<noteq> ?B"] *}
lemma prod_inter1 [rewrite]: "(X \<times> Y) \<inter> (X \<times> B) = X \<times> (Y \<inter> B)" by auto2
lemma prod_inter2 [rewrite]: "(X \<times> Y) \<inter> (A \<times> Y) = (X \<inter> A) \<times> Y" by auto2

lemma prod_empty1 [rewrite]: "\<emptyset> \<times> A = \<emptyset>" by auto2
lemma prod_empty2 [rewrite]: "A \<times> \<emptyset> = \<emptyset>" by auto2
lemma prod_union1 [rewrite_bidir]: "X \<times> A \<union> X \<times> B = X \<times> (A \<union> B)" by auto2
lemma prod_union2 [rewrite_bidir]: "A \<times> X \<union> B \<times> X = (A \<union> B) \<times> X" by auto2
lemma prod_diff1 [rewrite]: "X \<times> A \<midarrow> X \<times> B = X \<times> (A \<midarrow> B)" by auto2
lemma prod_diff2 [rewrite]: "A \<times> X \<midarrow> B \<times> X = (A \<midarrow> B) \<times> X" by auto2

end
