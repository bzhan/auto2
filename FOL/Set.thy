theory Set
imports Logic_FOL
begin

section \<open>Axiom of extension\<close>

axiomatization where
  extension: "\<forall>z. z \<in> x \<longleftrightarrow> z \<in> y \<Longrightarrow> x = y"

setup {* add_backward_prfstep_cond @{thm extension} [with_filt (order_filter "x" "y")] *}
setup {* add_fixed_sc ("Set.extension@back", 500) *}

section \<open>Axiom of empty set\<close>

axiomatization Empty_set :: "i"  ("\<emptyset>") where
  Empty_set_iff [resolve]: "x \<notin> \<emptyset>"

lemma nonempty_mem [backward]: "A \<noteq> \<emptyset> \<Longrightarrow> \<exists>x. x \<in> A" by auto2

section \<open>Axiom schema of specification\<close>

axiomatization Collect :: "[i, i \<Rightarrow> o] \<Rightarrow> i" where
  Collect_iff [rewrite]: "x \<in> Collect(A,P) \<longleftrightarrow> (x \<in> A \<and> P(x))"

syntax
  "_Collect" :: "[pttrn, i, o] \<Rightarrow> i"  ("(1{_ \<in> _ ./ _})")
translations
  "{x\<in>A. P}" \<rightleftharpoons> "CONST Collect(A, \<lambda>x. P)"

section \<open>Axiom of pairing\<close>

axiomatization Upair :: "[i, i] \<Rightarrow> i" where
  Upair_iff [rewrite]: "x \<in> Upair(y,z) \<longleftrightarrow> (x = y \<or> x = z)"

lemma Upair_nonempty [resolve]: "Upair(a,b) \<noteq> \<emptyset>"
  by (tactic {* auto2s_tac @{context} (HAVE "a \<in> Upair(a,b)") *})

section \<open>Axiom of union\<close>

axiomatization Union :: "i \<Rightarrow> i"  ("\<Union>_" [90] 90) where
  Union_iff [rewrite]: "A \<in> \<Union>(C) \<longleftrightarrow> (\<exists>B\<in>C. A\<in>B)"

section \<open>Subset, and standard properties\<close>

definition subset :: "i \<Rightarrow> i \<Rightarrow> o"  (infixl "\<subseteq>" 50) where subset_def [rewrite]:
  "A \<subseteq> B \<longleftrightarrow> (\<forall>x\<in>A. x\<in>B)"

lemma subset_refl [resolve]: "A \<subseteq> A" by auto2
lemma subsetD [forward]: "A \<subseteq> B \<Longrightarrow> c \<in> A \<Longrightarrow> c \<in> B" by auto2
lemma subsetI [backward, resolve]: "\<forall>x\<in>A. x \<in> B \<Longrightarrow> A \<subseteq> B" by auto2
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
  Pow_iff [rewrite]: "x \<in> Pow(S) \<longleftrightarrow> x \<subseteq> S"

(* Cantor's theorem *)
lemma cantor: "\<exists>S \<in> Pow(A). \<forall>x\<in>A. b(x) \<noteq> S"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "S, S = { x\<in>A. x \<notin> b(x) }" THEN
     HAVE "\<forall>x\<in>A. b(x) \<noteq> S" WITH CASE "x \<in> b(x)") *})

section \<open>General intersection\<close>

definition Inter :: "i \<Rightarrow> i"  ("\<Inter>_" [90] 90) where Inter_def [rewrite]:
  "\<Inter>(A) = { x \<in> \<Union>(A). \<forall>y\<in>A. x\<in>y}"

(* Inter really makes sense only if A \<noteq> \<emptyset>*)
lemma Inter_iff [rewrite]:
  "A \<noteq> \<emptyset> \<Longrightarrow> x \<in> \<Inter>(A) \<longleftrightarrow> (\<forall>y\<in>A. x\<in>y)" by auto2

setup {* add_gen_prfstep ("Inter_case",
  [WithTerm @{term_pat "\<Inter>(?A)"}, CreateConcl @{term_pat "?A \<noteq> \<emptyset>"}]) *}

setup {* del_prfstep_thm @{thm Inter_def} *}

section \<open>Binary union and intersection, subtraction on sets\<close>

definition Un :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<union>" 65) where Un_def [rewrite]:
  "A \<union> B = \<Union>(Upair(A,B))"

lemma Un_iff [rewrite]: "c \<in> A \<union> B \<longleftrightarrow> (c \<in> A \<or> c \<in> B)" by auto2
setup {* add_fixed_sc ("Set.Un_iff@eqforward", 500) *}
setup {* del_prfstep_thm @{thm Un_def} *}

lemma UnD1 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> A \<Longrightarrow> c \<in> B" by auto2
lemma UnD2 [forward]: "c \<in> A \<union> B \<Longrightarrow> c \<notin> B \<Longrightarrow> c \<in> A" by auto2
lemma Un_empty [forward]: "A \<union> B = \<emptyset> \<Longrightarrow> A = \<emptyset>" by auto2
lemma Un_commute: "A \<union> B = B \<union> A" by auto2
lemma Un_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)" by auto2
lemma Un_least [backward]: "A \<subseteq> D \<Longrightarrow> B \<subseteq> D \<Longrightarrow> A \<union> B \<subseteq> D" by auto2

definition Int :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "\<inter>" 70) where Int_def [rewrite]:
  "A \<inter> B = \<Inter>(Upair(A,B))"

lemma Int_iff [rewrite]: "c \<in> A \<inter> B \<longleftrightarrow> (c \<in> A \<and> c \<in> B)" by auto2
setup {* del_prfstep_thm @{thm Int_def} *}
lemma Int_commute: "A \<inter> B = B \<inter> A" by auto2
lemma Int_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)" by auto2
lemma Int_lower1 [resolve]: "A \<inter> B \<subseteq> A" by auto2
lemma Int_lower2 [resolve]: "A \<inter> B \<subseteq> B" by auto2

definition Diff :: "i \<Rightarrow> i \<Rightarrow> i"  (infixl "-" 65) where Diff_def[rewrite]:
  "A - B = {x \<in> A. x \<notin> B}"
lemma Diff_iff [rewrite]: "c \<in> A - B \<longleftrightarrow> (c \<in> A \<and> c \<notin> B)" by auto2
setup {* del_prfstep_thm @{thm Diff_def} *}
lemma diff_subset [resolve]: "A - B \<subseteq> A" by auto2
lemma diff_empty [forward]: "A - B = \<emptyset> \<Longrightarrow> A \<subseteq> B"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "x\<in>A, x \<notin> B" THEN HAVE "x \<in> A - B") *})
lemma compl_eq: "E-A = E-B \<Longrightarrow> A \<subseteq> E \<Longrightarrow> B \<subseteq> E \<Longrightarrow> A = B"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B" WITH (
      (CASE "x \<in> A" WITH HAVE "x \<notin> E-A") THEN
      (CASE "x \<in> B" WITH HAVE "x \<notin> E-B"))) *})
setup {* add_forward_prfstep_cond @{thm compl_eq}
  [with_cond "?A \<noteq> ?B", with_filt (order_filter "A" "B")] *}

section \<open>Strict subsets\<close>

definition strict_subset :: "i \<Rightarrow> i \<Rightarrow> o" (infixl "\<subset>" 50) where strict_subset_def [rewrite]:
  "A \<subset> B \<longleftrightarrow> (A \<subseteq> B \<and> A \<noteq> B)"

section \<open>Cons, notation for finite sets\<close>

definition cons :: "[i, i] \<Rightarrow> i" where cons_def [rewrite]:
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
theorem mem_cons [typing2]: "a \<in> cons(a,S)" by auto2
setup {* del_prfstep_thm @{thm cons_def} *}

theorem subset_cons: "S \<subseteq> cons(a,S)" by auto2
setup {* add_forward_prfstep_cond @{thm subset_cons}
  [with_term "cons(?a,?S)", with_cond "?S \<noteq> \<emptyset>", with_cond "?S \<noteq> {?b}"] *}

theorem mem_cons2 [typing2]: "b \<in> {a,b}" by auto2

lemma Union_singleton [rewrite]: "\<Union>{a} = a" by auto2
lemma singleton_eq_iff [forward]: "{a} = {b} \<Longrightarrow> a = b" by auto2
lemma cons_nonempty [resolve]: "cons(a, b) \<noteq> \<emptyset>" by auto2
lemma sub_singleton_empty [forward]: "X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> {a} \<Longrightarrow> X = {a}" by auto2

section \<open>Axiom of replacement\<close>

definition functional_rel :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> o" where functional_rel [rewrite]:
  "functional_rel(A,P) \<longleftrightarrow> (\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z)"

axiomatization Replace :: "[i, i \<Rightarrow> i \<Rightarrow> o] \<Rightarrow> i" where replacement [rewrite]:
  "functional_rel(A,P) \<Longrightarrow> (b \<in> Replace(A,P) \<longleftrightarrow> (\<exists>x\<in>A. P(x,b)))"

setup {* add_gen_prfstep ("Replace_case",
  [WithTerm @{term_pat "Replace(?A,?P)"},
   CreateConcl @{term_pat "functional_rel(?A,?P)"}]) *}

syntax
  "_Replace"  :: "[pttrn, pttrn, i, o] => i"  ("(1{_ ./ _ \<in> _, _})")
translations
  "{y. x\<in>A, Q}" \<rightleftharpoons> "CONST Replace(A, \<lambda>x y. Q)"

section \<open>Definite description\<close>

definition The :: "(i \<Rightarrow> o) \<Rightarrow> i"  (binder "THE " 10) where the_def [rewrite]:
  "The(P) = (\<Union>({y. x \<in> {\<emptyset>}, P(y)}))"

(* When encountering THE x. P(x), first show \<exists>!x. P(x), then can conclude
   THE x. P(x) satisfies P. *)
setup {* add_gen_prfstep ("THE_case",
  [WithTerm @{term_pat "THE x. (?P::i\<Rightarrow>o)(x)"}, CreateConcl @{term_pat "\<exists>!x. (?P::i\<Rightarrow>o)(x)"}]) *}
lemma theI' [forward]: "\<exists>!x. P(x) \<Longrightarrow> P (THE x. P(x))"
  by (tactic {* auto2s_tac @{context} (CHOOSE "a, P(a)" THEN HAVE "(THE x. P(x)) = a") *})

(* When trying to show (THE x. P(x)) = a, there is an alternative,
   since because we already know term a satisfies predicate P. *)
lemma the_equality [backward]: "\<forall>y. P(y) \<longrightarrow> y = a \<Longrightarrow> P(a) \<Longrightarrow> (THE x. P(x)) = a" by auto2
setup {* del_prfstep_thm @{thm the_def} *}

section \<open>Ordered pairs\<close>

definition Pair :: "[i, i] \<Rightarrow> i" where Pair_def [rewrite]:
  "Pair(a,b) = {{a,a}, {a,b}}"

definition fst :: "i \<Rightarrow> i" where fst_def [rewrite]:
  "fst(p) = (THE a. \<exists>b. p = Pair(a, b))"

definition snd :: "i \<Rightarrow> i" where snd_def [rewrite]:
  "snd(p) = (THE b. \<exists>a. p = Pair(a, b))"

(* For pattern-matching *)
definition split :: "[[i, i] \<Rightarrow> 'a, i] \<Rightarrow> 'a::{}" where
  "split(c) \<equiv> \<lambda>p. c(fst(p), snd(p))"

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

lemma doubleton_eq1 [forward]: "{a,b} = {c,d} \<Longrightarrow> a \<noteq> c \<Longrightarrow> a = d \<and> b = c" by auto2
lemma doubleton_eq2 [forward]: "{a,b} = {c,d} \<Longrightarrow> a = c \<Longrightarrow> b = d" by auto2
setup {* add_gen_prfstep ("doubleton_eq_case",
  [WithFact @{term_pat "{?a,?b}={?c,?d}"}, Filter (neq_filter "a" "c"),
   Filter (order_filter "a" "c"),
   CreateCase @{term_pat "?a = (?c::i)"}]) *}

(* \<emptyset> is used as a default value later. *)
lemma Empty_not_pair [resolve]: "\<emptyset> \<noteq> \<langle>a,b\<rangle>" by auto2

lemma Pair_iff [forward]: "\<langle>a, b\<rangle> = \<langle>c, d\<rangle> \<Longrightarrow> a = c \<and> b = d" by auto2
setup {* del_prfstep_thm @{thm Pair_def} *}

lemma fst_conv [rewrite]: "fst(\<langle>a, b\<rangle>) = a"
  by (tactic {* auto2s_tac @{context} (HAVE "\<exists>y. \<langle>a, b\<rangle> = \<langle>a, y\<rangle>") *})
setup {* del_prfstep_thm @{thm fst_def} *}

lemma snd_conv [rewrite]: "snd(\<langle>a, b\<rangle>) = b"
  by (tactic {* auto2s_tac @{context} (HAVE "\<exists>x. \<langle>a, b\<rangle> = \<langle>x, b\<rangle>") *})
setup {* del_prfstep_thm @{thm snd_def} *}

section \<open>If expressions\<close>

definition If :: "[o, i, i] \<Rightarrow> i"  ("(if (_)/ then (_)/ else (_))" [10] 10)  where if_def [rewrite]:
  "(if P then a else b) = (THE z. P \<and> z=a \<or> \<not>P \<and> z=b)"

lemma if_P [rewrite]: "P \<Longrightarrow> (if P then a else b) = a" by auto2
lemma if_not_P [rewrite]: "\<not>P \<Longrightarrow> (if P then a else b) = b" by auto2
lemma if_not_P' [rewrite]: "P \<Longrightarrow> (if \<not>P then a else b) = b" by auto2
setup {* del_prfstep_thm @{thm if_def} *}

setup {* add_gen_prfstep ("case_intro",
  [WithTerm @{term_pat "if ?cond then ?yes else ?no"},
   CreateCase @{term_pat "?cond::o"}]) *}

section \<open>Functional form of replacement\<close>

definition RepFun :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where RepFun_def [rewrite]:
  "RepFun(A,f) = {y. x \<in> A, y = f(x)}"

lemma RepFun_iff [rewrite]:
  "y \<in> RepFun(A,f) \<longleftrightarrow> (\<exists>x\<in>A. y = f(x))" by auto2
setup {* del_prfstep_thm @{thm RepFun_def} *}

syntax
  "_RepFun" :: "[i, pttrn, i] => i"  ("(1{_ ./ _ \<in> _})" [51,0,51])
translations
  "{b. x\<in>A}" \<rightleftharpoons> "CONST RepFun(A, \<lambda>x. b)"

lemma repfun_nonempty [backward]: "A \<noteq> \<emptyset> \<Longrightarrow> {b(x). x\<in>A} \<noteq> \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a, a \<in> A" THEN HAVE "b(a) \<in> {b(x). x\<in>A}") *})

section \<open>Parametrized union and intersection\<close>

definition UnionS :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> i" where UnionS_def [rewrite]:
  "UnionS(I,X) = \<Union>{X(a). a\<in>I}"

definition InterS :: "i \<Rightarrow> [i \<Rightarrow> i] \<Rightarrow> i" where InterS_def [rewrite]:
  "InterS(I,X) = \<Inter>{X(a). a\<in>I}"

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

setup {* add_gen_prfstep ("INT_case",
  [WithTerm @{term_pat "\<Inter>a\<in>?I. ?X(a)"}, CreateConcl @{term_pat "?I \<noteq> \<emptyset>"}]) *}

section {* Sigma *}

definition Sigma :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where Sigma_def [rewrite]:
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

lemma prod_memI: "a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> \<langle>a,b\<rangle> \<in> A\<times>B" by auto2
setup {* add_typing_rule_cond @{thm prod_memI} [with_term "?A\<times>?B"] *}

(* Determining the two sets from the product set. *)
lemma prod_non_zero [forward]: "A \<times> B = \<emptyset> \<Longrightarrow> A = \<emptyset> \<or> B = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>x\<in>A. \<forall>y\<in>B. \<langle>x,y\<rangle>\<in>A\<times>B") *})

lemma product_eq [forward]: "A \<times> B = C \<times> D \<Longrightarrow> A \<noteq> \<emptyset> \<Longrightarrow> B \<noteq> \<emptyset> \<Longrightarrow> A = C \<and> B = D"
  by (tactic {* auto2s_tac @{context}
    (HAVE "A \<times> B \<noteq> \<emptyset>" THEN HAVE "C \<noteq> \<emptyset> \<and> D \<noteq> \<emptyset>" THEN
     HAVE "\<forall>x\<in>A. \<forall>y\<in>B. \<langle>x,y\<rangle>\<in>A\<times>B" THEN
     HAVE "\<forall>x\<in>C. \<forall>y\<in>D. \<langle>x,y\<rangle>\<in>C\<times>D") *})

end
