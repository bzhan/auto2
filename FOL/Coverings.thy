theory Coverings
imports Functions
begin

section {* Coverings *}  (* Bourbaki II.4.6 *)

definition is_covering :: "i \<Rightarrow> i \<Rightarrow> o" where is_covering_def [rewrite]:
  "is_covering(E,X) \<longleftrightarrow> (\<forall>x\<in>E. \<exists>a\<in>source(X). x \<in> X`a)"

(* Y is finer than X *)
definition finer_covering :: "i \<Rightarrow> i \<Rightarrow> o" where finer_covering_def [rewrite]:
  "finer_covering(Y,X) \<longleftrightarrow> (\<forall>b\<in>source(Y). \<exists>a\<in>source(X). Y`b \<subseteq> X`a)"

lemma finer_covering_trans:
  "finer_covering(Z,Y) \<Longrightarrow> finer_covering(Y,X) \<Longrightarrow> finer_covering(Z,X)" by auto2

lemma subset_covering:
  "is_function(X) \<Longrightarrow> is_covering(E,X) \<Longrightarrow> J \<subseteq> source(X) \<Longrightarrow> E \<subseteq> (\<Union>a\<in>J. X`a) \<Longrightarrow>
   is_covering(E, func_restrict(X,J))" by auto2

lemma subset_is_finer:
  "is_function(X) \<Longrightarrow> J \<subseteq> source(X) \<Longrightarrow> finer_covering(func_restrict(X,J),X)" by auto2

definition join_covering :: "i \<Rightarrow> i \<Rightarrow> i" where join_covering_def [rewrite]:
  "join_covering(X,Y) = (\<lambda>p\<in>source(X)\<times>source(Y). X`fst(p) \<inter> Y`snd(p)\<in>target(X))"

lemma join_is_covering: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> is_covering(E,X) \<Longrightarrow>
  is_covering(E,Y) \<Longrightarrow> is_covering(E, join_covering(X,Y))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>E. \<exists>p\<in>source(X)\<times>source(Y). x \<in> X`fst(p) \<inter> Y`snd(p)" WITH (
      CHOOSE "a\<in>source(X), x\<in>X`a" THEN CHOOSE "b\<in>source(Y), x\<in>Y`b" THEN
      HAVE "\<langle>a,b\<rangle>\<in>source(X)\<times>source(Y)")) *})

lemma join_is_finer: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow>
  finer_covering(join_covering(X,Y),X) \<and> finer_covering(join_covering(X,Y),Y)" by auto2

lemma join_is_finer_maximal: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> Z \<in> L \<rightarrow> Pow(E) \<Longrightarrow>
  finer_covering(Z,X) \<Longrightarrow> finer_covering(Z,Y) \<Longrightarrow> finer_covering(Z,join_covering(X,Y))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>c\<in>L. \<exists>p\<in>I\<times>K. Z`c \<subseteq> join_covering(X,Y)`p" WITH (
      CHOOSE "a\<in>I, Z`c \<subseteq> X`a" THEN CHOOSE "b\<in>K, Z`c \<subseteq> Y`b" THEN
      HAVE "\<langle>a,b\<rangle> \<in> I\<times>K")) *})

lemma image_covering: "surjective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
  is_covering(B, \<lambda>a\<in>I. (f``(X`a))\<in>Pow(B))" by auto2

lemma vImage_covering: "g \<in> C \<rightarrow> A \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
  is_covering(C, \<lambda>a\<in>I. (g -`` (X`a))\<in>Pow(C))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "Y, Y = (\<lambda>a\<in>I. (g -`` (X`a))\<in>Pow(C))" THEN
    HAVE "\<forall>x\<in>C. \<exists>p\<in>I. x \<in> Y ` p" WITH CHOOSE "a\<in>I, g`x \<in> a") *})

lemma product_covering: "X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(B) \<Longrightarrow>
  is_covering(A,X) \<Longrightarrow> is_covering(B,Y) \<Longrightarrow>
  is_covering(A\<times>B, \<lambda>p\<in>I\<times>K. (X`fst(p) \<times> Y`snd(p))\<in>Pow(A\<times>B))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "Z, Z = (\<lambda>p\<in>I\<times>K. (X`fst(p) \<times> Y`snd(p))\<in>Pow(A\<times>B))" THEN
    HAVE "Z \<in> I\<times>K \<rightarrow> Pow(A\<times>B)" THEN
    HAVE "\<forall>a\<in>I. \<forall>b\<in>K. Z`\<langle>a,b\<rangle> = X`a \<times> Y`b") *})  (* Why is this line necessary? *)

lemma glue_fun_on_covering [backward1]: "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  \<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b) \<Longrightarrow>
  \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<exists>f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D. (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)" WITH (
      CHOOSE "f, f = (\<lambda>x\<in>(\<Union>a\<in>I. X`a). (F(SOME a\<in>I. x\<in>X`a) ` x) \<in> D)")) *})

section {* Partitions *}  (* Bourbaki II.4.7 *)

definition set_disjoint :: "i \<Rightarrow> i \<Rightarrow> o" where disjoint_def [rewrite]:
  "set_disjoint(A,B) \<longleftrightarrow> (A \<inter> B = \<emptyset>)"

lemma singleton_disjoint [backward]: "a \<noteq> b \<Longrightarrow> set_disjoint({a}, {b})" by auto2

lemma set_disjoint_neq [forward]: "set_disjoint(A,B) \<Longrightarrow> x \<in> A \<Longrightarrow> \<forall>y\<in>B. x \<noteq> y"
  by (tactic {* auto2s_tac @{context} (HAVE "x \<in> A \<inter> B") *})

definition mutually_disjoint :: "i \<Rightarrow> o" where mutually_disjoint_def [rewrite]:
  "mutually_disjoint(X) \<longleftrightarrow> (\<forall>a\<in>source(X). \<forall>b\<in>source(X). a \<noteq> b \<longrightarrow> set_disjoint(X`a, X`b))"

lemma vImage_set_disjoint [backward2]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> X \<subseteq> B \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> set_disjoint(X,Y) \<Longrightarrow> set_disjoint(f -`` X, f -`` Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "b, b \<in> (f -`` X) \<inter> (f -`` Y)" THEN HAVE "f ` b \<in> X \<inter> Y") *})

lemma vImage_mutually_disjoint [backward2]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> Y \<in> I \<rightarrow> Pow(B) \<Longrightarrow> mutually_disjoint(Y) \<Longrightarrow>
   mutually_disjoint(\<lambda>a\<in>I. (f -`` (Y`a))\<in>Pow(A))" by auto2

lemma glue_fun_on_mut_disj [backward1]: "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  mutually_disjoint(X) \<Longrightarrow> \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b)" WITH CASE "a = b") *})

(* For partitions, usually definition in terms of sets is more convenient *)
definition mutually_disjoint_sets :: "i \<Rightarrow> o" where mutually_disjoint_sets_def [rewrite]:
  "mutually_disjoint_sets(X) \<longleftrightarrow> (\<forall>a\<in>X. \<forall>b\<in>X. a \<noteq> b \<longrightarrow> set_disjoint(a,b))"

definition is_partition_sets :: "i \<Rightarrow> i \<Rightarrow> o" where is_partition_sets_def [rewrite]:
  "is_partition_sets(E,X) \<longleftrightarrow> (E = \<Union>X \<and> mutually_disjoint_sets(X))"

lemma singletons_is_partition: "is_partition_sets(E, {{x}. x\<in>E})"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>E. x \<in> \<Union>{{x}. x \<in> E}" WITH HAVE "x \<in> {x}") *})

(* Version for a family of sets *)
definition is_partition :: "i \<Rightarrow> i \<Rightarrow> o" where is_partition_def [rewrite]:
  "is_partition(E,X) \<longleftrightarrow> (E = (\<Union>a\<in>source(X). X`a) \<and> mutually_disjoint(X))"

lemma glue_fun_on_partition [backward1]:
  "is_function(X) \<Longrightarrow> \<forall>a\<in>source(X). F(a) \<in> X`a \<rightarrow> D \<Longrightarrow> is_partition(E,X) \<Longrightarrow>
   \<exists>!f. f\<in>E\<rightarrow>D \<and> (\<forall>a\<in>source(X). \<forall>b\<in>X`a. f`b = F(a)`b)" by auto2

(* X is a partition of E, indexed by I. F is a meta-family of functions indexed
   by I, where each F(a) is a function X(a)\<rightarrow>D. Get the glued map E\<rightarrow>D. *)
definition glue_partition_fun :: "[i, i, i, i \<Rightarrow> i] \<Rightarrow> i" where glue_partition_fun_def [rewrite]:
  "glue_partition_fun(E,X,D,F) = (THE f. f\<in>E\<rightarrow>D \<and> (\<forall>a\<in>source(X). \<forall>b\<in>X`a. f`b = F(a)`b))"

lemma glue_partition_fun_prop:
  "is_function(X) \<Longrightarrow> \<forall>a\<in>source(X). F(a) \<in> X`a \<rightarrow> D \<Longrightarrow> is_partition(E,X) \<Longrightarrow>
   glue_partition_fun(E,X,D,F) \<in> E\<rightarrow>D \<and>
   (\<forall>a\<in>source(X). \<forall>b\<in>X`a. glue_partition_fun(E,X,D,F)`b = F(a)`b)" by auto2
setup {* add_forward_prfstep_cond @{thm glue_partition_fun_prop} [with_term "glue_partition_fun(?E,?X,?D,?F)"] *}
setup {* add_gen_prfstep ("glue_partition_fun_case",
  [WithTerm @{term_pat "glue_partition_fun(?E,?X,?D,?F)"},
   CreateConcl @{term_pat "\<forall>a\<in>source(?X). ?F(a) \<in> ?X`a \<rightarrow> ?D"}]) *}
setup {* del_prfstep_thm @{thm glue_partition_fun_def} *}

section {* Sum of a family of sets *}  (* Bourbaki II.4.8 *)

(* Version of Sigma for object functions *)
definition Sigma' :: "i \<Rightarrow> i" where Sigma'_def [rewrite]:
  "Sigma'(X) = Sigma(source(X), \<lambda>a. (X`a))"

lemma Sigma'_iff [rewrite]:
  "is_function(X) \<Longrightarrow> \<langle>a, b\<rangle> \<in> Sigma'(X) \<longleftrightarrow> (a \<in> source(X) \<and> b \<in> X`a)" by auto2

lemma Sigma'_split: "p \<in> Sigma'(X) \<Longrightarrow> p = \<langle>fst(p), snd(p)\<rangle>" by auto2
setup {* add_forward_prfstep_cond @{thm Sigma'_split} [with_cond "?p \<noteq> \<langle>?a, ?b\<rangle>"] *}
setup {* del_prfstep_thm @{thm Sigma'_def} *}

definition union_to_sum_fun :: "i \<Rightarrow> i" where union_to_sum_fun [rewrite]:
  "union_to_sum_fun(X) = (\<lambda>p\<in>Sigma'(X). snd(p)\<in>(\<Union>a\<in>source(X). X`a))"

lemma union_to_sum_is_function [typing]:
  "is_function(X) \<Longrightarrow> union_to_sum_fun(X) \<in> Sigma'(X) \<rightarrow> (\<Union>a\<in>source(X). X`a)" by auto2

lemma union_to_sum_is_surj [forward]:
  "is_function(X) \<Longrightarrow> surjective(union_to_sum_fun(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "U, U = (\<Union>a\<in>source(X). X`a)" THEN
    HAVE "\<forall>x\<in>U. \<exists>p\<in>Sigma'(X). union_to_sum_fun(X) ` p = x" WITH (
      CHOOSE "a\<in>source(X), x \<in> X`a" THEN HAVE "\<langle>a,x\<rangle> \<in> Sigma'(X)")) *}) 

lemma union_to_sum_is_bij:
  "mutually_disjoint(X) \<Longrightarrow> is_function(X) \<Longrightarrow> union_to_sum_fun(X) \<in> Sigma'(X) \<cong> (\<Union>a\<in>source(X). X`a)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f = union_to_sum_fun(X)" THEN
    HAVE "\<forall>p\<in>Sigma'(X). \<forall>q\<in>Sigma'(X). p \<noteq> q \<longrightarrow> f ` p \<noteq> f ` q" WITH (
      CASE "fst(p) = fst(q)")) *})

end
