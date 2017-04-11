theory Coverings
imports Functions
begin

section {* Coverings *}  (* Bourbaki II.4.6 *)

definition is_covering :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_covering(E,X) \<longleftrightarrow> (\<forall>x\<in>E. \<exists>a\<in>source(X). x \<in> X`a)"

(* Y is finer than X *)
definition finer_covering :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "finer_covering(Y,X) \<longleftrightarrow> (\<forall>b\<in>source(Y). \<exists>a\<in>source(X). Y`b \<subseteq> X`a)"

lemma finer_covering_trans:
  "finer_covering(Z,Y) \<Longrightarrow> finer_covering(Y,X) \<Longrightarrow> finer_covering(Z,X)" by auto2

lemma subset_covering:
  "is_function(X) \<Longrightarrow> is_covering(E,X) \<Longrightarrow> J \<subseteq> source(X) \<Longrightarrow> E \<subseteq> (\<Union>a\<in>J. X`a) \<Longrightarrow>
   is_covering(E, func_restrict(X,J))" by auto2

lemma subset_is_finer:
  "is_function(X) \<Longrightarrow> J \<subseteq> source(X) \<Longrightarrow> finer_covering(func_restrict(X,J),X)" by auto2

definition join_covering :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "join_covering(X,Y) = (\<lambda>p\<in>source(X)\<times>source(Y). X`fst(p) \<inter> Y`snd(p)\<in>target(X))"
setup {* register_wellform_data ("join_covering(X,Y)", ["target(X) = target(Y)"]) *}

lemma join_covering_is_fun [typing]:
  "is_function(X) \<Longrightarrow> is_function(Y) \<Longrightarrow> target(X) = target(Y) \<Longrightarrow> target(X) = Pow(E) \<Longrightarrow>
   join_covering(X,Y) \<in> source(X)\<times>source(Y) \<rightarrow> target(X)" by auto2

lemma join_covering_eval [rewrite]:
  "is_function(X) \<Longrightarrow> is_function(Y) \<Longrightarrow> target(X) = target(Y) \<Longrightarrow> p \<in> source(join_covering(X,Y)) \<Longrightarrow>
   target(X) = Pow(E) \<Longrightarrow> join_covering(X,Y)`p = X`fst(p) \<inter> Y`snd(p)" by auto2
setup {* del_prfstep_thm @{thm join_covering_def} *}

lemma join_is_covering: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> is_covering(E,X) \<Longrightarrow>
  is_covering(E,Y) \<Longrightarrow> is_covering(E, join_covering(X,Y))" by auto2

lemma join_is_finer: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow>
  finer_covering(join_covering(X,Y),X) \<and> finer_covering(join_covering(X,Y),Y)" by auto2

lemma join_is_finer_maximal: "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> Z \<in> L \<rightarrow> Pow(E) \<Longrightarrow>
  finer_covering(Z,X) \<Longrightarrow> finer_covering(Z,Y) \<Longrightarrow> finer_covering(Z,join_covering(X,Y))" by auto2

lemma image_covering: "surjective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
  is_covering(B, \<lambda>a\<in>I. (f``(X`a))\<in>Pow(B))" by auto2

lemma vImage_covering: "g \<in> C \<rightarrow> A \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
  is_covering(C, \<lambda>a\<in>I. (g -`` (X`a))\<in>Pow(C))"
  by (tactic {* auto2s_tac @{context} (
    LET "Y = (\<lambda>a\<in>I. (g -`` (X`a))\<in>Pow(C))" THEN
    HAVE "\<forall>x\<in>C. \<exists>p\<in>I. x \<in> Y ` p" WITH CHOOSE "a\<in>I, g`x \<in> a") *})

lemma product_covering: "X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(B) \<Longrightarrow>
  is_covering(A,X) \<Longrightarrow> is_covering(B,Y) \<Longrightarrow>
  is_covering(A\<times>B, \<lambda>p\<in>I\<times>K. (X`fst(p) \<times> Y`snd(p))\<in>Pow(A\<times>B))"
  by (tactic {* auto2s_tac @{context} (
    LET "Z = (\<lambda>p\<in>I\<times>K. (X`fst(p) \<times> Y`snd(p))\<in>Pow(A\<times>B))") *})

lemma glue_fun_on_covering [backward1]: "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  \<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b) \<Longrightarrow>
  \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<exists>f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D. (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)" WITH (
      LET "f = (\<lambda>x\<in>(\<Union>a\<in>I. X`a). (F(SOME a\<in>I. x\<in>X`a) ` x) \<in> D)")) *})

section {* Partitions *}  (* Bourbaki II.4.7 *)

lemma singleton_disjoint [backward]: "a \<noteq> b \<Longrightarrow> {a} \<inter> {b} = \<emptyset>" by auto2

definition mutually_disjoint :: "i \<Rightarrow> o" where [rewrite]:
  "mutually_disjoint(X) \<longleftrightarrow> (\<forall>a\<in>source(X). \<forall>b\<in>source(X). a \<noteq> b \<longrightarrow> X`a \<inter> X`b = \<emptyset>)"

lemma vImage_set_disjoint [backward2]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> X \<subseteq> B \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> X \<inter> Y = \<emptyset> \<Longrightarrow> f -`` X \<inter> f -`` Y = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "b, b \<in> (f -`` X) \<inter> (f -`` Y)" THEN HAVE "f ` b \<in> X \<inter> Y") *})

lemma vImage_mutually_disjoint [backward2]:
  "is_function(f) \<Longrightarrow> Y \<in> I \<rightarrow> Pow(target(f)) \<Longrightarrow> mutually_disjoint(Y) \<Longrightarrow>
   mutually_disjoint(\<lambda>a\<in>I. (f -`` (Y`a))\<in>Pow(source(f)))" by auto2

lemma glue_fun_on_mut_disj [backward1]: "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  mutually_disjoint(X) \<Longrightarrow> \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b)" WITH CASE "a = b") *})

(* For partitions, usually definition in terms of sets is more convenient *)
definition mutually_disjoint_sets :: "i \<Rightarrow> o" where [rewrite]:
  "mutually_disjoint_sets(X) \<longleftrightarrow> (\<forall>a\<in>X. \<forall>b\<in>X. a \<noteq> b \<longrightarrow> a \<inter> b = \<emptyset>)"
setup {* add_property_const @{term mutually_disjoint_sets} *}

definition is_partition_sets :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_partition_sets(E,X) \<longleftrightarrow> (E = \<Union>X \<and> mutually_disjoint_sets(X))"

lemma singletons_is_partition: "is_partition_sets(E, {{x}. x\<in>E})"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>x\<in>E. x \<in> \<Union>{{x}. x \<in> E}" WITH HAVE "x \<in> {x}") *})

(* Version for a family of sets *)
definition is_partition :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_partition(E,X) \<longleftrightarrow> (E = (\<Union>a\<in>source(X). X`a) \<and> mutually_disjoint(X))"

lemma glue_fun_on_partition [backward1]:
  "is_function(X) \<Longrightarrow> \<forall>a\<in>source(X). F(a) \<in> X`a \<rightarrow> D \<Longrightarrow> is_partition(E,X) \<Longrightarrow>
   \<exists>!f. f\<in>E\<rightarrow>D \<and> (\<forall>a\<in>source(X). \<forall>b\<in>X`a. f`b = F(a)`b)" by auto2

(* X is a partition of E, indexed by I. F is a meta-family of functions indexed
   by I, where each F(a) is a function X(a)\<rightarrow>D. Get the glued map E\<rightarrow>D. *)
definition glue_partition_fun :: "[i, i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "glue_partition_fun(E,X,D,F) = (THE f. f\<in>E\<rightarrow>D \<and> (\<forall>a\<in>source(X). \<forall>b\<in>X`a. f`b = F(a)`b))"

lemma glue_partition_fun_prop:
  "is_function(X) \<Longrightarrow> \<forall>a\<in>source(X). F(a) \<in> X`a \<rightarrow> D \<Longrightarrow> is_partition(E,X) \<Longrightarrow>
   glue_partition_fun(E,X,D,F) \<in> E\<rightarrow>D \<and>
   (\<forall>a\<in>source(X). \<forall>b\<in>X`a. glue_partition_fun(E,X,D,F)`b = F(a)`b)" by auto2
setup {* add_forward_prfstep_cond @{thm glue_partition_fun_prop} [with_term "glue_partition_fun(?E,?X,?D,?F)"] *}
setup {* add_prfstep_check_req ("glue_partition_fun(E,X,D,F)", "\<forall>a\<in>source(X). F(a) \<in> X`a \<rightarrow> D") *}
setup {* del_prfstep_thm @{thm glue_partition_fun_def} *}

section {* Sum of a family of sets *}  (* Bourbaki II.4.8 *)

(* Version of Sigma for object functions *)
definition Sigma' :: "i \<Rightarrow> i" where [rewrite]:
  "Sigma'(X) = Sigma(source(X), \<lambda>a. X`a)"

lemma Sigma'_iff [rewrite]:
  "is_function(X) \<Longrightarrow> \<langle>a,b\<rangle> \<in> Sigma'(X) \<longleftrightarrow> (a \<in> source(X) \<and> b \<in> X`a)" by auto2

lemma Sigma'I: "is_function(X) \<Longrightarrow> a \<in> source(X) \<Longrightarrow> \<forall>b \<in> X`a. \<langle>a,b\<rangle> \<in> Sigma'(X)" by auto2
setup {* add_forward_prfstep_cond @{thm Sigma'I} [with_term "Sigma'(?X)"] *}

lemma Sigma'_split: "p \<in> Sigma'(X) \<Longrightarrow> p = \<langle>fst(p), snd(p)\<rangle>" by auto2
setup {* add_forward_prfstep_cond @{thm Sigma'_split} [with_cond "?p \<noteq> \<langle>?a, ?b\<rangle>"] *}
setup {* del_prfstep_thm @{thm Sigma'_def} *}

definition union_to_sum_fun :: "i \<Rightarrow> i" where [rewrite]:
  "union_to_sum_fun(X) = (\<lambda>p\<in>Sigma'(X). snd(p)\<in>(\<Union>a\<in>source(X). X`a))"

lemma union_to_sum_is_function [typing]:
  "is_function(X) \<Longrightarrow> union_to_sum_fun(X) \<in> Sigma'(X) \<rightarrow> (\<Union>a\<in>source(X). X`a)" by auto2

lemma union_to_sum_is_surj [forward]:
  "is_function(X) \<Longrightarrow> surjective(union_to_sum_fun(X))" by auto2 

lemma union_to_sum_is_bij:
  "mutually_disjoint(X) \<Longrightarrow> is_function(X) \<Longrightarrow>
   union_to_sum_fun(X) \<in> Sigma'(X) \<cong> (\<Union>a\<in>source(X). X`a)" by auto2

end
