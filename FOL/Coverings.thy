(*
  File: Coverings.thy
  Author: Bohua Zhan

  Covering by sets and partitions.
*)

theory Coverings
  imports Functions
begin

section \<open>Coverings\<close>  (* Bourbaki II.4.6 *)

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
  "join_covering(X,Y) = Fun(source(X)\<times>source(Y), target(X), \<lambda>p. X`fst(p) \<inter> Y`snd(p))"
setup {* register_wellform_data ("join_covering(X,Y)", ["target(X) = target(Y)"]) *}

lemma join_covering_is_fun [typing]:
  "is_function(X) \<Longrightarrow> is_function(Y) \<Longrightarrow> target(X) = target(Y) \<Longrightarrow> target(X) = Pow(E) \<Longrightarrow>
   join_covering(X,Y) \<in> source(X)\<times>source(Y) \<rightarrow> target(X)" by auto2

lemma join_covering_eval [rewrite]:
  "is_function(X) \<Longrightarrow> is_function(Y) \<Longrightarrow> target(X) = target(Y) \<Longrightarrow> p \<in> source(join_covering(X,Y)) \<Longrightarrow>
   target(X) = Pow(E) \<Longrightarrow> join_covering(X,Y)`p = X`fst(p) \<inter> Y`snd(p)" by auto2
setup {* del_prfstep_thm @{thm join_covering_def} *}

lemma join_is_covering:
  "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> is_covering(E,X) \<Longrightarrow>
   is_covering(E,Y) \<Longrightarrow> is_covering(E, join_covering(X,Y))" by auto2

lemma join_is_finer:
  "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow>
   finer_covering(join_covering(X,Y),X) \<and> finer_covering(join_covering(X,Y),Y)" by auto2

lemma join_is_finer_maximal:
  "X \<in> I \<rightarrow> Pow(E) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(E) \<Longrightarrow> Z \<in> L \<rightarrow> Pow(E) \<Longrightarrow>
   finer_covering(Z,X) \<Longrightarrow> finer_covering(Z,Y) \<Longrightarrow> finer_covering(Z,join_covering(X,Y))" by auto2

lemma image_covering:
  "surjective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
   Y = Fun(I, Pow(B), \<lambda>a. f``(X`a)) \<Longrightarrow> is_covering(B,Y)"
@proof
  @have "\<forall>x\<in>B. \<exists>p\<in>I. x \<in> Y ` p" @with
    @obtain "a\<in>A" where "f`a = x"
  @end
@qed

lemma vImage_covering:
  "g \<in> C \<rightarrow> A \<Longrightarrow> X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> is_covering(A,X) \<Longrightarrow>
   Y = Fun(I, Pow(C), \<lambda>a. g -`` (X`a)) \<Longrightarrow> is_covering(C,Y)"
@proof
  @have "\<forall>x\<in>C. \<exists>p\<in>I. x \<in> Y ` p" @with
    @contradiction
    @obtain "a\<in>I" where "g`x \<in> a"
  @end
@qed

lemma product_covering: "X \<in> I \<rightarrow> Pow(A) \<Longrightarrow> Y \<in> K \<rightarrow> Pow(B) \<Longrightarrow>
  is_covering(A,X) \<Longrightarrow> is_covering(B,Y) \<Longrightarrow>
  is_covering(A\<times>B, Fun(I\<times>K, Pow(A\<times>B), \<lambda>p. X`fst(p) \<times> Y`snd(p)))" by auto2

lemma glue_fun_on_covering [backward1]: "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  \<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b) \<Longrightarrow>
  \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
@proof
  @have "\<exists>f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D. (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)" @with
    @let "f = Fun(\<Union>a\<in>I. X`a, D, \<lambda>x. F(SOME a\<in>I. x\<in>X`a) ` x)"
    @have "f \<in> (\<Union>a\<in>I. X`a)\<rightarrow>D"
    @have "\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b" @with
      @have (@rule) "\<forall>b'\<in>I. func_coincide(F(a),F(b'), X`a \<inter> X`b')"
    @end
  @end
@qed

section \<open>Partitions\<close>  (* Bourbaki II.4.7 *)

lemma singleton_disjoint [backward]: "a \<noteq> b \<Longrightarrow> {a} \<inter> {b} = \<emptyset>" by auto2

definition mutually_disjoint :: "i \<Rightarrow> o" where [rewrite]:
  "mutually_disjoint(X) \<longleftrightarrow> (\<forall>a\<in>source(X). \<forall>b\<in>source(X). a \<noteq> b \<longrightarrow> X`a \<inter> X`b = \<emptyset>)"

lemma mutually_disjointD:
  "mutually_disjoint(X) \<Longrightarrow> a \<in> source(X) \<Longrightarrow> b \<in> source(X) \<Longrightarrow> a \<noteq> b \<Longrightarrow> X`a \<inter> X`b = \<emptyset>" by auto2
setup {* add_forward_prfstep_cond @{thm mutually_disjointD} [with_term "?X`?a", with_term "?X`?b", with_cond "?a \<noteq> ?b"] *}
setup {* del_prfstep_thm_eqforward @{thm mutually_disjoint_def} *}

lemma vImage_set_disjoint [backward2]:
  "f \<in> A \<rightarrow> B \<Longrightarrow> X \<subseteq> B \<Longrightarrow> Y \<subseteq> B \<Longrightarrow> X \<inter> Y = \<emptyset> \<Longrightarrow> f -`` X \<inter> f -`` Y = \<emptyset>"
@proof
  @contradiction
  @obtain "b \<in> (f -`` X) \<inter> (f -`` Y)" @have "f ` b \<in> X \<inter> Y"
@qed

lemma vImage_mutually_disjoint [backward2]:
  "is_function(f) \<Longrightarrow> Y \<in> I \<rightarrow> Pow(target(f)) \<Longrightarrow> mutually_disjoint(Y) \<Longrightarrow>
   mutually_disjoint(Fun(I,Pow(source(f)),\<lambda>a. f -`` (Y`a)))" by auto2

lemma glue_fun_on_mut_disj [backward1]:
  "is_function(X) \<Longrightarrow> I = source(X) \<Longrightarrow> \<forall>a\<in>I. F(a) \<in> X`a \<rightarrow> D \<Longrightarrow>
  mutually_disjoint(X) \<Longrightarrow> \<exists>!f. f\<in>(\<Union>a\<in>I. X`a)\<rightarrow>D \<and> (\<forall>a\<in>I. \<forall>b\<in>X`a. f`b = F(a)`b)"
@proof
  @have "\<forall>a\<in>I. \<forall>b\<in>I. func_coincide(F(a), F(b), X`a \<inter> X`b)" @with @case "a = b" @end
@qed

(* For partitions, usually definition in terms of sets is more convenient *)
definition mutually_disjoint_sets :: "i \<Rightarrow> o" where [rewrite]:
  "mutually_disjoint_sets(X) \<longleftrightarrow> (\<forall>a\<in>X. \<forall>b\<in>X. a \<noteq> b \<longrightarrow> a \<inter> b = \<emptyset>)"

definition is_partition_sets :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_partition_sets(E,X) \<longleftrightarrow> (E = \<Union>X \<and> mutually_disjoint_sets(X))"

lemma singletons_is_partition: "is_partition_sets(E, {{x}. x\<in>E})"
@proof @have "\<forall>x\<in>E. x \<in> \<Union>{{x}. x \<in> E}" @with @have "x \<in> {x}" @end @qed

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

section \<open>Sum of a family of sets\<close>  (* Bourbaki II.4.8 *)

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
  "union_to_sum_fun(X) = Fun(Sigma'(X), \<Union>a\<in>source(X). X`a, \<lambda>p. snd(p))"

lemma union_to_sum_is_function [typing]:
  "is_function(X) \<Longrightarrow> union_to_sum_fun(X) \<in> Sigma'(X) \<rightarrow> (\<Union>a\<in>source(X). X`a)" by auto2

lemma union_to_sum_is_surj [forward]:
  "is_function(X) \<Longrightarrow> surjective(union_to_sum_fun(X))" by auto2 

lemma union_to_sum_is_bij:
  "mutually_disjoint(X) \<Longrightarrow> is_function(X) \<Longrightarrow>
   union_to_sum_fun(X) \<in> Sigma'(X) \<cong> (\<Union>a\<in>source(X). X`a)" by auto2

end
