(*
  File: BigProd.thy
  Author: Bohua Zhan

  Results about arbitrary products, mainly following Section II.5 in Bourbaki.
*)

theory BigProd
  imports Coverings
begin

section \<open>Product of a family of sets\<close>  (* Bourbaki II.5.3 *)

definition projf :: "[i, i \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "projf(I,B,a) = Fun(Pi(I,B), B(a), \<lambda>f. f`a)"
setup {* register_wellform_data ("projf(I,B,a)", ["a \<in> I"]) *}

lemma projf_is_function [typing]: "a \<in> I \<Longrightarrow> projf(I,B,a) \<in> Pi(I,B) \<rightarrow> B(a)" by auto2

lemma projf_eval [rewrite]:
  "f \<in> source(projf(I,B,a)) \<Longrightarrow> a \<in> I \<Longrightarrow> projf(I,B,a) ` f = f`a" by auto2
setup {* del_prfstep_thm @{thm projf_def} *}

lemma Pi_empty_index [rewrite]: "Pi(\<emptyset>, B) = {Tup(\<emptyset>, \<lambda>_. \<emptyset>)}" by auto2

(* Canonical bijection between Pi(A, \<lambda>_B) with function space *)
definition Pi_to_fun_space :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "Pi_to_fun_space(I,B) = Fun(Pi(I,\<lambda>_. B), I\<rightarrow>B, \<lambda>f. Fun(I,B, \<lambda>a. f`a))"

lemma Pi_to_fun_space_is_function [typing]:
  "Pi_to_fun_space(I,B) \<in> Pi(I,\<lambda>_. B) \<rightarrow> (I \<rightarrow> B)" by auto2

lemma Pi_to_fun_space_eval [rewrite]:
  "f \<in> source(Pi_to_fun_space(I,B)) \<Longrightarrow> Pi_to_fun_space(I,B) ` f = Fun(I,B, \<lambda>a. f`a)" by auto2
setup {* del_prfstep_thm @{thm Pi_to_fun_space_def} *}

definition fun_space_to_Pi :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "fun_space_to_Pi(I,B) = Fun(I\<rightarrow>B, Pi(I,\<lambda>_. B), \<lambda>f. Tup(I, \<lambda>a. f`a))"

lemma fun_space_to_Pi_is_function [typing]:
  "fun_space_to_Pi(I,B) \<in> (I \<rightarrow> B) \<rightarrow> Pi(I,\<lambda>_. B)" by auto2

lemma fun_space_to_Pi_eval [rewrite]:
  "f \<in> source(fun_space_to_Pi(I,B)) \<Longrightarrow> fun_space_to_Pi(I,B) ` f = Tup(I, \<lambda>a. f`a)" by auto2
setup {* del_prfstep_thm @{thm fun_space_to_Pi_def} *}

lemma fun_space_Pi_bij: "fun_space_to_Pi(I,B) \<in> (I \<rightarrow> B) \<cong> Pi(I,\<lambda>_. B)"
@proof @have "inverse_pair(fun_space_to_Pi(I,B), Pi_to_fun_space(I,B))" @qed

(* Cases when the index contains one or two elements. *)
definition singleton_prod_map :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "singleton_prod_map(a,B) = Fun(Pi({a},B), B(a), \<lambda>f. f`a)"

lemma singleton_prod_map_is_bijective [typing]:
  "singleton_prod_map(a,B) \<in> Pi({a},B) \<cong> B(a)"
@proof
  @have "inverse_pair(singleton_prod_map(a,B), Fun(B(a), Pi({a},B), \<lambda>x. Tup({a}, \<lambda>_. x)))"
@qed

definition doubleton_prod_map :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "doubleton_prod_map(a,b,B) = Fun(Pi({a,b},B), B(a)\<times>B(b), \<lambda>f. \<langle>f`a, f`b\<rangle>)"

lemma doubleton_prod_map_is_bijective:
  "a \<noteq> b \<Longrightarrow> doubleton_prod_map(a,b,B) \<in> Pi({a,b},B) \<cong> B(a)\<times>B(b)"
@proof
  @have "doubleton_prod_map(a,b,B) \<in> Pi({a,b},B) \<rightarrow> B(a)\<times>B(b)"
  @let "inv = Fun(B(a)\<times>B(b), Pi({a,b},B), \<lambda>p. Tup({a,b}, \<lambda>c. if c = a then fst(p) else snd(p)))"
  @have "inv \<in> B(a)\<times>B(b) \<rightarrow> Pi({a,b},B)"
  @have "inverse_pair(doubleton_prod_map(a,b,B), inv)"
@qed

(* Case when each set in the family contains a single element. *)
lemma singleton_sets_prod:
  "\<forall>a\<in>I. \<exists>!x. x \<in> B(a) \<Longrightarrow> Pi(I,B) = {Tup(I, \<lambda>a. THE x. x\<in>B(a))}" by auto2

(* Diagonal mapping *)
definition prod_diagonal :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "prod_diagonal(I,E) = {Tup(I, \<lambda>_. e). e \<in> E}"

lemma prod_diagonal_is_subset:
  "prod_diagonal(I,E) \<subseteq> Pi(I, \<lambda>_. E)" by auto2
setup {* add_forward_prfstep_cond @{thm prod_diagonal_is_subset} [with_term "prod_diagonal(?I,?E)"] *}

definition diagonal_to_set :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "diagonal_to_set(I,E) = Fun(prod_diagonal(I,E), E, \<lambda>f. f`Choice(I))"

definition set_to_diagonal :: "[i, i] \<Rightarrow> i" where [rewrite]:
  "set_to_diagonal(I,E) = Fun(E, prod_diagonal(I,E), \<lambda>e. Tup(I, \<lambda>_. e))"

lemma set_to_diagonal_bijective:
  "I \<noteq> \<emptyset> \<Longrightarrow> set_to_diagonal(I,E) \<in> E \<cong> prod_diagonal(I,E)"
@proof @have "inverse_pair(diagonal_to_set(I,E), set_to_diagonal(I,E))" @qed

(* Bijection on index sets. Here B maps from target(u). *)
definition reindex_prod :: "[i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "reindex_prod(u,B) = Fun(Pi(target(u),B), Pi(source(u), \<lambda>a. B(u`a)), \<lambda>f. Tup(source(u), \<lambda>a. f`(u`a)))"

lemma reindex_prod_is_fun [typing]:
  "is_function(u) \<Longrightarrow> reindex_prod(u,B) \<in> Pi(target(u),B) \<rightarrow> Pi(source(u), \<lambda>a. B(u`a))" by auto2

lemma reindex_prod_eval [rewrite]:
  "is_function(u) \<Longrightarrow> f \<in> source(reindex_prod(u,B)) \<Longrightarrow> a \<in> source(u) \<Longrightarrow>
   (reindex_prod(u,B)`f)`a = f`(u`a)" by auto2
setup {* del_prfstep_thm @{thm reindex_prod_def} *}

lemma reindex_prod_comp [rewrite]:
  "is_function(u) \<Longrightarrow> is_function(v) \<Longrightarrow> target(u) = source(v) \<Longrightarrow>
   reindex_prod(u,\<lambda>a. B`(v`a)) \<circ> reindex_prod(v,\<lambda>a. B`a) = reindex_prod(v \<circ> u, \<lambda>a. B`a)" by auto2

lemma reindex_prod_id [rewrite]:
  "reindex_prod(id_fun(I), B) = id_fun(Pi(I,B))" by auto2

lemma reindex_prod_is_bij:
  "bijective(u) \<Longrightarrow> reindex_prod(u, \<lambda>a. B`a) \<in> Pi(target(u), \<lambda>a. B`a) \<cong> Pi(source(u), \<lambda>a. B`(u`a))"
@proof
  @have "inverse_pair(reindex_prod(u,\<lambda>a. B`a), reindex_prod(inverse(u), (\<lambda>a. B`(u`a))))"
@qed

section \<open>Partial products\<close>  (* Bourbaki II.5.4 *)

definition projf_set :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "projf_set(I,J,B) = Fun(Pi(I,B), Pi(J,B), \<lambda>f. proj_set(f,J))"
setup {* register_wellform_data ("projf_set(I,J,B)", ["J \<subseteq> I"]) *}
setup {* add_prfstep_check_req ("projf_set(I,J,B)", "J \<subseteq> I") *}

lemma restrict_prod_is_surj [backward]:
  "J \<subseteq> I \<Longrightarrow> \<forall>a\<in>I. B(a) \<noteq> \<emptyset> \<Longrightarrow> surjective(projf_set(I,J,B))"
@proof
  @have "\<forall>f\<in>Pi(J,B). \<exists>g\<in>Pi(I,B). projf_set(I,J,B)`g = f" @with
    @obtain "g \<in> Pi(I,B)" where "g = Tup(I, \<lambda>a. if a \<in> J then f`a else Choice(B(a)))" @end
@qed

lemma restrict_prod_is_proj [rewrite]:
  "{a} \<subseteq> I \<Longrightarrow> singleton_prod_map(a,B) \<circ> projf_set(I,{a},B) = projf(I,B,a)" by auto2

lemma proj_is_surj [backward]:
  "a \<in> I \<Longrightarrow> \<forall>a\<in>I. B(a) \<noteq> \<emptyset> \<Longrightarrow> surjective(projf(I,B,a))"
@proof
  @have "projf(I,B,a) = singleton_prod_map(a,B) \<circ> projf_set(I,{a},B)"
  @have "surjective(projf_set(I,{a},B))"
@qed

lemma proj_is_surj' [backward]:
  "\<forall>a\<in>I. B(a) \<noteq> \<emptyset> \<Longrightarrow> a \<in> I \<Longrightarrow> b \<in> B(a) \<Longrightarrow> \<exists>f\<in>Pi(I,B). f`a = b"
@proof
  @have "surjective(projf(I,B,a))"
  @obtain "f\<in>Pi(I,B)" where "projf(I,B,a)`f = b"
@qed

lemma prod_non_empty [rewrite]:
  "Pi(I,B) \<noteq> \<emptyset> \<longleftrightarrow> (\<forall>a\<in>I. B(a) \<noteq> \<emptyset>)"
@proof
  @contradiction
  @case "\<forall>a\<in>I. B(a) \<noteq> \<emptyset>" @with
    @contradiction
    @have "I \<noteq> \<emptyset>" @obtain "a \<in> I"
    @have "surjective(projf(I,B,a))" @end
  @case "Pi(I,B) \<noteq> \<emptyset>" @with
    @obtain "f \<in> Pi(I,B)"
    @have "\<forall>a\<in>I. B(a) \<noteq> \<emptyset>" @with @have "f`a \<in> B(a)" @end @end
@qed

lemma prod_is_empty [rewrite]: "B(a) = \<emptyset> \<Longrightarrow> a \<in> I \<Longrightarrow> Pi(I,B) = \<emptyset>" by auto2
setup {* del_prfstep_thm_eqforward @{thm prod_non_empty} *}

lemma prod_subset1 [backward]:
  "\<forall>a\<in>I. X(a) \<subseteq> Y(a) \<Longrightarrow> Pi(I,X) \<subseteq> Pi(I,Y)" by auto2

lemma prod_subset2:
  "Pi(I,X) \<subseteq> Pi(I,Y) \<Longrightarrow> \<forall>a\<in>I. X(a) \<noteq> \<emptyset> \<Longrightarrow> \<forall>a\<in>I. X(a) \<subseteq> Y(a)"
@proof
  @have (@rule) "\<forall>a\<in>I. \<forall>y\<in>X(a). \<exists>f\<in>Pi(I,X). projf(I,X,a)`f = y" @with
    @have "surjective(projf(I,X,a))"
  @end
@qed

section \<open>Associativity of products\<close>  (* Bourbaki II.5.5 *)

definition prod_assoc_fun :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "prod_assoc_fun(I,J,X) =
    Fun(Pi(I,X), Pi(source(J), \<lambda>a. Pi(J`a, X)), \<lambda>f. Tup(source(J), \<lambda>a. projf_set(I,J`a,X)`f))"
setup {* register_wellform_data ("prod_assoc_fun(I,J,X)", ["target(J) = Pow(I)"]) *}

lemma prod_assoc_fun_is_function [typing]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow>
   prod_assoc_fun(I,J,X) \<in> Pi(I,X) \<rightarrow> Pi(source(J), \<lambda>a. Pi(J`a, X))" by auto2

lemma prod_assoc_fun_eval [rewrite]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> f \<in> source(prod_assoc_fun(I,J,X)) \<Longrightarrow>
   a \<in> source(J) \<Longrightarrow> b \<in> J`a \<Longrightarrow> prod_assoc_fun(I,J,X)`f`a`b = f`b" by auto2

setup {* del_prfstep_thm @{thm prod_assoc_fun_def} *}

(* We define the inverse in stages. First, given a element of Pi(source(J), \<lambda>a. Pi(J`a, X)),
   define a function from I to \<Union>a\<in>I. X(a), by pasting together the functions J`a (a\<in>L) to
   \<Union>a\<in>I. X(a). *)
definition prod_assoc_fun_inv1 :: "[i, i, i \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "prod_assoc_fun_inv1(I,J,X,f) =
    glue_partition_fun(I,J,\<Union>{X(c). c\<in>I}, \<lambda>a. Fun(J`a, \<Union>{X(c). c\<in>I}, \<lambda>b. f`a`b))"
setup {* register_wellform_data ("prod_assoc_fun_inv1(I,J,X,f)",
  ["target(J) = Pow(I)", "is_partition(I,J)", "f \<in> Pi(source(J), \<lambda>a. Pi(J`a,X))"]) *}

lemma prod_assoc_fun_inv1_is_fun [typing]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   f \<in> Pi(source(J), \<lambda>a. Pi(J`a, X)) \<Longrightarrow> prod_assoc_fun_inv1(I,J,X,f) \<in> I \<rightarrow> \<Union>{X(c). c\<in>I}" by auto2

lemma prod_assoc_fun_inv1_eval [rewrite]:
  "is_function(J) \<Longrightarrow> a \<in> source(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   f \<in> Pi(source(J), \<lambda>a. Pi(J`a, X)) \<Longrightarrow> b \<in> J`a \<Longrightarrow> prod_assoc_fun_inv1(I,J,X,f)`b = f`a`b" by auto2

setup {* del_prfstep_thm @{thm prod_assoc_fun_inv1_def} *}

(* Second stage, define a function from Pi(source(J), \<lambda>b. Pi(J`b, X)) to Pi(I,X). *)
definition prod_assoc_fun_inv :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "prod_assoc_fun_inv(I,J,X) = Fun(Pi(source(J), \<lambda>a. Pi(J`a, X)), Pi(I,X),
    \<lambda>f. Tup(I, \<lambda>a. prod_assoc_fun_inv1(I,J,X,f)`a))"
setup {* register_wellform_data ("prod_assoc_fun_inv(I,J,X)",
  ["target(J) = Pow(I)", "is_partition(I,J)"]) *}

lemma prod_assoc_fun_inv_is_fun [typing]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   prod_assoc_fun_inv(I,J,X) \<in> Pi(source(J), \<lambda>a. Pi(J`a, X)) \<rightarrow> Pi(I,X)" by auto2

lemma prod_assoc_fun_inv_eval [rewrite]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow> a \<in> source(J) \<Longrightarrow>
   f \<in> source(prod_assoc_fun_inv(I,J,X)) \<Longrightarrow> b \<in> J`a \<Longrightarrow>
   prod_assoc_fun_inv(I,J,X)`f`b = f`a`b" by auto2
setup {* del_prfstep_thm @{thm prod_assoc_fun_inv_def} *}

lemma prod_assoc_fun_inv_pair1 [rewrite]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   x \<in> source(prod_assoc_fun(I,J,X)) \<Longrightarrow> prod_assoc_fun_inv(I,J,X) ` (prod_assoc_fun(I,J,X) ` x) = x"
@proof @have "\<forall>b\<in>I. \<exists>a\<in>source(J). b \<in> J`a" @qed

lemma prod_assoc_fun_inv_pair2 [rewrite]:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   x \<in> source(prod_assoc_fun_inv(I,J,X)) \<Longrightarrow> prod_assoc_fun(I,J,X) ` (prod_assoc_fun_inv(I,J,X) ` x) = x"
@proof @have "\<forall>b\<in>I. \<exists>a\<in>source(J). b \<in> J`a" @qed

lemma prod_assoc_fun_bijective:
  "is_function(J) \<Longrightarrow> target(J) = Pow(I) \<Longrightarrow> is_partition(I,J) \<Longrightarrow>
   prod_assoc_fun(I,J,X) \<in> Pi(I,X) \<cong> Pi(source(J), \<lambda>a. Pi(J`a, X))"
@proof @have "inverse_pair(prod_assoc_fun(I,J,X), prod_assoc_fun_inv(I,J,X))" @qed

section \<open>Distributivity formulae\<close>  (* Bourbaki II.5.6 *)

(* L is an overall index set. J is a mapping from b\<in>L to index sets J(b).
   X(b) is a family of sets indexed by J(b). If L and each J(b) are nonempty,
   then the product index set Pi(L,J) is nonempty. *)
lemma distrib_Union_INT [rewrite_bidir]:
  "\<forall>b\<in>L. J(b) \<noteq> \<emptyset> \<Longrightarrow>
  (\<Union>b\<in>L. (\<Inter>a\<in>J(b). X(b)`a)) = (\<Inter>f\<in>Pi(L,J). (\<Union>b\<in>L. X(b)`(f`b)))"
@proof
  @have "\<forall>x\<in>(\<Inter>f\<in>Pi(L,J). (\<Union>b\<in>L. X(b)`(f`b))). x\<in>(\<Union>b\<in>L. (\<Inter>a\<in>J(b). X(b)`a))" @with
    @contradiction
    @obtain "f \<in> Pi(L,J)" where "f = Tup(L, \<lambda>b. SOME a\<in>J(b). x \<notin> X(b)`a)" @end
@qed

(* Corollary of above. More trouble to set up link. *)
lemma distrib_Union_inter:
  "I \<noteq> \<emptyset> \<Longrightarrow> K \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>a\<in>I. X`a) \<union> (\<Inter>b\<in>K. Y`b) = (\<Inter>p\<in>I\<times>K. (X`fst(p) \<union> Y`snd(p)))" by auto2

(* Can also make use of UN_complement and INT_complement, but more troublesome. *)
lemma distrib_Inter_UN [rewrite_bidir]:
  "L \<noteq> \<emptyset> \<Longrightarrow> \<forall>b\<in>L. J(b) \<noteq> \<emptyset> \<Longrightarrow>
  (\<Inter>b\<in>L. (\<Union>a\<in>J(b). X(b)`a)) = (\<Union>f\<in>Pi(L,J). (\<Inter>b\<in>L. X(b)`(f`b)))"
@proof
  @have "\<forall>x\<in>(\<Inter>b\<in>L. (\<Union>a\<in>J(b). X(b)`a)). x\<in>(\<Union>f\<in>Pi(L,J). (\<Inter>b\<in>L. X(b)`(f`b)))" @with
    @obtain "f \<in> Pi(L,J)" where "f = Tup(L, \<lambda>b. SOME a\<in>J(b). x \<in> X(b)`a)" @end
@qed

(* Corollary of above. More trouble to set up link. *)
lemma distrib_Inter_union:
  "I \<noteq> \<emptyset> \<Longrightarrow> K \<noteq> \<emptyset> \<Longrightarrow> (\<Union>a\<in>I. X`a) \<inter> (\<Union>b\<in>K. Y`b) = (\<Union>p\<in>I\<times>K. (X`fst(p) \<inter> Y`snd(p)))" by auto2

(* Distributivity of product over union. *)
lemma distrib_prod_UN [rewrite_back]:
  "Pi(L, \<lambda>b. (\<Union>a\<in>J(b). X(b)`a)) = (\<Union>f\<in>Pi(L,J). Pi(L, \<lambda>b. X(b)`(f`b)))"
@proof
  @have "\<forall>g\<in>Pi(L, \<lambda>b. (\<Union>a\<in>J(b). X(b)`a)). g\<in>(\<Union>f\<in>Pi(L,J). Pi(L, \<lambda>b. X(b)`(f`b)))" @with
    @obtain "f \<in> Pi(L,J)" where "f = Tup(L, \<lambda>b. SOME a\<in>J(b). g`b \<in> X(b)`a)" @end
@qed

lemma distrib_prod_INT:
  "L \<noteq> \<emptyset> \<Longrightarrow> \<forall>b\<in>L. J(b) \<noteq> \<emptyset> \<Longrightarrow>
   Pi(L, \<lambda>b. (\<Inter>a\<in>J(b). X(b)`a)) = (\<Inter>f\<in>Pi(L,J). Pi(L, \<lambda>b. X(b)`(f`b)))"
@proof
  @have "\<forall>g\<in>(\<Inter>f\<in>Pi(L,J). Pi(L, \<lambda>b. X(b)`(f`b))). g\<in>Pi(L, \<lambda>b. (\<Inter>a\<in>J(b). X(b)`a))" @with
    @have (@rule) "\<forall>b\<in>L. \<forall>a\<in>J(b). g`b \<in> X(b)`a" @with
      @obtain "f\<in>Pi(L,J)" where "f`b = a" @end @end
@qed

lemma distrib_prod_union:
  "(\<Union>a\<in>I. X(a)) \<times> (\<Union>b\<in>K. Y(b)) = (\<Union>p\<in>I\<times>K. X(fst(p))\<times>Y(snd(p)))" by auto2

lemma distrib_prod_inter:
  "I \<noteq> \<emptyset> \<Longrightarrow> K \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>a\<in>I. X(a)) \<times> (\<Inter>b\<in>K. Y(b)) = (\<Inter>p\<in>I\<times>K. X(fst(p))\<times>Y(snd(p)))" by auto2

lemma distrib_prod_INT_pair:
  "K \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>b\<in>K. Pi(I, \<lambda>a. X`\<langle>a,b\<rangle>)) = Pi(I, \<lambda>a. \<Inter>b\<in>K. X`\<langle>a,b\<rangle>)" by auto2

lemma distrib_inter_prod_pair:
  "I \<noteq> \<emptyset> \<Longrightarrow> Pi(I,X) \<inter> Pi(I,Y) = Pi(I, \<lambda>a. X(a)\<inter>Y(a))" by auto2

lemma distrib_prod_inter_pair:
  "I \<noteq> \<emptyset> \<Longrightarrow> (\<Inter>a\<in>I. X(a)) \<times> (\<Inter>a\<in>I. Y(a)) = (\<Inter>a\<in>I. X(a)\<times>Y(a))" by auto2

(* Disjointness of product sets *)
lemma prod_set_disjoint [backward1]:
  "a \<in> I \<Longrightarrow> X(a) \<inter> Y(a) = \<emptyset> \<Longrightarrow> Pi(I,X) \<inter> Pi(I,Y) = \<emptyset>"
@proof
  @contradiction
  @obtain x where "x \<in> Pi(I,X) \<inter> Pi(I,Y)" @have "x`a \<in> X(a) \<inter> Y(a)"
@qed

section \<open>Extension of mappings to products\<close>  (* Bourbaki II.5.7 *)

definition ext_prod_fun :: "[i, i \<Rightarrow> i, i \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "ext_prod_fun(I,X,Y,F) = Fun(Pi(I,X), Pi(I,Y), \<lambda>u. Tup(I, \<lambda>a. (F`a)`(u`a)))"
setup {* register_wellform_data ("ext_prod_fun(I,X,Y,F)", ["F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a))"]) *}
setup {* add_prfstep_check_req ("ext_prod_fun(I,X,Y,F)", "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a))") *}

lemma ext_prod_fun_is_function [typing]:
  "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a)) \<Longrightarrow> ext_prod_fun(I,X,Y,F) \<in> Pi(I,X) \<rightarrow> Pi(I,Y)" by auto2

lemma ext_prod_fun_eval [rewrite]:
  "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a)) \<Longrightarrow> u \<in> source(ext_prod_fun(I,X,Y,F)) \<Longrightarrow>
   a \<in> source(ext_prod_fun(I,X,Y,F)`u) \<Longrightarrow>
   ext_prod_fun(I,X,Y,F)`u`a = (F`a)`(u`a)" by auto2
setup {* del_prfstep_thm @{thm ext_prod_fun_def} *}

lemma ext_prod_fun_assoc [rewrite_back]:
  "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a)) \<Longrightarrow> G \<in> Pi(I,\<lambda>a. Y(a)\<rightarrow>Z(a)) \<Longrightarrow>
   ext_prod_fun(I,X,Z, Tup(I, \<lambda>a. G`a \<circ> F`a)) = ext_prod_fun(I,Y,Z,G) \<circ> ext_prod_fun(I,X,Y,F)" by auto2

lemma ext_prod_fun_id [rewrite]:
  "ext_prod_fun(I,X,X, Tup(I, \<lambda>a. id_fun(X(a)))) = id_fun(Pi(I,X))" by auto2

lemma ext_prod_fun_inj:
  "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a)) \<Longrightarrow> \<forall>a\<in>I. injective(F`a) \<Longrightarrow> injective(ext_prod_fun(I,X,Y,F))"
@proof
  @case "\<forall>a\<in>I. X(a) \<noteq> \<emptyset>" @with
    @let "R = ext_prod_fun(I,Y,X, Tup(I, \<lambda>a. left_inverse(F`a)))"
    @have "R \<circ> ext_prod_fun(I,X,Y,F) = id_fun(Pi(I,X))" @end
@qed

lemma ext_prod_fun_surj:
  "F \<in> Pi(I,\<lambda>a. X(a)\<rightarrow>Y(a)) \<Longrightarrow> \<forall>a\<in>I. surjective(F`a) \<Longrightarrow> surjective(ext_prod_fun(I,X,Y,F))"
@proof
  @let "R = ext_prod_fun(I,Y,X, Tup(I, \<lambda>a. right_inverse(F`a)))"
  @have "ext_prod_fun(I,X,Y,F) \<circ> R = id_fun(Pi(I,Y))"
@qed

(* Canonical bijection coming from extension to products. *)

(* Given a mapping f \<in> E \<rightarrow> Pi(I,X), get family of mappings f_i \<in> Pi(I, \<lambda>a\<in>I. E\<rightarrow>X(i)). *)
definition map_to_prod_to_map_family :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "map_to_prod_to_map_family(E,I,X) =
    Fun(E\<rightarrow>Pi(I,X), Pi(I, \<lambda>a. E\<rightarrow>X(a)), \<lambda>f. Tup(I, \<lambda>a. projf(I,X,a) \<circ> f))"

lemma map_to_prod_to_map_family_is_fun [typing]:
  "map_to_prod_to_map_family(E,I,X) \<in> (E\<rightarrow>Pi(I,X)) \<rightarrow> Pi(I, \<lambda>a. E\<rightarrow>X(a))" by auto2

lemma map_to_prod_to_map_family_eval [rewrite]:
  "a \<in> I \<Longrightarrow> x \<in> E \<Longrightarrow> f \<in> E\<rightarrow>Pi(I,X) \<Longrightarrow>
   map_to_prod_to_map_family(E,I,X)`f`a`x = f`x`a" by auto2
setup {* del_prfstep_thm @{thm map_to_prod_to_map_family_def} *}

definition map_family_to_map_to_prod :: "[i, i, i \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "map_family_to_map_to_prod(E,I,X) =
    Fun(Pi(I, \<lambda>a. E\<rightarrow>X(a)), E\<rightarrow>Pi(I,X), \<lambda>f. Fun(E, Pi(I,X), \<lambda>x. Tup(I, \<lambda>a. f`a`x)))"

lemma map_family_to_map_to_prod_is_fun [typing]:
  "map_family_to_map_to_prod(E,I,X) \<in> Pi(I, \<lambda>a. E\<rightarrow>X(a)) \<rightarrow> E \<rightarrow> Pi(I,X)" by auto2

lemma map_family_to_map_to_prod_eval [rewrite]:
  "a \<in> I \<Longrightarrow> x \<in> E \<Longrightarrow> f \<in> Pi(I, \<lambda>a. E\<rightarrow>X(a)) \<Longrightarrow>
   map_family_to_map_to_prod(E,I,X)`f`x`a = f`a`x" by auto2
setup {* del_prfstep_thm @{thm map_family_to_map_to_prod_def} *}

lemma map_to_prod_to_map_family_bij:
  "map_to_prod_to_map_family(E,I,X) \<in> (E\<rightarrow>Pi(I,X)) \<cong> Pi(I, \<lambda>a. E\<rightarrow>X(a))"
@proof
  @have "inverse_pair(map_to_prod_to_map_family(E,I,X), map_family_to_map_to_prod(E,I,X))"
@qed

end
