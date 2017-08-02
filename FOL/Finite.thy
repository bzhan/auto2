theory Finite
imports Nat
begin

section {* Gluing together two functions *}

(* Glue together two functions *)
definition glue_function2 :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "glue_function2(f,g) = Fun(source(f) \<union> source(g), target(f) \<union> target(g),
     \<lambda>x. if x \<in> source(f) then f ` x else g ` x)"
setup {* register_wellform_data ("glue_function2(f,g)", ["source(f) \<inter> source(g) = \<emptyset>"]) *}

lemma glue_function2_is_function [typing]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow>
   glue_function2(f,g) \<in> source(f) \<union> source(g) \<rightarrow> target(f) \<union> target(g)" by auto2

lemma glue_function2_eval [rewrite]:
  "is_function(f) \<Longrightarrow> is_function(g) \<Longrightarrow> x \<in> source(glue_function2(f,g)) \<Longrightarrow>
   glue_function2(f,g)`x = (if x \<in> source(f) then f`x else g`x)" by auto2
setup {* del_prfstep_thm @{thm glue_function2_def} *}

lemma glue_function2_bij [backward]:
  "f \<in> A \<cong> B \<Longrightarrow> g \<in> C \<cong> D \<Longrightarrow> A \<inter> C = \<emptyset> \<Longrightarrow> B \<inter> D = \<emptyset> \<Longrightarrow>
   glue_function2(f,g) \<in> (A \<union> C) \<cong> (B \<union> D)" by auto2

section {* Equipotent condition *}

definition equipotent :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "equipotent(S,T) \<longleftrightarrow> (\<exists>f. f \<in> S \<cong> T)"
  
lemma equipotentI [resolve]: "f \<in> S \<cong> T \<Longrightarrow> equipotent(S,T)" by auto2
lemma equipotentE [backward]: "equipotent(S,T) \<Longrightarrow> \<exists>f. f \<in> S \<cong> T" by auto2
setup {* del_prfstep_thm @{thm equipotent_def} *}

lemma equipotent_refl [resolve]: "equipotent(X,X)"
@proof @have "id_fun(X) \<in> X \<cong> X" @qed

lemma equipotent_sym [forward]: "equipotent(S,T) \<Longrightarrow> equipotent(T,S)"
@proof @obtain "f \<in> S \<cong> T" @then @have "bijective(inverse(f))" @qed

lemma equipotent_trans [backward2]: "equipotent(S,T) \<Longrightarrow> equipotent(T,U) \<Longrightarrow> equipotent(S,U)"
@proof @obtain "f \<in> S \<cong> T" @then @obtain "g \<in> T \<cong> U" @then @have "g \<circ> f \<in> S \<cong> U" @qed

lemma bij_is_equiv_meta_real: "equiv_meta_rel(equipotent)" by auto2

lemma equipotent_empty [forward]: "equipotent(X,\<emptyset>) \<Longrightarrow> X = \<emptyset>"
@proof @obtain "f \<in> X \<cong> \<emptyset>" @then @have "X \<rightarrow> \<emptyset> \<noteq> \<emptyset>" @qed

lemma equipotent_singleton [resolve]: "equipotent({a},{b})"
@proof @have "(\<lambda>x\<in>{a}. b\<in>{b}) \<in> {a} \<cong> {b}" @qed

lemma equipotent_union [backward1]:
  "A \<inter> C = \<emptyset> \<Longrightarrow> B \<inter> D = \<emptyset> \<Longrightarrow> equipotent(A,B) \<Longrightarrow> equipotent(C,D) \<Longrightarrow>
   equipotent(A \<union> C, B \<union> D)"
@proof
  @obtain "f \<in> A \<cong> B" @then @obtain "g \<in> C \<cong> D" @then
  @have "glue_function2(f,g) \<in> (A \<union> C) \<cong> (B \<union> D)"
@qed

lemma equipotent_cons [backward1]:
  "x \<notin> A \<Longrightarrow> y \<notin> B \<Longrightarrow> equipotent(A,B) \<Longrightarrow> equipotent(cons(x,A), cons(y,B))"
@proof
  @have "cons(x,A) = {x} \<union> A" @then @have "cons(y,B) = {y} \<union> B"
@qed

lemma equipotent_minus1 [backward]:
  "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> equipotent(S \<midarrow> {a}, S \<midarrow> {b})"
@proof
  @case "a = b" @then
  @have "a \<in> S \<midarrow> {b}" @then @have "b \<in> S \<midarrow> {a}" @then
  @let "T = S \<midarrow> {a} \<midarrow> {b}" @then
  @have "equipotent({b},{a})" @then
  @have "S \<midarrow> {a} = T \<union> {b}" @then @have "S \<midarrow> {b} = T \<union> {a}"
@qed

lemma equipotent_minus1_gen [backward2]:
  "equipotent(A,B) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> equipotent(A \<midarrow> {x}, B \<midarrow> {y})"
@proof
  @obtain "f \<in> A \<cong> B" @then
  @have "equipotent(A \<midarrow> {x}, B \<midarrow> {f`x})" @with
    @have "func_restrict_image(func_restrict(f,A\<midarrow>{x})) \<in> A \<midarrow> {x} \<cong> B \<midarrow> {f`x}" @end
@qed

section {* Schroeder-Bernstein Theorem *}

lemma schroeder_bernstein:
  "injective(f) \<Longrightarrow> injective(g) \<Longrightarrow> f \<in> X \<rightarrow> Y \<Longrightarrow> g \<in> Y \<rightarrow> X \<Longrightarrow> equipotent(X,Y)"
@proof
  @let "X_A = lfp(X, \<lambda>W. X \<midarrow> g``(Y \<midarrow> f``W))" @then
  @let "X_B = X \<midarrow> X_A" "Y_A = f``X_A" "Y_B = Y \<midarrow> Y_A" @then
  @have "X \<midarrow> g``Y_B = X_A" @then
  @have "g``Y_B = X_B" @then
  @let "f' = func_restrict_image(func_restrict(f,X_A))" @then
  @let "g' = func_restrict_image(func_restrict(g,Y_B))" @then
  @have "glue_function2(f', inverse(g')) \<in> (X_A \<union> X_B) \<cong> (Y_A \<union> Y_B)"
@qed

section {* Set of first n natural numbers *}

definition nat_less_range :: "i \<Rightarrow> i" where [rewrite]:
  "nat_less_range(n) = {x\<in>.\<nat>. x <\<^sub>\<nat> n}"
setup {* register_wellform_data ("nat_less_range(n)", ["n \<in> nat"]) *}
notation nat_less_range ("[_]")

lemma nat_less_rangeI [typing2]:
  "m \<in>. \<nat> \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> m <\<^sub>\<nat> n \<Longrightarrow> m \<in> [n]" by auto2

lemma nat_less_range_iff [rewrite]: "n \<in> nat \<Longrightarrow> m \<in> [n] \<longleftrightarrow> m <\<^sub>\<nat> n" by auto2
setup {* del_prfstep_thm @{thm nat_less_range_def} *}

lemma nat_less_range_zero [rewrite]: "[0] = \<emptyset>" by auto2
lemma nat_less_range_empty_iff [rewrite]: "x \<in> nat \<Longrightarrow> [x] = \<emptyset> \<longleftrightarrow> x = 0"
  @proof @case "x \<noteq> 0" @with @have "x >\<^sub>\<nat> 0" @end @qed

lemma nat_less_range_notin [resolve]: "k \<in> nat \<Longrightarrow> k \<notin> [k]" by auto2
lemma nat_less_range_Suc [rewrite_back]: "n \<in> nat \<Longrightarrow> [n +\<^sub>\<nat> 1] = cons(n,[n])" by auto2
lemma nat_less_range_Suc_diff [rewrite]: "n \<in>. \<nat> \<Longrightarrow> [n +\<^sub>\<nat> 1] \<midarrow> {n} = [n]" by auto2

lemma equipotent_nat_less_range_Suc [forward]:
  "m \<in>. \<nat> \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> equipotent([m +\<^sub>\<nat> 1], [n +\<^sub>\<nat> 1]) \<Longrightarrow> equipotent([m], [n])"
@proof @have "[m] = [m +\<^sub>\<nat> 1] \<midarrow> {m}" @then @have "[n] = [n +\<^sub>\<nat> 1] \<midarrow> {n}" @qed

lemma equipotent_is_Suc [forward]:
  "m \<in>. \<nat> \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent([m +\<^sub>\<nat> 1], [n]) \<Longrightarrow> \<exists>n'\<in>nat. n = n' +\<^sub>\<nat> 1" by auto2

lemma equipotent_nat_less_range [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent([m], [n]) \<Longrightarrow> m = n"
@proof @induct "m \<in> nat" "\<forall>n\<in>nat. equipotent([m], [n]) \<longrightarrow> m = n" @qed
setup {* del_prfstep_thm @{thm equipotent_is_Suc} *}

section {* Cardinality on finite sets *}
  
definition finite :: "i \<Rightarrow> o" where [rewrite]:
  "finite(X) \<longleftrightarrow> (\<exists>n\<in>nat. equipotent(X, [n]))"
setup {* add_property_const @{term finite} *}

lemma finiteI [forward]: "n \<in> nat \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> finite(X)" by auto2
lemma finiteD [backward]: "finite(X) \<Longrightarrow> \<exists>n\<in>nat. equipotent(X, [n])" by auto2
setup {* del_prfstep_thm @{thm finite_def} *}

lemma finite_empty [forward]: "finite(\<emptyset>)"
  @proof @have "equipotent(\<emptyset>,[0])" @qed

lemma finite_nat_less_range: "k \<in> nat \<Longrightarrow> finite([k])"
  @proof @have "equipotent([k], [k])" @qed
setup {* add_forward_prfstep_cond @{thm finite_nat_less_range} [with_term "[?k]"] *}

lemma finite_cons [forward]: "finite(X) \<Longrightarrow> finite(cons(a,X))"
@proof
  @contradiction
  @obtain "n\<in>nat" where "equipotent(X, [n])" @then
  @have "equipotent(cons(a,X), [n +\<^sub>\<nat> 1])" @with
    @have "[n +\<^sub>\<nat> 1] = cons(n,[n])" @end
@qed

lemma finite_diff_singleton: "finite(X) \<Longrightarrow> finite(X \<midarrow> {a})"
@proof
  @case "a \<notin> X" @then
  @obtain "n\<in>nat" where "equipotent(X, [n])" @then
  @have "n \<noteq> 0" @then
  @obtain "n'\<in>nat" where "n = n' +\<^sub>\<nat> 1" @then
  @have "equipotent(X \<midarrow> {a}, [n'])" @with @have "[n'] = [n] \<midarrow> {n'}" @end
@qed
setup {* add_forward_prfstep_cond @{thm finite_diff_singleton} [with_term "?X \<midarrow> {?a}"] *}

definition card :: "i \<Rightarrow> i" where [rewrite]:
  "card(X) = (THE n. n \<in> nat \<and> equipotent(X, [n]))"

lemma card_unique [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent(X, [m]) \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> m = n"
@proof @have "equipotent([m], [n])" @qed

lemma card_type [typing]: "finite(X) \<Longrightarrow> card(X) \<in> nat" by auto2
lemma card_equipotent [resolve]: "finite(X) \<Longrightarrow> equipotent(X, [card(X)])" by auto2
lemma cardI [rewrite]: "n \<in> nat \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> card(X) = n" by auto2
setup {* del_prfstep_thm @{thm card_def} *}

lemma card_empty [rewrite]: "card(\<emptyset>) = 0"
@proof @have "equipotent(\<emptyset>, [0])" @qed

lemma card_empty' [forward]: "finite(X) \<Longrightarrow> card(X) = 0 \<Longrightarrow> X = \<emptyset>"
@proof @have "equipotent(X,[0])" @qed

lemma card_nat_less_range [rewrite]: "k \<in> nat \<Longrightarrow> card([k]) = k"
@proof @have "equipotent([k], [k])" @qed

lemma card_cons [rewrite]:
  "finite(X) \<Longrightarrow> a \<notin> X \<Longrightarrow> n = card(X) \<Longrightarrow> card(cons(a,X)) = n +\<^sub>\<nat> 1"
@proof
  @have "equipotent(X,[n])" @then @have "[n +\<^sub>\<nat> 1] = cons(n,[n])" @then
  @have "equipotent(cons(a,X),cons(n,[n]))"
@qed

no_notation nat_less_range ("[_]")

section {* Induction on finite sets *}

lemma card_induct_step [forward]:
  "finite(F) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> card(F) = n +\<^sub>\<nat> 1 \<Longrightarrow> \<exists>a F'. F = cons(a,F') \<and> a \<notin> F' \<and> finite(F') \<and> card(F') = n"
@proof @obtain "a \<in> F" @then @have "F = cons(a,F\<midarrow>{a})" @qed

lemma finite_induct [script_induct]:
  "P(\<emptyset>) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow> finite(F) \<Longrightarrow> P(F)"
@proof
  @let "n = card(F)" @then
  @induct "n \<in> nat" "\<forall>F. finite(F) \<longrightarrow> card(F) = n \<longrightarrow> P(F)"
@qed

lemma finite_nonempty_induct [script_induct]:
  "\<forall>a. P({a}) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow>
   finite(F) \<and> F \<noteq> \<emptyset> \<Longrightarrow> P(F)"
@proof
  @let "n = card(F)" @then @have "1 = 0 +\<^sub>\<nat> 1" @then
  @induct "n \<ge>\<^sub>\<nat> 1" "\<forall>F. finite(F) \<longrightarrow> card(F) = n \<longrightarrow> P(F)"
@qed
setup {* del_prfstep_thm @{thm card_induct_step} *}

section {* Applications *}

lemma subset_finite_step [forward]:
  "\<forall>B. B \<subseteq> A \<longrightarrow> finite(B) \<Longrightarrow> B \<subseteq> cons(a,A) \<Longrightarrow> finite(B)"
@proof
  @case "a \<notin> B" @with @have "B \<subseteq> A" @end
  @have "B = cons(a, B \<inter> A)" @then @have "B \<inter> A \<subseteq> A"
@qed
  
lemma subset_finite [forward]:
  "finite(A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> finite(B)"
@proof @induct "finite(A)" "\<forall>B. B \<subseteq> A \<longrightarrow> finite(B)" @qed
setup {* del_prfstep_thm @{thm subset_finite_step} *}

lemma finite_minus_gen [forward]:
  "finite(A) \<Longrightarrow> finite(A \<midarrow> B)"
@proof @have "A \<midarrow> B \<subseteq> A" @qed
setup {* del_prfstep_thm @{thm finite_diff_singleton} *}

lemma image_finite [forward]:
  "is_function(f) \<Longrightarrow> finite(A) \<Longrightarrow> finite(f `` A)"
@proof
  @have (@rule) "\<forall>x B. f `` cons(x,B) \<subseteq> cons(f`x, f``B)" @then
  @induct "finite(A)" "finite(f `` A)"
@qed

section {* Finite sets contain greatest element *}
  
lemma has_greatest_singleton [backward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> has_greatest(R,{a})"
@proof @have "has_greatest(R,{a}) \<and> greatest(R,{a}) = a" @qed

lemma has_greatest_cons [backward1]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> has_greatest(R,cons(a,X))"
@proof @have "has_greatest(R,cons(a,X)) \<and> greatest(R,cons(a,X)) = max(R,a,greatest(R,X))" @qed

lemma finite_set_has_greatest [backward]:
  "linorder(R) \<Longrightarrow> finite(X) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_greatest(R,X)"
@proof @induct "finite(X) \<and> X \<noteq> \<emptyset>" "X \<subseteq> carrier(R) \<longrightarrow> has_greatest(R,X)" @qed
setup {* add_forward_prfstep_cond @{thm finite_set_has_greatest} [with_term "greatest(?R,?X)"] *}

section {* Other consequences of induction *}

lemma ex_least_nat_less [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. (\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i)) \<and> P(k +\<^sub>\<nat> 1)"
@proof
  @contradiction
  @have (@rule) "\<forall>x\<in>nat. (\<forall>i\<le>\<^sub>\<nat>x. \<not>P(i)) \<longrightarrow> (\<forall>i\<le>\<^sub>\<nat>x+\<^sub>\<nat>1. \<not>P(i))" @with @case "i = x +\<^sub>\<nat> 1" @end
  @induct "n \<in> nat" "\<forall>i\<le>\<^sub>\<nat>n. \<not>P(i)"
@qed
      
lemma ex_nat_split [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. \<not>P(k) \<and> P(k +\<^sub>\<nat> 1)"
@proof @obtain k where "k <\<^sub>\<nat> n" "(\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i))" "P (k +\<^sub>\<nat> 1)" @qed

end
