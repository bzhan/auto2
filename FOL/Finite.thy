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
  by (tactic {* auto2s_tac @{context} (HAVE "id_fun(X) \<in> X \<cong> X") *})

lemma equipotent_sym [forward]: "equipotent(S,T) \<Longrightarrow> equipotent(T,S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> S \<cong> T" THEN HAVE "bijective(inverse(f))") *})

lemma equipotent_trans [backward2]: "equipotent(S,T) \<Longrightarrow> equipotent(T,U) \<Longrightarrow> equipotent(S,U)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> S \<cong> T" THEN CHOOSE "g, g \<in> T \<cong> U" THEN
    HAVE "g \<circ> f \<in> S \<cong> U") *})

lemma bij_is_equiv_meta_real: "equiv_meta_rel(equipotent)" by auto2

lemma equipotent_empty [forward]: "equipotent(X,\<emptyset>) \<Longrightarrow> X = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> X \<cong> \<emptyset>" THEN HAVE "X \<rightarrow> \<emptyset> \<noteq> \<emptyset>") *})

lemma equipotent_singleton [resolve]: "equipotent({a},{b})"
  by (tactic {* auto2s_tac @{context} (HAVE "(\<lambda>x\<in>{a}. b\<in>{b}) \<in> {a} \<cong> {b}") *})

lemma equipotent_union [backward1]:
  "A \<inter> C = \<emptyset> \<Longrightarrow> B \<inter> D = \<emptyset> \<Longrightarrow> equipotent(A,B) \<Longrightarrow> equipotent(C,D) \<Longrightarrow>
   equipotent(A \<union> C, B \<union> D)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> A \<cong> B" THEN CHOOSE "g, g \<in> C \<cong> D" THEN
    HAVE "glue_function2(f,g) \<in> (A \<union> C) \<cong> (B \<union> D)") *})

lemma equipotent_cons [backward1]:
  "x \<notin> A \<Longrightarrow> y \<notin> B \<Longrightarrow> equipotent(A,B) \<Longrightarrow> equipotent(cons(x,A), cons(y,B))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "cons(x,A) = {x} \<union> A" THEN HAVE "cons(y,B) = {y} \<union> B") *})

lemma equipotent_minus1 [backward]:
  "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> equipotent(S \<midarrow> {a}, S \<midarrow> {b})"
  by (tactic {* auto2s_tac @{context} (
    CASE "a = b" THEN
    HAVE "a \<in> S \<midarrow> {b}" THEN HAVE "b \<in> S \<midarrow> {a}" THEN
    LET "T = S \<midarrow> {a} \<midarrow> {b}" THEN
    HAVE "equipotent({b},{a})" THEN
    HAVE "S \<midarrow> {a} = T \<union> {b}" THEN HAVE "S \<midarrow> {b} = T \<union> {a}") *})

lemma equipotent_minus1_gen [backward2]:
  "equipotent(A,B) \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> equipotent(A \<midarrow> {x}, B \<midarrow> {y})"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "f, f \<in> A \<cong> B" THEN
    HAVE "equipotent(A \<midarrow> {x}, B \<midarrow> {f`x})" WITH
      HAVE "func_restrict_image(func_restrict(f,A\<midarrow>{x})) \<in> A \<midarrow> {x} \<cong> B \<midarrow> {f`x}") *})

section {* Schroeder-Bernstein Theorem *}

lemma schroeder_bernstein:
  "injective(f) \<Longrightarrow> injective(g) \<Longrightarrow> f \<in> X \<rightarrow> Y \<Longrightarrow> g \<in> Y \<rightarrow> X \<Longrightarrow> equipotent(X,Y)"
  by (tactic {* auto2s_tac @{context} (
    LET "X_A = lfp(X, \<lambda>W. X \<midarrow> g``(Y \<midarrow> f``W))" THEN
    LET "X_B = X \<midarrow> X_A, Y_A = f``X_A, Y_B = Y \<midarrow> Y_A" THEN
    HAVE "X \<midarrow> g``Y_B = X_A" THEN
    HAVE "g``Y_B = X_B" THEN
    LET "f' = func_restrict_image(func_restrict(f,X_A))" THEN
    LET "g' = func_restrict_image(func_restrict(g,Y_B))" THEN
    HAVE "glue_function2(f', inverse(g')) \<in> (X_A \<union> X_B) \<cong> (Y_A \<union> Y_B)") *})

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
  by (tactic {* auto2s_tac @{context} (CASE "x \<noteq> 0" WITH HAVE "x >\<^sub>\<nat> 0") *})

lemma nat_less_range_notin [resolve]: "k \<in> nat \<Longrightarrow> k \<notin> [k]" by auto2
lemma nat_less_range_Suc [rewrite_back]: "n \<in> nat \<Longrightarrow> [n +\<^sub>\<nat> 1] = cons(n,[n])" by auto2
lemma nat_less_range_Suc_diff [rewrite]: "n \<in>. \<nat> \<Longrightarrow> [n +\<^sub>\<nat> 1] \<midarrow> {n} = [n]" by auto2

lemma equipotent_nat_less_range_Suc [forward]:
  "m \<in>. \<nat> \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> equipotent([m +\<^sub>\<nat> 1], [n +\<^sub>\<nat> 1]) \<Longrightarrow> equipotent([m], [n])"
  by (tactic {* auto2s_tac @{context} (
    HAVE "[m] = [m +\<^sub>\<nat> 1] \<midarrow> {m}" THEN HAVE "[n] = [n +\<^sub>\<nat> 1] \<midarrow> {n}") *})

lemma equipotent_is_Suc [forward]:
  "m \<in>. \<nat> \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent([m +\<^sub>\<nat> 1], [n]) \<Longrightarrow> \<exists>n'\<in>nat. n = n' +\<^sub>\<nat> 1" by auto2

lemma equipotent_nat_less_range [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent([m], [n]) \<Longrightarrow> m = n"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "m \<in> nat" "\<forall>n\<in>nat. equipotent([m], [n]) \<longrightarrow> m = n") *})
setup {* del_prfstep_thm @{thm equipotent_is_Suc} *}

section {* Cardinality on finite sets *}
  
definition finite :: "i \<Rightarrow> o" where [rewrite]:
  "finite(X) \<longleftrightarrow> (\<exists>n\<in>nat. equipotent(X, [n]))"
setup {* add_property_const @{term finite} *}

lemma finiteI [forward]: "n \<in> nat \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> finite(X)" by auto2
lemma finiteD [backward]: "finite(X) \<Longrightarrow> \<exists>n\<in>nat. equipotent(X, [n])" by auto2
setup {* del_prfstep_thm @{thm finite_def} *}

lemma finite_empty [forward]: "finite(\<emptyset>)"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent(\<emptyset>,[0])") *})

lemma finite_nat_less_range: "k \<in> nat \<Longrightarrow> finite([k])"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent([k], [k])") *})
setup {* add_forward_prfstep_cond @{thm finite_nat_less_range} [with_term "[?k]"] *}

lemma finite_cons [forward]: "finite(X) \<Longrightarrow> finite(cons(a,X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "n\<in>nat, equipotent(X, [n])" THEN
    HAVE "equipotent(cons(a,X), [n +\<^sub>\<nat> 1])" WITH
      HAVE "[Suc(n)] = cons(n,[n])") *})

lemma finite_diff_singleton: "finite(X) \<Longrightarrow> finite(X \<midarrow> {a})"
  by (tactic {* auto2s_tac @{context} (
    CASE "a \<notin> X" THEN
    CHOOSE "n\<in>nat, equipotent(X, [n])" THEN HAVE "n \<noteq> 0" THEN
    CHOOSE "n'\<in>nat, n = n' +\<^sub>\<nat> 1" THEN
    HAVE "equipotent(X \<midarrow> {a}, [n'])" WITH HAVE "[n'] = [n] \<midarrow> {n'}") *})
setup {* add_forward_prfstep_cond @{thm finite_diff_singleton} [with_term "?X \<midarrow> {?a}"] *}

definition card :: "i \<Rightarrow> i" where [rewrite]:
  "card(X) = (THE n. n \<in> nat \<and> equipotent(X, [n]))"

lemma card_unique [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> equipotent(X, [m]) \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> m = n"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent([m], [n])") *})

lemma card_type [typing]: "finite(X) \<Longrightarrow> card(X) \<in> nat" by auto2
lemma card_equipotent [resolve]: "finite(X) \<Longrightarrow> equipotent(X, [card(X)])" by auto2
lemma cardI [rewrite]: "n \<in> nat \<Longrightarrow> equipotent(X, [n]) \<Longrightarrow> card(X) = n" by auto2
setup {* del_prfstep_thm @{thm card_def} *}

lemma card_empty [rewrite]: "card(\<emptyset>) = 0"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent(\<emptyset>, [0])") *})

lemma card_empty' [forward]: "finite(X) \<Longrightarrow> card(X) = 0 \<Longrightarrow> X = \<emptyset>"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent(X,[0])") *})

lemma card_nat_less_range [rewrite]: "k \<in> nat \<Longrightarrow> card([k]) = k"
  by (tactic {* auto2s_tac @{context} (HAVE "equipotent([k], [k])") *})

lemma card_cons [rewrite]:
  "finite(X) \<Longrightarrow> a \<notin> X \<Longrightarrow> n = card(X) \<Longrightarrow> card(cons(a,X)) = n +\<^sub>\<nat> 1"
  by (tactic {* auto2s_tac @{context} (
    HAVE "equipotent(X,[n])" THEN HAVE "[n +\<^sub>\<nat> 1] = cons(n,[n])" THEN
    HAVE "equipotent(cons(a,X),cons(n,[n]))") *})

no_notation nat_less_range ("[_]")

section {* Induction on finite sets *}

lemma card_induct_step [forward]:
  "finite(F) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> card(F) = n +\<^sub>\<nat> 1 \<Longrightarrow> \<exists>a F'. F = cons(a,F') \<and> a \<notin> F' \<and> finite(F') \<and> card(F') = n"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a, a \<in> F" THEN HAVE "F = cons(a,F\<midarrow>{a})") *})

lemma finite_induct [script_induct]:
  "P(\<emptyset>) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow> finite(F) \<Longrightarrow> P(F)"
  by (tactic {* auto2s_tac @{context} (
    LET "n = card(F)" THEN
    INDUCT_ON "n \<in> nat" "\<forall>F. finite(F) \<longrightarrow> card(F) = n \<longrightarrow> P(F)") *})

lemma finite_nonempty_induct [script_induct]:
  "\<forall>a. P({a}) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow>
   finite(F) \<and> F \<noteq> \<emptyset> \<Longrightarrow> P(F)"
  by (tactic {* auto2s_tac @{context} (
    LET "n = card(F)" THEN HAVE "1 = 0 +\<^sub>\<nat> 1" THEN
    INDUCT_ON "n \<ge>\<^sub>\<nat> 1" "\<forall>F. finite(F) \<longrightarrow> card(F) = n \<longrightarrow> P(F)") *})
setup {* del_prfstep_thm @{thm card_induct_step} *}

section {* Applications *}

lemma subset_finite_step [forward]:
  "\<forall>B. B \<subseteq> A \<longrightarrow> finite(B) \<Longrightarrow> B \<subseteq> cons(a,A) \<Longrightarrow> finite(B)"
  by (tactic {* auto2s_tac @{context} (
    CASE "a \<notin> B" WITH HAVE "B \<subseteq> A" THEN
    HAVE "B = cons(a, B \<inter> A)" THEN HAVE "B \<inter> A \<subseteq> A") *})
  
lemma subset_finite [forward]:
  "finite(A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> finite(B)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "finite(A)" "\<forall>B. B \<subseteq> A \<longrightarrow> finite(B)") *})
setup {* del_prfstep_thm @{thm subset_finite_step} *}

lemma finite_minus_gen [forward]:
  "finite(A) \<Longrightarrow> finite(A \<midarrow> B)"
  by (tactic {* auto2s_tac @{context} (HAVE "A \<midarrow> B \<subseteq> A") *})
setup {* del_prfstep_thm @{thm finite_diff_singleton} *}

lemma image_finite [forward]:
  "is_function(f) \<Longrightarrow> finite(A) \<Longrightarrow> finite(f `` A)"
  by (tactic {* auto2s_tac @{context} (
    HAVE_RULE "\<forall>x B. f `` cons(x,B) \<subseteq> cons(f`x, f``B)" THEN
    INDUCT_ON "finite(A)" "finite(f `` A)") *})

section {* Finite sets contain greatest element *}
  
lemma has_greatest_singleton [backward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> has_greatest(R,{a})"
  by (tactic {* auto2s_tac @{context} (
    HAVE "has_greatest(R,{a}) \<and> greatest(R,{a}) = a") *})

lemma has_greatest_cons [backward1]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_greatest(R,X) \<Longrightarrow> has_greatest(R,cons(a,X))"
  by (tactic {* auto2s_tac @{context} (
    HAVE "has_greatest(R,cons(a,X)) \<and> greatest(R,cons(a,X)) = max(R,a,greatest(R,X))") *})

lemma finite_set_has_greatest [backward]:
  "linorder(R) \<Longrightarrow> finite(X) \<Longrightarrow> X \<noteq> \<emptyset> \<Longrightarrow> X \<subseteq> carrier(R) \<Longrightarrow> has_greatest(R,X)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "finite(X) \<and> X \<noteq> \<emptyset>" "X \<subseteq> carrier(R) \<longrightarrow> has_greatest(R,X)") *})
setup {* add_forward_prfstep_cond @{thm finite_set_has_greatest} [with_term "greatest(?R,?X)"] *}

section {* Other consequences of induction *}

lemma ex_least_nat_less [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. (\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i)) \<and> P(k +\<^sub>\<nat> 1)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> nat" "\<forall>i\<le>\<^sub>\<nat>n. \<not>P(i)" THEN
    HAVE "\<forall>x\<in>nat. (\<forall>i\<le>\<^sub>\<nat>x. \<not>P(i)) \<longrightarrow> (\<forall>i\<le>\<^sub>\<nat>x+\<^sub>\<nat>1. \<not>P(i))" WITH CASE "i = x +\<^sub>\<nat> 1") *})
      
lemma ex_nat_split [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. \<not>P(k) \<and> P(k +\<^sub>\<nat> 1)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "k <\<^sub>\<nat> n, (\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i)) \<and> P (k +\<^sub>\<nat> 1)") *})

end
