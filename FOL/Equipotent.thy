(*
  File: Equipotent.thy
  Author: Bohua Zhan

  Equipotence (existence of bijective function) between two sets.
*)

theory Equipotent
  imports Functions Wfrec
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
   glue_function2(f,g) \<in> (A \<union> C) \<cong> (B \<union> D)"
@proof
  @have (@rule) "\<forall>y\<in>B. \<exists>x\<in>A. f`x = y"
  @have (@rule) "\<forall>y\<in>D. \<exists>x\<in>C. g`x = y"
@qed

lemma glue_function2_image1 [rewrite]:
  "surjective(f) \<Longrightarrow> is_function(g) \<Longrightarrow> glue_function2(f,g) `` source(f) = target(f)"
@proof
  @let "h = glue_function2(f,g)"
  @have "\<forall>x. x \<in> h``source(f) \<longleftrightarrow> x \<in> target(f)" @with
    @case "x \<in> h``source(f)" @with
      @obtain y where "y \<in> source(f)" "h`y = x"
    @end
    @case "x \<in> target(f)" @with
      @obtain y where "y \<in> source(f)" "f`y = x"
      @have "h`y = x"
    @end
  @end
@qed

section {* Equipotent condition *}

definition equipotent :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "\<approx>\<^sub>S" 50) where [rewrite]:
  "S \<approx>\<^sub>S T \<longleftrightarrow> (\<exists>f. f \<in> S \<cong> T)"
  
lemma equipotentI [resolve]: "f \<in> S \<cong> T \<Longrightarrow> S \<approx>\<^sub>S T" by auto2
lemma equipotentE [backward]: "S \<approx>\<^sub>S T \<Longrightarrow> \<exists>f. f \<in> S \<cong> T" by auto2
setup {* del_prfstep_thm @{thm equipotent_def} *}

lemma equipotent_refl [resolve]: "X \<approx>\<^sub>S X"
@proof @have "id_fun(X) \<in> X \<cong> X" @qed

lemma equipotent_sym [forward]: "S \<approx>\<^sub>S T \<Longrightarrow> T \<approx>\<^sub>S S"
@proof @obtain "f \<in> S \<cong> T" @have "bijective(inverse(f))" @qed

lemma equipotent_trans [backward2]: "S \<approx>\<^sub>S T \<Longrightarrow> T \<approx>\<^sub>S U \<Longrightarrow> S \<approx>\<^sub>S U"
@proof @obtain "f \<in> S \<cong> T" @obtain "g \<in> T \<cong> U" @have "g \<circ> f \<in> S \<cong> U" @qed

lemma equipotent_empty [forward]: "X \<approx>\<^sub>S \<emptyset> \<Longrightarrow> X = \<emptyset>"
@proof @obtain "f \<in> X \<cong> \<emptyset>" @have "X \<rightarrow> \<emptyset> \<noteq> \<emptyset>" @qed

lemma equipotent_singleton [resolve]: "{a} \<approx>\<^sub>S {b}"
@proof @have "Fun({a}, {b}, \<lambda>x. b) \<in> {a} \<cong> {b}" @qed

lemma equipotent_union [backward1]:
  "A \<inter> C = \<emptyset> \<Longrightarrow> B \<inter> D = \<emptyset> \<Longrightarrow> A \<approx>\<^sub>S B \<Longrightarrow> C \<approx>\<^sub>S D \<Longrightarrow> A \<union> C \<approx>\<^sub>S B \<union> D"
@proof
  @obtain "f \<in> A \<cong> B" @obtain "g \<in> C \<cong> D"
  @have "glue_function2(f,g) \<in> (A \<union> C) \<cong> (B \<union> D)"
@qed

lemma equipotent_cons [backward1]:
  "x \<notin> A \<Longrightarrow> y \<notin> B \<Longrightarrow> A \<approx>\<^sub>S B \<Longrightarrow> cons(x,A) \<approx>\<^sub>S cons(y,B)"
@proof
  @have "cons(x,A) = {x} \<union> A" @have "cons(y,B) = {y} \<union> B"
@qed

lemma equipotent_minus1 [backward]:
  "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> S \<midarrow> {a} \<approx>\<^sub>S S \<midarrow> {b}"
@proof
  @case "a = b"
  @have "a \<in> S \<midarrow> {b}" @have "b \<in> S \<midarrow> {a}"
  @let "T = S \<midarrow> {a} \<midarrow> {b}"
  @have "{b} \<approx>\<^sub>S {a}"
  @have "S \<midarrow> {a} = T \<union> {b}" @have "S \<midarrow> {b} = T \<union> {a}"
@qed

lemma equipotent_minus1_gen [backward2]:
  "A \<approx>\<^sub>S B \<Longrightarrow> x \<in> A \<Longrightarrow> y \<in> B \<Longrightarrow> A \<midarrow> {x} \<approx>\<^sub>S B \<midarrow> {y}"
@proof
  @obtain "f \<in> A \<cong> B"
  @have (@rule) "\<forall>y'\<in>B. \<exists>x\<in>A. f`x = y'"
  @have "A \<midarrow> {x} \<approx>\<^sub>S B \<midarrow> {f`x}" @with
    @have "func_restrict_image(func_restrict(f,A\<midarrow>{x})) \<in> A \<midarrow> {x} \<cong> B \<midarrow> {f`x}"
  @end
@qed

section \<open>Ordering on cardinality\<close>

definition le_potent :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "\<lesssim>\<^sub>S" 50) where [rewrite]:
  "S \<lesssim>\<^sub>S T \<longleftrightarrow> (\<exists>f\<in>S\<rightarrow>T. injective(f))"

lemma le_potentI [resolve]: "injective(f) \<Longrightarrow> f \<in> A \<rightarrow> B \<Longrightarrow> A \<lesssim>\<^sub>S B" by auto2
lemma le_potentE [resolve]: "S \<lesssim>\<^sub>S T \<Longrightarrow> \<exists>f\<in>S\<rightarrow>T. injective(f)" by auto2
setup {* del_prfstep_thm @{thm le_potent_def} *}

definition less_potent :: "i \<Rightarrow> i \<Rightarrow> o"  (infix "\<prec>\<^sub>S" 50) where [rewrite]:
  "S \<prec>\<^sub>S T \<longleftrightarrow> (S \<lesssim>\<^sub>S T \<and> \<not>S \<approx>\<^sub>S T)"

lemma le_potent_trans [forward]:
  "A \<lesssim>\<^sub>S B \<Longrightarrow> B \<lesssim>\<^sub>S C \<Longrightarrow> A \<lesssim>\<^sub>S C"
@proof
  @obtain "f \<in> A \<rightarrow> B" where "injective(f)"
  @obtain "g \<in> B \<rightarrow> C" where "injective(g)"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma le_potent_eq_trans [forward]:
  "A \<approx>\<^sub>S B \<Longrightarrow> B \<lesssim>\<^sub>S C \<Longrightarrow> A \<lesssim>\<^sub>S C"
@proof
  @obtain "f \<in> A \<cong> B"
  @obtain "g \<in> B \<rightarrow> C" where "injective(g)"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma le_potent_trans_eq [forward]:
  "A \<lesssim>\<^sub>S B \<Longrightarrow> B \<approx>\<^sub>S C \<Longrightarrow> A \<lesssim>\<^sub>S C"
@proof
  @obtain "f \<in> A \<rightarrow> B" where "injective(f)"
  @obtain "g \<in> B \<cong> C"
  @let "h = g \<circ> f"
  @have "h \<in> A \<rightarrow> C" @have "injective(h)"
@qed

lemma subset_le_potent [resolve]:
  "S \<subseteq> T \<Longrightarrow> S \<lesssim>\<^sub>S T"
@proof
  @let "f = Fun(S,T,\<lambda>x. x)"
  @have "injective(f)" @have "f \<in> S \<rightarrow> T"
@qed

lemma pow_le_potent [resolve]:
  "S \<lesssim>\<^sub>S Pow(S)"
@proof
  @let "f = Fun(S,Pow(S),\<lambda>x. {x})"
  @have "injective(f)" @have "f \<in> S \<rightarrow> Pow(S)"
@qed

section {* Schroeder-Bernstein Theorem *}

lemma schroeder_bernstein [forward]:
  "X \<lesssim>\<^sub>S Y \<Longrightarrow> Y \<lesssim>\<^sub>S X \<Longrightarrow> X \<approx>\<^sub>S Y"
@proof
  @obtain "f\<in>X\<rightarrow>Y" where "injective(f)"
  @obtain "g\<in>Y\<rightarrow>X" where "injective(g)"
  @let "X_A = lfp(X, \<lambda>W. X \<midarrow> g``(Y \<midarrow> f``W))"
  @let "X_B = X \<midarrow> X_A" "Y_A = f``X_A" "Y_B = Y \<midarrow> Y_A"
  @have "X \<midarrow> g``Y_B = X_A"
  @have "g``Y_B = X_B"
  @let "f' = func_restrict_image(func_restrict(f,X_A))"
  @let "g' = func_restrict_image(func_restrict(g,Y_B))"
  @have "glue_function2(f', inverse(g')) \<in> (X_A \<union> X_B) \<cong> (Y_A \<union> Y_B)"
  @have "X = X_A \<union> X_B" @have "Y = Y_A \<union> Y_B"
@qed

end
