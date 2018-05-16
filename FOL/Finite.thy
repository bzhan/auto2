theory Finite
  imports Nat
begin

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

lemma equipotent_nat_less_range [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> [m] \<approx>\<^sub>S [n] \<Longrightarrow> m = n"
@proof
  @var_induct "m \<in> nat" arbitrary n @with
    @subgoal "m = m' +\<^sub>\<nat> 1"
      @obtain "n'\<in>nat" where "n = n' +\<^sub>\<nat> 1"
      @have "[m'] = [m' +\<^sub>\<nat> 1] \<midarrow> {m'}"
      @have "[n'] = [n' +\<^sub>\<nat> 1] \<midarrow> {n'}"
      @have "[m'] \<approx>\<^sub>S [n']"
    @endgoal
  @end
@qed

section {* Cardinality on finite sets *}
  
definition finite :: "i \<Rightarrow> o" where [rewrite]:
  "finite(X) \<longleftrightarrow> (\<exists>n\<in>nat. X \<approx>\<^sub>S [n])"
setup {* add_property_const @{term finite} *}

lemma finiteI [forward]: "n \<in> nat \<Longrightarrow> X \<approx>\<^sub>S [n] \<Longrightarrow> finite(X)" by auto2
lemma finiteD [backward]: "finite(X) \<Longrightarrow> \<exists>n\<in>nat. X \<approx>\<^sub>S [n]" by auto2
setup {* del_prfstep_thm @{thm finite_def} *}

lemma finite_empty [forward]: "finite(\<emptyset>)"
  @proof @have "\<emptyset> \<approx>\<^sub>S [0]" @qed

lemma finite_nat_less_range: "k \<in> nat \<Longrightarrow> finite([k])"
  @proof @have "[k] \<approx>\<^sub>S [k]" @qed
setup {* add_forward_prfstep_cond @{thm finite_nat_less_range} [with_term "[?k]"] *}

lemma finite_cons [forward]: "finite(X) \<Longrightarrow> finite(cons(a,X))"
@proof
  @contradiction
  @obtain "n\<in>nat" where "X \<approx>\<^sub>S [n]"
  @have "cons(a,X) \<approx>\<^sub>S [n +\<^sub>\<nat> 1]" @with
    @have "[n +\<^sub>\<nat> 1] = cons(n,[n])" @end
@qed

lemma finite_diff_singleton: "finite(X) \<Longrightarrow> finite(X \<midarrow> {a})"
@proof
  @case "a \<notin> X"
  @obtain "n\<in>nat" where "X \<approx>\<^sub>S [n]"
  @have "n \<noteq> 0"
  @obtain "n'\<in>nat" where "n = n' +\<^sub>\<nat> 1"
  @have "X \<midarrow> {a} \<approx>\<^sub>S [n']" @with @have "[n'] = [n] \<midarrow> {n'}" @end
@qed
setup {* add_forward_prfstep_cond @{thm finite_diff_singleton} [with_term "?X \<midarrow> {?a}"] *}

definition card :: "i \<Rightarrow> i" where [rewrite]:
  "card(X) = (THE n. n \<in> nat \<and> X \<approx>\<^sub>S [n])"

lemma card_unique [forward]:
  "m \<in> nat \<Longrightarrow> n \<in> nat \<Longrightarrow> X \<approx>\<^sub>S [m] \<Longrightarrow> X \<approx>\<^sub>S [n] \<Longrightarrow> m = n"
@proof @have "[m] \<approx>\<^sub>S [n]" @qed

lemma card_type [typing]: "finite(X) \<Longrightarrow> card(X) \<in> nat" by auto2
lemma card_equipotent [resolve]: "finite(X) \<Longrightarrow> X \<approx>\<^sub>S [card(X)]" by auto2
lemma cardI [rewrite]: "n \<in> nat \<Longrightarrow> X \<approx>\<^sub>S [n] \<Longrightarrow> card(X) = n" by auto2
setup {* del_prfstep_thm @{thm card_def} *}

lemma card_empty [rewrite]: "card(\<emptyset>) = 0"
@proof @have "\<emptyset> \<approx>\<^sub>S [0]" @qed

lemma card_empty' [forward]: "finite(X) \<Longrightarrow> card(X) = 0 \<Longrightarrow> X = \<emptyset>"
@proof @have "X \<approx>\<^sub>S [0]" @qed

lemma card_nat_less_range [rewrite]: "k \<in> nat \<Longrightarrow> card([k]) = k"
@proof @have "[k] \<approx>\<^sub>S [k]" @qed

lemma card_cons [rewrite]:
  "finite(X) \<Longrightarrow> a \<notin> X \<Longrightarrow> n = card(X) \<Longrightarrow> card(cons(a,X)) = n +\<^sub>\<nat> 1"
@proof
  @have "X \<approx>\<^sub>S [n]" @have "[n +\<^sub>\<nat> 1] = cons(n,[n])"
  @have "cons(a,X) \<approx>\<^sub>S cons(n,[n])"
@qed

no_notation nat_less_range ("[_]")

section {* Induction on finite sets *}

lemma card_Suc_elim [resolve]:
  "finite(F) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> card(F) = n +\<^sub>\<nat> 1 \<Longrightarrow> \<exists>a F'. F = cons(a,F') \<and> a \<notin> F' \<and> finite(F') \<and> card(F') = n"
@proof @obtain "a \<in> F" @have "F = cons(a,F\<midarrow>{a})" @qed
setup {* del_prfstep_thm @{thm finite_diff_singleton} *}

lemma card_1_elim [backward]:
  "finite(F) \<Longrightarrow> card(F) = 1 \<Longrightarrow> \<exists>a. F = {a}"
@proof
  @have "1 = 0 +\<^sub>\<nat> 1"
  @obtain a F' where "F = cons(a,F') \<and> a \<notin> F' \<and> finite(F') \<and> card(F') = 0"
@qed

lemma finite_induct [var_induct]:
  "finite(F) \<Longrightarrow> P(\<emptyset>) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow> P(F)"
@proof
  @let "n = card(F)"
  @var_induct "n \<in> nat" arbitrary F @with
    @subgoal "n = n' +\<^sub>\<nat> 1"
      @obtain a F' where "F = cons(a,F')" "a \<notin> F'" "finite(F')" "card(F') = n'"
    @endgoal
  @end
@qed

lemma finite_nonempty_induct [var_induct]:
  "finite(F) \<and> F \<noteq> \<emptyset> \<Longrightarrow>
   \<forall>a. P({a}) \<Longrightarrow> \<forall>a X. finite(X) \<longrightarrow> X \<noteq> \<emptyset> \<longrightarrow> a \<notin> X \<longrightarrow> P(X) \<longrightarrow> P(cons(a,X)) \<Longrightarrow> P(F)"
@proof
  @let "n = card(F)"
  @var_induct "n \<ge>\<^sub>\<nat> 1" for "finite(F) \<longrightarrow> n = card(F) \<longrightarrow> P(F)" arbitrary F @with
    @subgoal "n = 1"
      @obtain a where "F = {a}"
    @endgoal
    @subgoal "n = n' +\<^sub>\<nat> 1"
      @obtain a F' where "F = cons(a,F')" "a \<notin> F'" "finite(F')" "card(F') = n'"
    @endgoal
  @end
@qed

section {* Applications *}

lemma subset_finite [forward]: "finite(A) \<Longrightarrow> B \<subseteq> A \<Longrightarrow> finite(B)"
@proof
  @var_induct "finite(A)" arbitrary B @with
    @subgoal "A = cons(a,A')"
      @case "a \<notin> B" @with @have "B \<subseteq> A'" @end
      @have "B = cons(a, B \<inter> A')" @have "B \<inter> A' \<subseteq> A'"
    @endgoal
  @end
@qed

lemma finite_minus_gen [forward]: "finite(A) \<Longrightarrow> finite(A \<midarrow> B)"
@proof @have "A \<midarrow> B \<subseteq> A" @qed

lemma image_finite [forward]: "is_function(f) \<Longrightarrow> finite(A) \<Longrightarrow> finite(f `` A)"
@proof
  @var_induct "finite(A)" @with
    @subgoal "A = cons(x,A')"
      @have "f `` cons(x,A') \<subseteq> cons(f ` x, f `` A')"
    @endgoal
  @end
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
@proof @var_induct "finite(X) \<and> X \<noteq> \<emptyset>" @qed
setup {* add_forward_prfstep_cond @{thm finite_set_has_greatest} [with_term "greatest(?R,?X)"] *}

section {* Other consequences of induction *}

lemma ex_least_nat_less [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. (\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i)) \<and> P(k +\<^sub>\<nat> 1)"
@proof
  @contradiction
  @have (@rule) "\<forall>x\<in>nat. \<forall>i\<le>\<^sub>\<nat>x. \<not>P(i)" @with
    @var_induct "x \<in> nat" for "\<forall>i\<le>\<^sub>\<nat>x. \<not>P(i)" @with
      @subgoal "x = x' +\<^sub>\<nat> 1" @case "i = x' +\<^sub>\<nat> 1" @endgoal
    @end
  @end
@qed

lemma ex_nat_split [backward1]:
  "n \<in> nat \<Longrightarrow> \<not>P(0) \<Longrightarrow> P(n) \<Longrightarrow> \<exists>k<\<^sub>\<nat>n. \<not>P(k) \<and> P(k +\<^sub>\<nat> 1)"
@proof @obtain k where "k <\<^sub>\<nat> n" "(\<forall>i\<le>\<^sub>\<nat>k. \<not>P(i))" "P(k +\<^sub>\<nat> 1)" @qed

end
