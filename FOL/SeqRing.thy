theory SeqRing
imports Sequence
begin

section {* Construction of the ring of sequences *}

definition seq_ring :: "i \<Rightarrow> i" where [rewrite]:
  "seq_ring(R) = Ring(seqs(R), Seq(R,\<lambda>n. \<zero>\<^sub>R), \<lambda>X Y. Seq(R,\<lambda>n. X`n +\<^sub>R Y`n),
                               Seq(R,\<lambda>n. \<one>\<^sub>R), \<lambda>X Y. Seq(R,\<lambda>n. X`n *\<^sub>R Y`n))"

lemma seq_ring_is_ring_raw [forward]:
  "is_ring_raw(R) \<Longrightarrow> ring_form(seq_ring(R))" by auto2

lemma seq_ring_carrier [rewrite_bidir]:
  "carrier(seq_ring(R)) = seqs(R)" by auto2

lemma seq_ring_eval [rewrite]:
  "is_ring_raw(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> n \<in> source(\<zero>\<^sub>S) \<Longrightarrow> (\<zero>\<^sub>S)`n = \<zero>\<^sub>R"
  "is_ring_raw(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> n \<in> source(\<one>\<^sub>S) \<Longrightarrow> (\<one>\<^sub>S)`n = \<one>\<^sub>R"
  "is_ring_raw(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> n \<in> source(X +\<^sub>S Y) \<Longrightarrow> (X +\<^sub>S Y)`n = X`n +\<^sub>R Y`n"
  "is_ring_raw(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> n \<in> source(X *\<^sub>S Y) \<Longrightarrow> (X *\<^sub>S Y)`n = X`n *\<^sub>R Y`n"
  by auto2+
setup {* del_prfstep_thm @{thm seq_ring_def} *}

lemma seq_ring_zero_neq_one [resolve]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> \<zero>\<^sub>S \<noteq> \<one>\<^sub>S"
  by (tactic {* auto2s_tac @{context} (HAVE "(\<zero>\<^sub>S)`0 = (\<one>\<^sub>S)`0") *})

lemma seq_ring_plus_assoc [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> Z \<in>. S \<Longrightarrow> (X +\<^sub>S Y) +\<^sub>S Z = X +\<^sub>S (Y +\<^sub>S Z)"
  by (tactic {* auto2s_tac @{context} (
    HAVE_RULE "\<forall>n\<in>.\<nat>. (X`n +\<^sub>R Y`n) +\<^sub>R Z`n = X`n +\<^sub>R (Y`n +\<^sub>R Z`n)") *})

lemma seq_ring_times_assoc [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> Z \<in>. S \<Longrightarrow> (X *\<^sub>S Y) *\<^sub>S Z = X *\<^sub>S (Y *\<^sub>S Z)"
  by (tactic {* auto2s_tac @{context} (
    HAVE_RULE "\<forall>n\<in>.\<nat>. (X`n *\<^sub>R Y`n) *\<^sub>R Z`n = X`n *\<^sub>R (Y`n *\<^sub>R Z`n)") *})

lemma seq_ring_has_add_inverse [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> X +\<^sub>S seq_neg(X) = \<zero>\<^sub>S" by auto2

lemma seq_ring_left_distrib [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> Z \<in>. S \<Longrightarrow>
   X *\<^sub>S (Y +\<^sub>S Z) = X *\<^sub>S Y +\<^sub>S X *\<^sub>S Z"
  by (tactic {* auto2s_tac @{context} (
    HAVE_RULE "\<forall>n\<in>.\<nat>. X`n *\<^sub>R (Y`n +\<^sub>R Z`n) = X`n *\<^sub>R Y`n +\<^sub>R X`n *\<^sub>R Z`n") *})

lemma seq_ring_add_id [forward]: "is_comm_ring(R) \<Longrightarrow> is_add_id(seq_ring(R))" by auto2
lemma seq_ring_mult_id [forward]: "is_comm_ring(R) \<Longrightarrow> is_mult_id(seq_ring(R))" by auto2

lemma seq_ring_is_comm_ring [forward]:
  "is_comm_ring(R) \<Longrightarrow> is_comm_ring(seq_ring(R))"
  by (tactic {* auto2s_tac @{context} (
    LET "S = seq_ring(R)" THEN
    HAVE "has_add_inverse(S)" WITH
      HAVE "\<forall>X\<in>.S. X +\<^sub>S seq_neg(X) = \<zero>\<^sub>S" THEN
    HAVE "is_times_comm(S)") *})

lemma seq_ring_uminus [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> n \<in> source(-\<^sub>S X) \<Longrightarrow> (-\<^sub>S X)`n = -\<^sub>R (X`n)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "-\<^sub>S X = seq_neg(X)" WITH HAVE "X +\<^sub>S seq_neg(X) = \<zero>\<^sub>S") *})

lemma seq_ring_eval_minus [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> n \<in> source(X -\<^sub>S Y) \<Longrightarrow> (X -\<^sub>S Y)`n = X`n -\<^sub>R Y`n"
  by (tactic {* auto2s_tac @{context} (
    HAVE "X -\<^sub>S Y = X +\<^sub>S (-\<^sub>S Y)" THEN HAVE "X`n -\<^sub>R Y`n = X`n +\<^sub>R -\<^sub>R Y`n") *})

setup {* fold del_prfstep_thm [@{thm seq_ring_zero_neq_one}, @{thm seq_ring_plus_assoc},
  @{thm seq_ring_times_assoc}, @{thm seq_ring_has_add_inverse}, @{thm seq_ring_left_distrib}] *}

(* Inverse of a sequence: invert all entries, except keeping 0 unchanged. *)

definition inv_gen :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "inv_gen(R,x) = (if x \<in> units(R) then inv(R,x) else \<zero>\<^sub>R)"

lemma inv_gen_type [typing]: "is_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> inv_gen(R,x) \<in>. R" by auto2
lemma inv_gen_eval [rewrite]: "is_ring(R) \<Longrightarrow> x \<in> units(R) \<Longrightarrow> inv_gen(R,x) = inv(R,x)" by auto2
setup {* del_prfstep_thm @{thm inv_gen_def} *}

definition seq_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "seq_inverse(X) = (let R = target_str(X) in Seq(R,\<lambda>n. inv_gen(R,X`n)))"

lemma seq_inverse_type [typing]:
  "ord_field_seq(X) \<Longrightarrow> seq_inverse(X) \<in> seqs(target_str(X))" by auto2

lemma eval_seq_inverse [rewrite]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<in> source(seq_inverse(X)) \<Longrightarrow> X`n \<in> units(R) \<Longrightarrow>
   seq_inverse(X)`n = inv(R,X`n)" by auto2
setup {* del_prfstep_thm @{thm seq_inverse_def} *}

section {* Property on vanishes condition *}

lemma vanishes_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X +\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "s, t, s >\<^sub>R \<zero>\<^sub>R \<and> t >\<^sub>R \<zero>\<^sub>R \<and> r = s +\<^sub>R t" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n\<bar>\<^sub>R <\<^sub>R s" THEN
    CHOOSE "j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R t" THEN
    HAVE "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r") *})
setup {* add_forward_prfstep_cond @{thm vanishes_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma vanishes_minus:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> vanishes(X) \<Longrightarrow> vanishes(-\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" THEN HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r") *})
setup {* add_forward_prfstep_cond @{thm vanishes_minus} [with_term "-\<^sub>?S ?X"] *}

lemma vanishes_minus' [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> vanishes(-\<^sub>S X) \<Longrightarrow> vanishes(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "X = -\<^sub>S (-\<^sub>S X)") *})

lemma vanishes_diff:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X -\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (HAVE "X -\<^sub>S Y = X +\<^sub>S (-\<^sub>S Y)") *})
setup {* add_forward_prfstep_cond @{thm vanishes_diff} [with_term "?X -\<^sub>?S ?Y"] *}

lemma vanishes_diff' [rewrite]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(X) \<longleftrightarrow> vanishes(Y)"
  by (tactic {* auto2s_tac @{context} (
    CASE "vanishes(X)" WITH HAVE "X -\<^sub>S (X -\<^sub>S Y) = Y" THEN
    CASE "vanishes(Y)" WITH HAVE "Y +\<^sub>S (X -\<^sub>S Y) = X") *})

lemma vanishes_mult_bounded:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   bounded(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X *\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a >\<^sub>R \<zero>\<^sub>R, \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R a" THEN
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R r /\<^sub>R a" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r") *})
setup {* add_forward_prfstep_cond @{thm vanishes_mult_bounded} [with_term "?X *\<^sub>?S ?Y"] *}

lemma vanishes_mult_bounded2:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   bounded(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(Y *\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (HAVE "X *\<^sub>S Y = Y *\<^sub>S X") *})
setup {* add_forward_prfstep_cond @{thm vanishes_mult_bounded2} [with_term "?Y *\<^sub>?S ?X"] *}

lemma vanishes_limit_equal [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> vanishes(X -\<^sub>S Y) \<Longrightarrow>
   converges_to(X,x) \<Longrightarrow> converges_to(Y,x)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, t >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R t" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R t" THEN
    CHOOSE "j\<ge>\<^sub>\<nat>i, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R s" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R r") *})

section {* Property on Cauchy condition *}
  
lemma cauchy_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X +\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X +\<^sub>S Y)`m -\<^sub>R (X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, t >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R t" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s" THEN
    CHOOSE "j\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t" THEN
    HAVE "\<forall>m \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X +\<^sub>S Y)`m -\<^sub>R (X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r" WITH
      HAVE "(X`m +\<^sub>R Y`m) -\<^sub>R (X`n +\<^sub>R Y`n) = (X`m -\<^sub>R X`n) +\<^sub>R (Y`m -\<^sub>R Y`n)") *})
setup {* add_forward_prfstep_cond @{thm cauchy_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma cauchy_minus:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> cauchy(-\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`m -\<^sub>R (-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "k\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r" THEN
    HAVE "\<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`m -\<^sub>R (-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r" WITH
      HAVE "-\<^sub>R (X`m) -\<^sub>R (-\<^sub>R X`n) = X`n -\<^sub>R X`m") *})
setup {* add_forward_prfstep_cond @{thm cauchy_minus} [with_term "-\<^sub>?S ?X"] *}

lemma cauchy_minus' [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(-\<^sub>S X) \<Longrightarrow> cauchy(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "X = -\<^sub>S (-\<^sub>S X)") *})
    
lemma cauchy_diff:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X -\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (HAVE "X -\<^sub>S Y = X +\<^sub>S -\<^sub>S Y") *})
setup {* add_forward_prfstep_cond @{thm cauchy_diff} [with_term "?X -\<^sub>?S ?Y"] *}

lemma cauchy_mult:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X *\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`m -\<^sub>R (X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "a >\<^sub>R \<zero>\<^sub>R, \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R a" THEN
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, \<forall>n\<in>.\<nat>. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R b" THEN
    CHOOSE "s, t, s >\<^sub>R \<zero>\<^sub>R \<and> t >\<^sub>R \<zero>\<^sub>R \<and> r = s +\<^sub>R t" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s /\<^sub>R b" THEN
    CHOOSE "j\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t /\<^sub>R a" THEN
    HAVE "\<forall>m \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X *\<^sub>S Y)`m -\<^sub>R (X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r" WITH
      (HAVE "(X`m *\<^sub>R Y`m) -\<^sub>R (X`n *\<^sub>R Y`n) = (X`m -\<^sub>R X`n) *\<^sub>R Y`n +\<^sub>R X`m *\<^sub>R (Y`m -\<^sub>R Y`n)" THEN
       HAVE "\<bar>X`m *\<^sub>R (Y`m -\<^sub>R Y`n)\<bar>\<^sub>R <\<^sub>R t")) *})
setup {* add_forward_prfstep_cond @{thm cauchy_mult} [with_term "?X *\<^sub>?S ?Y"] *}

lemma cauchy_inverse:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   cauchy(seq_inverse(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>seq_inverse(X)`m -\<^sub>R seq_inverse(X)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R" THEN
    CHOOSE "j \<ge>\<^sub>\<nat> i, \<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r *\<^sub>R (b *\<^sub>R b)" THEN
    HAVE "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>seq_inverse(X)`m -\<^sub>R seq_inverse(X)`n\<bar>\<^sub>R <\<^sub>R r" WITH (
      HAVE "b *\<^sub>R b <\<^sub>R \<bar>X`m *\<^sub>R X`n\<bar>\<^sub>R" THEN
      HAVE "inv(R,X`m) -\<^sub>R inv(R,X`n) = (X`n -\<^sub>R X`m) /\<^sub>R (X`m *\<^sub>R X`n)")) *})
setup {* add_forward_prfstep_cond @{thm cauchy_inverse} [with_term "seq_inverse(?X)"] *}

lemma vanishes_diff_inverse [backward1]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow> \<not>vanishes(Y) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(seq_inverse(X) -\<^sub>S seq_inverse(Y))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(seq_inverse(X) -\<^sub>S seq_inverse(Y))`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "a >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. a <\<^sub>R \<bar>X`n\<bar>\<^sub>R" THEN
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. b <\<^sub>R \<bar>Y`n\<bar>\<^sub>R" THEN
    CHOOSE "k \<ge>\<^sub>\<nat> max(\<nat>,i,j), \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r *\<^sub>R (a *\<^sub>R b)" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(seq_inverse(X) -\<^sub>S seq_inverse(Y))`n\<bar>\<^sub>R <\<^sub>R r" WITH (
      HAVE "a *\<^sub>R b <\<^sub>R \<bar>X`n *\<^sub>R Y`n\<bar>\<^sub>R" THEN
      HAVE "inv(R,X`n) -\<^sub>R inv(R,Y`n) = (Y`n -\<^sub>R X`n) /\<^sub>R (X`n *\<^sub>R Y`n)")) *})

lemma seq_inverse_is_inverse [backward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   vanishes(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)`n\<bar>\<^sub>R <\<^sub>R r") *})

section {* Positive sequences *}
  
definition pos_seq :: "i \<Rightarrow> o" where [rewrite]:
  "pos_seq(X) \<longleftrightarrow> (let R = target_str(X) in \<exists>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r)"
setup {* add_property_const @{term pos_seq} *}

lemma pos_seqI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> pos_seq(X)" by auto2

lemma pos_seqD [resolve]:
  "pos_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r" by auto2
setup {* del_prfstep_thm @{thm pos_seq_def} *}
  
lemma pos_seq_compat_vanishes [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> pos_seq(X) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> pos_seq(Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, t >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R t" THEN
    CHOOSE "j \<ge>\<^sub>\<nat> i, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R s" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>j. Y`n >\<^sub>R t" WITH (
      HAVE "X`n -\<^sub>R Y`n <\<^sub>R s" THEN HAVE "X`n = (X`n -\<^sub>R Y`n) +\<^sub>R Y`n")) *})
      
lemma pos_seq_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   pos_seq(X) \<Longrightarrow> pos_seq(Y) \<Longrightarrow> pos_seq(X +\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. s <\<^sub>R X`n" THEN
    CHOOSE "t >\<^sub>R \<zero>\<^sub>R, j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. t <\<^sub>R Y`n" THEN
    HAVE "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). s +\<^sub>R t <\<^sub>R (X +\<^sub>S Y)`n" THEN
    HAVE "s +\<^sub>R t >\<^sub>R \<zero>\<^sub>R") *})
setup {* add_forward_prfstep_cond @{thm pos_seq_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma pos_seq_mult:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   pos_seq(X) \<Longrightarrow> pos_seq(Y) \<Longrightarrow> pos_seq(X *\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. s <\<^sub>R X`n" THEN
    CHOOSE "t >\<^sub>R \<zero>\<^sub>R, j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. t <\<^sub>R Y`n" THEN
    HAVE "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). s *\<^sub>R t <\<^sub>R (X *\<^sub>S Y)`n" THEN HAVE "s *\<^sub>R t >\<^sub>R \<zero>\<^sub>R") *})
setup {* add_forward_prfstep_cond @{thm pos_seq_mult} [with_term "?X *\<^sub>?S ?Y"] *}

lemma non_vanishes_pos_seq_cases [backward1]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   \<not>pos_seq(X) \<Longrightarrow> pos_seq(-\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, k\<in>.\<nat>, (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n) \<or> (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R X`n)" THEN
    CASE "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n" WITH HAVE "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R (-\<^sub>S X)`n") *})
      
lemma pos_seq_minus [resolve]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> pos_seq(X) \<Longrightarrow> \<not>pos_seq(-\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. (-\<^sub>S X)`n >\<^sub>R s" THEN
    LET "k = max(\<nat>,i,j)" THEN
    HAVE "(-\<^sub>S X)`k >\<^sub>R s" THEN HAVE "X`k >\<^sub>R r") *})

definition nonneg_seq :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_seq(X) \<longleftrightarrow> pos_seq(X) \<or> vanishes(X)"
setup {* add_property_const @{term nonneg_seq} *}
  
lemma nonneg_seq_compat_vanishes [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> nonneg_seq(X) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> nonneg_seq(Y)" by auto2

lemma nonneg_seq_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   nonneg_seq(X) \<Longrightarrow> nonneg_seq(Y) \<Longrightarrow> nonneg_seq(X +\<^sub>S Y)"
  by (tactic {* auto2s_tac @{context} (
    CASE "vanishes(X) \<and> pos_seq(Y)" WITH HAVE "-\<^sub>S X = Y -\<^sub>S (X +\<^sub>S Y)" THEN
    CASE "pos_seq(X) \<and> vanishes(Y)" WITH HAVE "-\<^sub>S Y = X -\<^sub>S (X +\<^sub>S Y)") *})
setup {* add_forward_prfstep_cond @{thm nonneg_seq_add} [with_term "?X +\<^sub>?S ?Y"] *}

section {* Characterization of non-positive sequences *}
  
lemma pos_seq_not_vanish [resolve]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> pos_seq(X) \<Longrightarrow> \<not>vanishes(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r" THEN
    CHOOSE "j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" THEN
    HAVE "\<bar>X`max(\<nat>,i,j)\<bar>\<^sub>R <\<^sub>R r" THEN HAVE "X`max(\<nat>,i,j) >\<^sub>R r") *})

lemma not_positive_to_nonneg_uminus [rewrite_back]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> cauchy(X) \<Longrightarrow>
   \<not>pos_seq(X) \<longleftrightarrow> nonneg_seq(-\<^sub>S X)"
  by (tactic {* auto2s_tac @{context} (
    CASE "vanishes(X)" THEN HAVE "pos_seq(X) \<or> pos_seq(-\<^sub>S X)") *})

lemma not_positiveD [backward2]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<not>pos_seq(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow>
   \<exists>k\<ge>\<^sub>\<nat>i. r \<ge>\<^sub>R X`k"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r") *})

lemma not_positive' [rewrite_back]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow>
   \<not>pos_seq(X) \<longleftrightarrow> (\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)"
  by (tactic {* auto2s_tac @{context} (
    CASE "\<not>pos_seq(X)" WITH (
      CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)" THEN
      CHOOSE "s >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R s" THEN
      CHOOSE "i\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s" THEN
      CHOOSE "k \<ge>\<^sub>\<nat> i, s \<ge>\<^sub>R X`k" THEN
      HAVE "\<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r") THEN
    CASE "pos_seq(X)" WITH (
      CHOOSE "r >\<^sub>R \<zero>\<^sub>R, i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. r <\<^sub>R X`n" THEN
      CHOOSE "j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. X`n \<le>\<^sub>R r" THEN
      CHOOSE "k\<in>.\<nat>, k \<ge>\<^sub>\<nat> i \<and> k \<ge>\<^sub>\<nat> j" THEN
      HAVE "X`k \<le>\<^sub>R r")) *})

lemma not_positive [rewrite]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> cauchy(X) \<Longrightarrow>
   nonneg_seq(-\<^sub>S X) \<longleftrightarrow> (\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)" by auto2
setup {* fold del_prfstep_thm [@{thm not_positive_to_nonneg_uminus}, @{thm not_positive'}] *}

section {* Constant sequences *}
  
lemma seq_const_zero [rewrite_bidir]:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> {\<zero>\<^sub>R}\<^sub>R = \<zero>\<^sub>S" by auto2
  
lemma seq_const_one [rewrite_bidir]:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> {\<one>\<^sub>R}\<^sub>R = \<one>\<^sub>S" by auto2
    
lemma seq_const_add [rewrite_bidir]:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> {a +\<^sub>R b}\<^sub>R = {a}\<^sub>R +\<^sub>S {b}\<^sub>R" by auto2

lemma seq_const_minus [rewrite_bidir]:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> {a -\<^sub>R b}\<^sub>R = {a}\<^sub>R -\<^sub>S {b}\<^sub>R" by auto2
  
lemma seq_const_mult [rewrite_bidir]:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> {a *\<^sub>R b}\<^sub>R = {a}\<^sub>R *\<^sub>S {b}\<^sub>R" by auto2

lemma seq_const_inv [rewrite_bidir]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> a \<in> units(R) \<Longrightarrow> seq_inverse({a}\<^sub>R) = {inv(R,a)}\<^sub>R"
  by (tactic {* auto2s_tac @{context} (HAVE_RULE "\<forall>n\<in>nat. {a}\<^sub>R`n \<in> units(R)") *})

lemma vanishes_zero [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> vanishes({c}\<^sub>R) \<longleftrightarrow> c = \<zero>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    CASE "vanishes({c}\<^sub>R)" WITH (
      CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R \<bar>c\<bar>\<^sub>R" THEN
      HAVE "\<bar>{c}\<^sub>R`k\<bar>\<^sub>R <\<^sub>R \<bar>c\<bar>\<^sub>R") THEN
    CASE "c = \<zero>\<^sub>R" WITH (
      CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r)" THEN
      HAVE "\<forall>n\<ge>\<^sub>\<nat>0. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r")) *})
      
lemma cauchy_const [backward]:
  "is_ord_field(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> cauchy({c}\<^sub>R)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`m -\<^sub>R {c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    HAVE "\<forall>m\<ge>\<^sub>\<nat>0. \<forall>n\<ge>\<^sub>\<nat>0. \<bar>{c}\<^sub>R`m -\<^sub>R {c}`n\<bar>\<^sub>R <\<^sub>R r") *})

end
