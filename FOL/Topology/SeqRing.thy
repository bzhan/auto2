(*
  File: SeqRing.thy
  Author: Bohua Zhan

  Set of sequences as a ring.
*)

theory SeqRing
  imports Sequence
begin

section \<open>Construction of the ring of sequences\<close>

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

lemma seq_ring_is_comm_ring [forward]:
  "is_comm_ring(R) \<Longrightarrow> is_comm_ring(seq_ring(R))"
@proof
  @let "S = seq_ring(R)"
  @have "\<zero>\<^sub>S \<noteq> \<one>\<^sub>S" @with @have "(\<zero>\<^sub>S)`0 \<noteq> (\<one>\<^sub>S)`0" @end
  @have "is_add_id(S)"
  @have "is_mult_id(S)"
  @have "has_add_inverse(S)" @with
    @have "\<forall>X\<in>.S. X +\<^sub>S seq_neg(X) = \<zero>\<^sub>S"
  @end
  @have "\<forall>X\<in>.S. \<forall>Y\<in>.S. \<forall>Z\<in>.S. (X +\<^sub>S Y) +\<^sub>S Z = X +\<^sub>S (Y +\<^sub>S Z)" @with
    @have (@rule) "\<forall>n\<in>.\<nat>. (X`n +\<^sub>R Y`n) +\<^sub>R Z`n = X`n +\<^sub>R (Y`n +\<^sub>R Z`n)"
  @end
  @have "\<forall>X\<in>.S. \<forall>Y\<in>.S. \<forall>Z\<in>.S. (X *\<^sub>S Y) *\<^sub>S Z = X *\<^sub>S (Y *\<^sub>S Z)" @with
    @have (@rule) "\<forall>n\<in>.\<nat>. (X`n *\<^sub>R Y`n) *\<^sub>R Z`n = X`n *\<^sub>R (Y`n *\<^sub>R Z`n)"
  @end
  @have "\<forall>X\<in>.S. \<forall>Y\<in>.S. \<forall>Z\<in>.S. X *\<^sub>S (Y +\<^sub>S Z) = X *\<^sub>S Y +\<^sub>S X *\<^sub>S Z" @with
    @have (@rule) "\<forall>n\<in>.\<nat>. X`n *\<^sub>R (Y`n +\<^sub>R Z`n) = X`n *\<^sub>R Y`n +\<^sub>R X`n *\<^sub>R Z`n"
  @end
  @have "is_times_comm(S)"
@qed

lemma seq_ring_uminus [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> n \<in> source(-\<^sub>S X) \<Longrightarrow> (-\<^sub>S X)`n = -\<^sub>R (X`n)"
@proof @have "-\<^sub>S X = seq_neg(X)" @with @have "X +\<^sub>S seq_neg(X) = \<zero>\<^sub>S" @end @qed

lemma seq_ring_eval_minus [rewrite]:
  "is_comm_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> n \<in> source(X -\<^sub>S Y) \<Longrightarrow>
   (X -\<^sub>S Y)`n = X`n -\<^sub>R Y`n"
@proof @have "X -\<^sub>S Y = X +\<^sub>S (-\<^sub>S Y)" @have "X`n -\<^sub>R Y`n = X`n +\<^sub>R -\<^sub>R Y`n" @qed

(* Inverse of a sequence: invert all entries, except keeping 0 unchanged. *)

definition seq_inverse :: "i \<Rightarrow> i" where [rewrite]:
  "seq_inverse(X) = (let R = target_str(X) in Seq(R,\<lambda>n. if X`n \<in> units(R) then inv(R,X`n) else \<zero>\<^sub>R))"

lemma seq_inverse_type [typing]:
  "ord_field_seq(X) \<Longrightarrow> seq_inverse(X) \<in> seqs(target_str(X))" by auto2

lemma eval_seq_inverse [rewrite]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<in> source(seq_inverse(X)) \<Longrightarrow> X`n \<in> units(R) \<Longrightarrow>
   seq_inverse(X)`n = inv(R,X`n)" by auto2
setup {* del_prfstep_thm @{thm seq_inverse_def} *}

section \<open>Property on vanishes condition\<close>

lemma vanishes_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X +\<^sub>S Y)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain s t where "s >\<^sub>R \<zero>\<^sub>R \<and> t >\<^sub>R \<zero>\<^sub>R \<and> r = s +\<^sub>R t"
    @obtain "i\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n\<bar>\<^sub>R <\<^sub>R s"
    @obtain "j\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R t"
    @have "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm vanishes_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma vanishes_minus:
  "is_ord_ring(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> vanishes(X) \<Longrightarrow> vanishes(-\<^sub>S X)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm vanishes_minus} [with_term "-\<^sub>?S ?X"] *}

lemma vanishes_minus' [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> vanishes(-\<^sub>S X) \<Longrightarrow> vanishes(X)"
@proof @have "X = -\<^sub>S (-\<^sub>S X)" @qed

lemma vanishes_diff:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X -\<^sub>S Y)"
@proof @have "X -\<^sub>S Y = X +\<^sub>S (-\<^sub>S Y)" @qed
setup {* add_forward_prfstep_cond @{thm vanishes_diff} [with_term "?X -\<^sub>?S ?Y"] *}

lemma vanishes_diff' [rewrite]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(X) \<longleftrightarrow> vanishes(Y)"
@proof
  @case "vanishes(X)" @with @have "X -\<^sub>S (X -\<^sub>S Y) = Y" @end
  @case "vanishes(Y)" @with @have "Y +\<^sub>S (X -\<^sub>S Y) = X" @end
@qed

lemma vanishes_mult_bounded:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   bounded(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(X *\<^sub>S Y)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain a where "a >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R a"
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R r /\<^sub>R a"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm vanishes_mult_bounded} [with_term "?X *\<^sub>?S ?Y"] *}

lemma vanishes_mult_bounded2:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   bounded(X) \<Longrightarrow> vanishes(Y) \<Longrightarrow> vanishes(Y *\<^sub>S X)"
@proof @have "X *\<^sub>S Y = Y *\<^sub>S X" @qed
setup {* add_forward_prfstep_cond @{thm vanishes_mult_bounded2} [with_term "?Y *\<^sub>?S ?X"] *}

lemma vanishes_limit_equal [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> vanishes(X -\<^sub>S Y) \<Longrightarrow>
   converges_to(X,x) \<Longrightarrow> converges_to(Y,x)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>Y`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain s t where "s >\<^sub>R \<zero>\<^sub>R" "t >\<^sub>R \<zero>\<^sub>R" "r = s +\<^sub>R t"
    @obtain "i\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R t"
    @obtain j where "j\<ge>\<^sub>\<nat>i" "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R s"
    @have "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R r"
  @end
@qed

section \<open>Property on Cauchy condition\<close>
  
lemma cauchy_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X +\<^sub>S Y)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X +\<^sub>S Y)`m -\<^sub>R (X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain s t where "s >\<^sub>R \<zero>\<^sub>R" "t >\<^sub>R \<zero>\<^sub>R" "r = s +\<^sub>R t"
    @obtain "i\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s"
    @obtain "j\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t"
    @have "\<forall>m \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X +\<^sub>S Y)`m -\<^sub>R (X +\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "\<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s"
      @have "\<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t"
      @have "(X`m +\<^sub>R Y`m) -\<^sub>R (X`n +\<^sub>R Y`n) = (X`m -\<^sub>R X`n) +\<^sub>R (Y`m -\<^sub>R Y`n)"
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm cauchy_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma cauchy_minus:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> cauchy(-\<^sub>S X)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`m -\<^sub>R (-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain "k\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r"
    @have "\<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(-\<^sub>S X)`m -\<^sub>R (-\<^sub>S X)`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "-\<^sub>R (X`m) -\<^sub>R (-\<^sub>R X`n) = X`n -\<^sub>R X`m" @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm cauchy_minus} [with_term "-\<^sub>?S ?X"] *}

lemma cauchy_minus' [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(-\<^sub>S X) \<Longrightarrow> cauchy(X)"
@proof @have "X = -\<^sub>S (-\<^sub>S X)" @qed
    
lemma cauchy_diff:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X -\<^sub>S Y)"
@proof @have "X -\<^sub>S Y = X +\<^sub>S -\<^sub>S Y" @qed
setup {* add_forward_prfstep_cond @{thm cauchy_diff} [with_term "?X -\<^sub>?S ?Y"] *}

lemma cauchy_mult:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> cauchy(X *\<^sub>S Y)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S Y)`m -\<^sub>R (X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain a where "a >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R a"
    @obtain b where "b >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<in>.\<nat>. \<bar>Y`n\<bar>\<^sub>R <\<^sub>R b"
    @obtain s t where "s >\<^sub>R \<zero>\<^sub>R" "t >\<^sub>R \<zero>\<^sub>R" "r = s +\<^sub>R t"
    @obtain "i\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s /\<^sub>R b"
    @obtain "j\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t /\<^sub>R a"
    @have "\<forall>m \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>(X *\<^sub>S Y)`m -\<^sub>R (X *\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "\<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s /\<^sub>R b"
      @have "\<bar>Y`m -\<^sub>R Y`n\<bar>\<^sub>R <\<^sub>R t /\<^sub>R a"
      @have "(X`m *\<^sub>R Y`m) -\<^sub>R (X`n *\<^sub>R Y`n) = (X`m -\<^sub>R X`n) *\<^sub>R Y`n +\<^sub>R X`m *\<^sub>R (Y`m -\<^sub>R Y`n)"
      @have "\<bar>X`m *\<^sub>R (Y`m -\<^sub>R Y`n)\<bar>\<^sub>R <\<^sub>R t" @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm cauchy_mult} [with_term "?X *\<^sub>?S ?Y"] *}

lemma cauchy_inverse:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   cauchy(seq_inverse(X))"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>seq_inverse(X)`m -\<^sub>R seq_inverse(X)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain b "i\<in>.\<nat>" where "b >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R"
    @obtain j where "j \<ge>\<^sub>\<nat> i" "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r *\<^sub>R (b *\<^sub>R b)"
    @have "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>seq_inverse(X)`m -\<^sub>R seq_inverse(X)`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "\<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r *\<^sub>R (b *\<^sub>R b)"
      @have "b *\<^sub>R b <\<^sub>R \<bar>X`m *\<^sub>R X`n\<bar>\<^sub>R"
      @have "inv(R,X`m) -\<^sub>R inv(R,X`n) = (X`n -\<^sub>R X`m) /\<^sub>R (X`m *\<^sub>R X`n)" @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm cauchy_inverse} [with_term "seq_inverse(?X)"] *}

lemma vanishes_diff_inverse [backward1]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   cauchy(X) \<Longrightarrow> cauchy(Y) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow> \<not>vanishes(Y) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(seq_inverse(X) -\<^sub>S seq_inverse(Y))"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(seq_inverse(X) -\<^sub>S seq_inverse(Y))`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain a "i\<in>.\<nat>" where "a >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. a <\<^sub>R \<bar>X`n\<bar>\<^sub>R"
    @obtain b "j\<in>.\<nat>" where "b >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>j. b <\<^sub>R \<bar>Y`n\<bar>\<^sub>R"
    @obtain k where "k \<ge>\<^sub>\<nat> max(\<nat>,i,j)" "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R r *\<^sub>R (a *\<^sub>R b)"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(seq_inverse(X) -\<^sub>S seq_inverse(Y))`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "a *\<^sub>R b <\<^sub>R \<bar>X`n *\<^sub>R Y`n\<bar>\<^sub>R"
      @have "inv(R,X`n) -\<^sub>R inv(R,Y`n) = (Y`n -\<^sub>R X`n) /\<^sub>R (X`n *\<^sub>R Y`n)" @end
  @end
@qed

lemma seq_inverse_is_inverse [backward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   vanishes(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain b "k\<in>.\<nat>" where "b >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>(X *\<^sub>S seq_inverse(X) -\<^sub>S \<one>\<^sub>S)`n\<bar>\<^sub>R <\<^sub>R r"
  @end
@qed

section \<open>Positive sequences\<close>
  
definition pos_seq :: "i \<Rightarrow> o" where [rewrite]:
  "pos_seq(X) \<longleftrightarrow> (let R = target_str(X) in \<exists>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r)"

lemma pos_seqI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> pos_seq(X)" by auto2

lemma pos_seqD [resolve]:
  "pos_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n >\<^sub>R r" by auto2
setup {* del_prfstep_thm @{thm pos_seq_def} *}
  
lemma pos_seq_compat_vanishes [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> pos_seq(X) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> pos_seq(Y)"
@proof
  @obtain r "i\<in>.\<nat>" where "r >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r"
  @obtain s t where "s >\<^sub>R \<zero>\<^sub>R" "t >\<^sub>R \<zero>\<^sub>R" "r = s +\<^sub>R t"
  @obtain j where "j \<ge>\<^sub>\<nat> i" "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>(X -\<^sub>S Y)`n\<bar>\<^sub>R <\<^sub>R s"
  @have "\<forall>n\<ge>\<^sub>\<nat>j. Y`n >\<^sub>R t" @with
    @have "X`n -\<^sub>R Y`n <\<^sub>R s" @have "X`n = (X`n -\<^sub>R Y`n) +\<^sub>R Y`n" @end
@qed      

lemma pos_seq_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   pos_seq(X) \<Longrightarrow> pos_seq(Y) \<Longrightarrow> pos_seq(X +\<^sub>S Y)"
@proof
  @obtain s "i\<in>.\<nat>" where "s >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. s <\<^sub>R X`n"
  @obtain t "j\<in>.\<nat>" where "t >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>j. t <\<^sub>R Y`n"
  @have "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). s +\<^sub>R t <\<^sub>R (X +\<^sub>S Y)`n"
  @have "s +\<^sub>R t >\<^sub>R \<zero>\<^sub>R"
@qed
setup {* add_forward_prfstep_cond @{thm pos_seq_add} [with_term "?X +\<^sub>?S ?Y"] *}

lemma pos_seq_mult:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   pos_seq(X) \<Longrightarrow> pos_seq(Y) \<Longrightarrow> pos_seq(X *\<^sub>S Y)"
@proof
  @obtain s "i\<in>.\<nat>" where "s >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. s <\<^sub>R X`n"
  @obtain t "j\<in>.\<nat>" where "t >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>j. t <\<^sub>R Y`n"
  @have "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). s *\<^sub>R t <\<^sub>R (X *\<^sub>S Y)`n"
  @have "s *\<^sub>R t >\<^sub>R \<zero>\<^sub>R"
@qed
setup {* add_forward_prfstep_cond @{thm pos_seq_mult} [with_term "?X *\<^sub>?S ?Y"] *}

lemma non_vanishes_pos_seq_cases [backward1]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   \<not>pos_seq(X) \<Longrightarrow> pos_seq(-\<^sub>S X)"
@proof
  @obtain b "k\<in>.\<nat>" where "b >\<^sub>R \<zero>\<^sub>R" "(\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n) \<or> (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R X`n)"
  @case "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n" @with @have "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R (-\<^sub>S X)`n" @end
@qed
      
lemma pos_seq_minus [resolve]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> pos_seq(X) \<Longrightarrow> \<not>pos_seq(-\<^sub>S X)"
@proof
  @contradiction
  @obtain r "i\<in>.\<nat>" where "r >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r"
  @obtain s "j\<in>.\<nat>" where "s >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>j. (-\<^sub>S X)`n >\<^sub>R s"
  @let "k = max(\<nat>,i,j)"
  @have "(-\<^sub>S X)`k >\<^sub>R s" @have "X`k >\<^sub>R r"
@qed

definition nonneg_seq :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_seq(X) \<longleftrightarrow> pos_seq(X) \<or> vanishes(X)"
  
lemma nonneg_seq_compat_vanishes [forward]:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> nonneg_seq(X) \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> nonneg_seq(Y)" by auto2

lemma nonneg_seq_add:
  "is_ord_field(R) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow>
   nonneg_seq(X) \<Longrightarrow> nonneg_seq(Y) \<Longrightarrow> nonneg_seq(X +\<^sub>S Y)"
@proof
  @case "vanishes(X) \<and> pos_seq(Y)" @with @have "-\<^sub>S X = Y -\<^sub>S (X +\<^sub>S Y)" @end
  @case "pos_seq(X) \<and> vanishes(Y)" @with @have "-\<^sub>S Y = X -\<^sub>S (X +\<^sub>S Y)" @end
@qed
setup {* add_forward_prfstep_cond @{thm nonneg_seq_add} [with_term "?X +\<^sub>?S ?Y"] *}

section \<open>Characterization of non-positive sequences\<close>
  
lemma pos_seq_not_vanish [resolve]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> pos_seq(X) \<Longrightarrow> \<not>vanishes(X)"
@proof
  @contradiction
  @obtain r "i\<in>.\<nat>" where "r >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r"
  @obtain "j\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r"
  @have "\<bar>X`max(\<nat>,i,j)\<bar>\<^sub>R <\<^sub>R r" @have "X`max(\<nat>,i,j) >\<^sub>R r"
@qed

lemma not_positive_to_nonneg_uminus [rewrite_back]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> cauchy(X) \<Longrightarrow>
   \<not>pos_seq(X) \<longleftrightarrow> nonneg_seq(-\<^sub>S X)"
@proof @case "vanishes(X)" @have "pos_seq(X) \<or> pos_seq(-\<^sub>S X)" @qed

lemma not_positiveD [backward2]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<not>pos_seq(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow> \<exists>k\<ge>\<^sub>\<nat>i. r \<ge>\<^sub>R X`k"
@proof @contradiction @have "\<forall>n\<ge>\<^sub>\<nat>i. X`n >\<^sub>R r" @qed

lemma not_positive' [rewrite_back]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>pos_seq(X) \<longleftrightarrow> (\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)"
@proof
  @case "\<not>pos_seq(X)" @with
    @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)" @with
      @obtain s where "s >\<^sub>R \<zero>\<^sub>R" "r = s +\<^sub>R s"
      @obtain "i\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s"
      @obtain k where "k \<ge>\<^sub>\<nat> i" "s \<ge>\<^sub>R X`k"
      @have "\<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r" @with @have "\<bar>X`k -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s" @end
    @end
  @end
  @case "\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r" @with
    @obtain r "i\<in>.\<nat>" where "r >\<^sub>R \<zero>\<^sub>R" "\<forall>n\<ge>\<^sub>\<nat>i. r <\<^sub>R X`n"
    @obtain "j\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>j. X`n \<le>\<^sub>R r"
    @obtain "k\<in>.\<nat>" where "k \<ge>\<^sub>\<nat> i" "k \<ge>\<^sub>\<nat> j"
    @have "X`k \<le>\<^sub>R r"
  @end
@qed

lemma not_positive [rewrite]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> S = seq_ring(R) \<Longrightarrow> cauchy(X) \<Longrightarrow>
   nonneg_seq(-\<^sub>S X) \<longleftrightarrow> (\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>R r)" by auto2
setup {* fold del_prfstep_thm [@{thm not_positive_to_nonneg_uminus}, @{thm not_positive'}] *}

section \<open>Constant sequences\<close>
  
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
@proof @have (@rule) "\<forall>n\<in>nat. {a}\<^sub>R`n \<in> units(R)" @qed

lemma vanishes_zero [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> vanishes({c}\<^sub>R) \<longleftrightarrow> c = \<zero>\<^sub>R"
@proof
  @case "vanishes({c}\<^sub>R)" @with
    @contradiction
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R \<bar>c\<bar>\<^sub>R"
    @have "\<bar>{c}\<^sub>R`k\<bar>\<^sub>R <\<^sub>R \<bar>c\<bar>\<^sub>R" @end
  @case "c = \<zero>\<^sub>R" @with
    @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r)" @with
      @have "\<forall>n\<ge>\<^sub>\<nat>0. \<bar>{c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r" @end @end
@qed      

lemma cauchy_const [backward]:
  "is_ord_field(R) \<Longrightarrow> c \<in>. R \<Longrightarrow> cauchy({c}\<^sub>R)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>{c}\<^sub>R`m -\<^sub>R {c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @have "\<forall>m\<ge>\<^sub>\<nat>0. \<forall>n\<ge>\<^sub>\<nat>0. \<bar>{c}\<^sub>R`m -\<^sub>R {c}\<^sub>R`n\<bar>\<^sub>R <\<^sub>R r" @end
@qed

end
