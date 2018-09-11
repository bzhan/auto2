(*
  File: CompleteOrder.thy
  Author: Bohua Zhan

  Results about Cauchy completeness and completeness of ordered fields.
*)

theory CompleteOrder
  imports SeqRing
begin

section {* Cauchy completeness *}
  
definition cauchy_complete_field :: "i \<Rightarrow> o" where [rewrite]:
  "cauchy_complete_field(R) \<longleftrightarrow> (is_ord_field(R) \<and> (\<forall>X\<in>seqs(R). cauchy(X) \<longrightarrow> converges(X)))"

lemma cauchy_completeD [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_ord_field(R)"
  "is_sequence(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> cauchy_complete_field(target_str(X)) \<Longrightarrow> converges(X)" by auto2+

lemma cauchy_completeI [forward]:
  "is_ord_field(R) \<Longrightarrow> \<forall>X\<in>seqs(R). cauchy(X) \<longrightarrow> converges(X) \<Longrightarrow> cauchy_complete_field(R)" by auto2
setup {* del_prfstep_thm @{thm cauchy_complete_field_def} *}

section {* Monotone convergence theorem *}

lemma seq_has_increment_induct [backward1]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> N \<in> nat \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a \<Longrightarrow> \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R of_nat(R,N) *\<^sub>R a"
@proof
  @var_induct "N \<in> nat" arbitrary k @with
    @subgoal "N = N' +\<^sub>\<nat> 1"
      @obtain k1 where "k1\<ge>\<^sub>\<nat>k" "X`k1 -\<^sub>R X`k \<ge>\<^sub>R of_nat(R,N') *\<^sub>R a"
      @obtain k2 where "k2\<ge>\<^sub>\<nat>k1" "X`k2 -\<^sub>R X`k1 \<ge>\<^sub>R a"
      @have "X`k2 -\<^sub>R X`k = (X`k2 -\<^sub>R X`k1) +\<^sub>R (X`k1 -\<^sub>R X`k)"
      @have "(of_nat(R,N') +\<^sub>R 1\<^sub>R) *\<^sub>R a = a +\<^sub>R of_nat(R,N') *\<^sub>R a"
    @endgoal
  @end
@qed

lemma monotone_cauchy [forward]:
  "ord_field_seq(X) \<Longrightarrow> seq_incr(X) \<Longrightarrow> upper_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   is_archimedean(R) \<Longrightarrow> cauchy(X)"
@proof
  @contradiction
  @obtain a where "a >\<^sub>R \<zero>\<^sub>R" "\<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R \<ge>\<^sub>R a"
  @have "\<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a"
  @obtain "M\<in>.R" where "\<forall>n\<in>.\<nat>. X`n \<le>\<^sub>R M"
  @obtain "N\<in>nat" where "of_nat(R,N) *\<^sub>R a >\<^sub>R (M -\<^sub>R X`0)"
  @obtain n where "n \<ge>\<^sub>\<nat> 0" "X`n -\<^sub>R X`0 \<ge>\<^sub>R of_nat(R,N) *\<^sub>R a" @have "X`n \<le>\<^sub>R M"
@qed

lemma monotone_incr_converges [forward]:
  "is_sequence(X) \<Longrightarrow> seq_incr(X) \<Longrightarrow> upper_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> converges(X)" by auto2

lemma monotone_decr_converges [forward]:
  "is_sequence(X) \<Longrightarrow> seq_decr(X) \<Longrightarrow> lower_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> converges(X)"
@proof @have "upper_bounded(seq_neg(X))" @have "seq_incr(seq_neg(X))" @qed

section {* A simple test for vanishing of sequences *}

definition half_seq :: "i \<Rightarrow> o" where [rewrite]:
  "half_seq(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R)"

lemma half_seqD:
  "half_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm half_seqD} [with_term "\<bar>?X`(?n +\<^sub>\<nat> 1)\<bar>\<^sub>target_str(?X)"] *}

lemma half_seqI [backward]:
  "R = target_str(X) \<Longrightarrow> \<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R \<Longrightarrow> half_seq(X)" by auto2
setup {* del_prfstep_thm @{thm half_seq_def} *}

lemma ord_field_divide_le_trans1 [backward1]:
  "is_ord_field(R) \<Longrightarrow> d \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> e >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c \<Longrightarrow>
   b \<le>\<^sub>R d /\<^sub>R e \<Longrightarrow> a \<le>\<^sub>R d /\<^sub>R (e *\<^sub>R c)"
@proof @have "a *\<^sub>R c \<le>\<^sub>R b" @have "a \<le>\<^sub>R d /\<^sub>R e /\<^sub>R c" @qed

lemma half_seq_induct [resolve]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> n \<in> nat \<Longrightarrow>
   \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R (2\<^sub>R ^\<^sub>R n)"
@proof @var_induct "n \<in> nat" @qed
setup {* del_prfstep_thm @{thm ord_field_divide_le_trans1} *}

lemma half_seq_abs_decr [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> seq_abs_decr(X)"
@proof @have "\<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R" @qed

lemma ord_field_divide_le_trans2 [forward]:
  "is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> a >\<^sub>R b /\<^sub>R c \<Longrightarrow> d \<le>\<^sub>R b /\<^sub>R a \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c >\<^sub>R d"
@proof
  @have "a *\<^sub>R c >\<^sub>R b" @have "d *\<^sub>R a \<le>\<^sub>R b" @have "a *\<^sub>R c >\<^sub>R a *\<^sub>R d"
@qed

lemma half_seq_vanishes [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> vanishes(X)"
@proof
  @have "\<forall>r. r >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r)" @with
    @obtain "k\<in>nat" where "2\<^sub>R ^\<^sub>R k >\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R r"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" @with
      @have "\<bar>X`k\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R (2\<^sub>R ^\<^sub>R k)"
      @have "\<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`k\<bar>\<^sub>R" @end @end
@qed
setup {* del_prfstep_thm @{thm ord_field_divide_le_trans2} *}
  
section {* Dedekind cut *}

(* A dedekind cut is a set that is closed downward and has no greatest element *)
definition dedekind_cut :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "dedekind_cut(R,U) \<longleftrightarrow> (U \<noteq> \<emptyset> \<and> U \<subset> carrier(R) \<and> (\<forall>a\<in>U. \<forall>b \<le>\<^sub>R a. b \<in> U) \<and> (\<forall>a\<in>U. \<exists>b >\<^sub>R a. b\<in>U))"

lemma dedekind_cutI1 [forward]:
  "dedekind_cut(R,U) \<Longrightarrow> a \<in> U \<Longrightarrow> \<forall>b \<le>\<^sub>R a. b \<in> U" by auto2

lemma dedekind_cutI2 [backward2]:
  "dedekind_cut(R,U) \<Longrightarrow> a \<in> U \<Longrightarrow> \<exists>b >\<^sub>R a. b \<in> U" by auto2
    
lemma dedekind_cutI_ex [resolve]:
  "dedekind_cut(R,U) \<Longrightarrow> \<exists>x\<in>.R. x \<in> U" by auto2

lemma dedekind_cutI_ex2 [resolve]:
  "dedekind_cut(R,U) \<Longrightarrow> \<exists>x\<in>.R. x \<notin> U" by auto2
setup {* del_prfstep_thm_eqforward @{thm dedekind_cut_def} *}

(* For any dedekind cut, we define two sequences converging to the boundary point. *)
definition DCSeqs :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "DCSeqs(R,U) = Seq_rec2(R,
    SOME a\<in>.R. a \<in> U, \<lambda>x p q. if avg(R,p,q) \<notin> U then p else avg(R,p,q),
    SOME b\<in>.R. b \<notin> U, \<lambda>x p q. if avg(R,p,q) \<notin> U then avg(R,p,q) else q)"

lemma DCSeqs_type [forward]:
  "is_ord_field(R) \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> A = fst(DCSeqs(R,U)) \<Longrightarrow> B = snd(DCSeqs(R,U)) \<Longrightarrow>
   A \<in> seqs(R) \<and> B \<in> seqs(R) \<and> A`0 \<in> U \<and> B`0 \<notin> U" by auto2

lemma DCSeqs_eval1 [rewrite]:
  "is_ord_field(R) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> A = fst(DCSeqs(R,U)) \<Longrightarrow> B = snd(DCSeqs(R,U)) \<Longrightarrow>
   A`(n +\<^sub>\<nat> 1) = (if avg(R,A`n,B`n) \<notin> U then A`n else avg(R,A`n,B`n))" by auto2

lemma DCSeqs_eval2 [rewrite]:
  "is_ord_field(R) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> A = fst(DCSeqs(R,U)) \<Longrightarrow> B = snd(DCSeqs(R,U)) \<Longrightarrow>
   B`(n +\<^sub>\<nat> 1) = (if avg(R,A`n,B`n) \<notin> U then avg(R,A`n,B`n) else B`n)" by auto2
setup {* del_prfstep_thm @{thm DCSeqs_def} *}

lemma DCSeqs_le [backward]:
  "is_ord_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> A = fst(DCSeqs(R,U)) \<Longrightarrow> B = snd(DCSeqs(R,U)) \<Longrightarrow>
   n \<in> source(A) \<Longrightarrow> n \<in> source(B) \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> A`n \<le>\<^sub>R B`n"
@proof @var_induct "n \<in> nat" @qed

lemma dedekind_complete [resolve]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> \<exists>x\<in>.R. \<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U"
@proof
  @let "A = fst(DCSeqs(R,U))" "B = snd(DCSeqs(R,U))"
  @have "converges(A)" @with
    @have "seq_incr(A)" @with @have "\<forall>n\<in>.\<nat>. A`(n +\<^sub>\<nat> 1) \<ge>\<^sub>R A`n" @end
    @have "upper_bounded(A)" @with
      @have "\<forall>n\<in>.\<nat>. A`n \<le>\<^sub>R B`0" @with @var_induct "n \<in>. \<nat>" @end @end @end
  @have "converges(B)" @with
    @have "seq_decr(B)" @with @have "\<forall>n\<in>.\<nat>. B`(n +\<^sub>\<nat> 1) \<le>\<^sub>R B`n" @end
    @have "lower_bounded(B)" @with
      @have "\<forall>n\<in>.\<nat>. B`n \<ge>\<^sub>R A`0" @with @var_induct "n \<in>. \<nat>" @end @end @end
  @obtain x where "converges_to(B,x)"
  @let "S = seq_ring(R)"
  @have "vanishes(B -\<^sub>S A)" @with @have "half_seq(B -\<^sub>S A)" @end
  @have (@rule) "\<forall>n\<in>nat. A`n \<in> U" @with @var_induct "n \<in> nat" @end
  @have (@rule) "\<forall>n\<in>nat. B`n \<notin> U" @with @var_induct "n \<in> nat" @end
  @have "\<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U" @with
    @case "y <\<^sub>R x" @with @obtain "n\<in>nat" where "y <\<^sub>R A`n" @end
    @case "y \<in> U" @with
      @have "x \<in> U" @obtain x' where "x' >\<^sub>R x" "x' \<in> U"
      @obtain "n\<in>nat" where "x' >\<^sub>R B`n" @have "B`n \<notin> U"
    @end
  @end
@qed

section {* Least upper bound property *}

lemma least_upper_bound_complete [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> S \<noteq> \<emptyset> \<Longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<Longrightarrow> has_sup(R,S)"
@proof
  @let "U = carrier(R) \<midarrow> upper_bound(R,S)"
  @have "dedekind_cut(R,U)" @with
    @have "U \<noteq> \<emptyset>" @with
      @obtain "x \<in> S" @obtain y where "y <\<^sub>R x" @have "y \<in> U" @end
    @have "U \<noteq> carrier(R)" @with
      @obtain "z \<in> upper_bound(R,S)" @have "z \<notin> U" @end
    @have "\<forall>a\<in>U. \<exists>b >\<^sub>R a. b \<in> U" @with
      @obtain "c \<in> S" where "a <\<^sub>R c" @obtain b where "a <\<^sub>R b \<and> b <\<^sub>R c" @have "b \<in> U" @end @end
  @obtain "y\<in>.R" where "\<forall>z\<in>.R. z <\<^sub>R y \<longleftrightarrow> z \<in> U"
  @have "y \<notin> U" @have "y \<in> upper_bound(R,S)"
  @have "has_sup(R,S) \<and> sup(R,S) = y"
@qed

lemma complete_to_linear_continuum [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> linear_continuum(R)"
@proof @have "\<forall>S. S \<noteq> \<emptyset> \<longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<longrightarrow> has_sup(R,S)" @qed

end
