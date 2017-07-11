theory CompleteOrder
imports SeqRing
begin

section {* Cauchy completeness *}
  
definition cauchy_complete_field :: "i \<Rightarrow> o" where [rewrite]:
  "cauchy_complete_field(R) \<longleftrightarrow> (is_ord_field(R) \<and> (\<forall>X\<in>seqs(R). cauchy(X) \<longrightarrow> converges(X)))"
setup {* add_property_const @{term cauchy_complete_field} *}

lemma cauchy_completeD [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_ord_field(R)"
  "is_sequence(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> cauchy_complete_field(target_str(X)) \<Longrightarrow> converges(X)" by auto2+

lemma cauchy_completeI [forward]:
  "is_ord_field(R) \<Longrightarrow> \<forall>X\<in>seqs(R). cauchy(X) \<longrightarrow> converges(X) \<Longrightarrow> cauchy_complete_field(R)" by auto2
setup {* del_prfstep_thm @{thm cauchy_complete_field_def} *}

section {* Monotone convergence theorem *}

definition seq_has_increment :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "seq_has_increment(X,a) \<longleftrightarrow> (let R = target_str(X) in \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a)"

lemma seq_has_incrementD [backward1]:
  "seq_has_increment(X,a) \<Longrightarrow> R = target_str(X) \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a" by auto2

lemma seq_has_incrementI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a \<Longrightarrow> seq_has_increment(X,a)" by auto2
    
lemma seq_has_increment_zero [resolve]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> seq_has_increment(X,0\<^sub>R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R 0\<^sub>R" WITH HAVE "X`k -\<^sub>R X`k \<ge>\<^sub>R 0\<^sub>R") *})
setup {* del_prfstep_thm @{thm seq_has_increment_def} *}
  
lemma seq_has_increment_induct [backward1]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> N \<in> nat \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   seq_has_increment(X,a) \<Longrightarrow> seq_has_increment(X,of_nat(R,N) *\<^sub>R a)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "seq_has_increment(X,0\<^sub>R)" THEN
    HAVE "\<forall>n\<in>nat. seq_has_increment(X,of_nat(R,n) *\<^sub>R a) \<longrightarrow> seq_has_increment(X,of_nat(R,n +\<^sub>\<nat> 1) *\<^sub>R a)" WITH (
      HAVE "\<forall>k\<in>.\<nat>. \<exists>k'\<ge>\<^sub>\<nat>k. X`k' -\<^sub>R X`k \<ge>\<^sub>R of_nat(R,n +\<^sub>\<nat> 1) *\<^sub>R a" WITH (
        CHOOSE "k1\<ge>\<^sub>\<nat>k, X`k1 -\<^sub>R X`k \<ge>\<^sub>R of_nat(R,n) *\<^sub>R a" THEN
        CHOOSE "k2\<ge>\<^sub>\<nat>k1, X`k2 -\<^sub>R X`k1 \<ge>\<^sub>R a" THEN
        HAVE "X`k2 -\<^sub>R X`k = (X`k2 -\<^sub>R X`k1) +\<^sub>R (X`k1 -\<^sub>R X`k)" THEN
        HAVE "(of_nat(R,n) +\<^sub>R 1\<^sub>R) *\<^sub>R a = a +\<^sub>R of_nat(R,n) *\<^sub>R a")) THEN
    INDUCT_ON "N \<in> nat" "seq_has_increment(X,of_nat(R,N) *\<^sub>R a)") *})
   
lemma monotone_cauchy [forward]:
  "ord_field_seq(X) \<Longrightarrow> seq_incr(X) \<Longrightarrow> upper_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   is_archimedean(R) \<Longrightarrow> cauchy(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "a >\<^sub>R \<zero>\<^sub>R, \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R \<ge>\<^sub>R a" THEN
    HAVE "\<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. X`n -\<^sub>R X`k \<ge>\<^sub>R a" THEN
    CHOOSE "M\<in>.R, \<forall>n\<in>.\<nat>. X`n \<le>\<^sub>R M" THEN
    CHOOSE "N\<in>nat, of_nat(R,N) *\<^sub>R a >\<^sub>R (M -\<^sub>R X`0)" THEN
    CHOOSE "n \<ge>\<^sub>\<nat> 0, X`n -\<^sub>R X`0 \<ge>\<^sub>R of_nat(R,N) *\<^sub>R a" THEN HAVE "X`n \<le>\<^sub>R M") *})
      
lemma monotone_incr_converges [forward]:
  "is_sequence(X) \<Longrightarrow> seq_incr(X) \<Longrightarrow> upper_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> converges(X)" by auto2

lemma monotone_decr_converges [forward]:
  "is_sequence(X) \<Longrightarrow> seq_decr(X) \<Longrightarrow> lower_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> converges(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "upper_bounded(seq_neg(X))" THEN HAVE "seq_incr(seq_neg(X))") *})

section {* A simple test for vanishing of sequences *}

definition half_seq :: "i \<Rightarrow> o" where [rewrite]:
  "half_seq(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R)"
setup {* add_property_const @{term half_seq} *}

lemma half_seqD:
  "half_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R" by auto2
setup {* add_forward_prfstep_cond @{thm half_seqD} [with_term "\<bar>?X`(?n +\<^sub>\<nat> 1)\<bar>\<^sub>target_str(?X)"] *}

lemma half_seqI [backward]:
  "R = target_str(X) \<Longrightarrow> \<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R /\<^sub>R 2\<^sub>R \<Longrightarrow> half_seq(X)" by auto2
setup {* del_prfstep_thm @{thm half_seq_def} *}

lemma ord_field_divide_le_trans1 [backward1]:
  "is_ord_field(R) \<Longrightarrow> d \<in>. R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> e >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> a \<le>\<^sub>R b /\<^sub>R c \<Longrightarrow>
   b \<le>\<^sub>R d /\<^sub>R e \<Longrightarrow> a \<le>\<^sub>R d /\<^sub>R (e *\<^sub>R c)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a *\<^sub>R c \<le>\<^sub>R b" THEN HAVE "a \<le>\<^sub>R d /\<^sub>R e /\<^sub>R c") *})

lemma half_seq_induct [resolve]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> n \<in> nat \<Longrightarrow>
   \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R (2\<^sub>R ^\<^sub>R n)"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "n \<in> nat" "\<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R (2\<^sub>R ^\<^sub>R n)") *})
setup {* del_prfstep_thm @{thm ord_field_divide_le_trans1} *}

lemma half_seq_abs_decr [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> seq_abs_decr(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R") *})

lemma ord_field_divide_le_trans2 [forward]:
  "is_ord_field(R) \<Longrightarrow> b \<in>. R \<Longrightarrow> a >\<^sub>R b /\<^sub>R c \<Longrightarrow> d \<le>\<^sub>R b /\<^sub>R a \<Longrightarrow> a >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> c >\<^sub>R d"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a *\<^sub>R c >\<^sub>R b" THEN HAVE "d *\<^sub>R a \<le>\<^sub>R b" THEN HAVE "a *\<^sub>R c >\<^sub>R a *\<^sub>R d") *})

lemma half_seq_vanishes [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> half_seq(X) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> vanishes(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "k\<in>nat, 2\<^sub>R ^\<^sub>R k >\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R r" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" WITH (
      HAVE "\<bar>X`k\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`0\<bar>\<^sub>R /\<^sub>R (2\<^sub>R ^\<^sub>R k)" THEN
      HAVE "\<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`k\<bar>\<^sub>R")) *})
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
setup {* del_prfstep_thm_str "@eqforward" @{thm dedekind_cut_def} *}

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
  by (tactic {* auto2s_tac @{context} (INDUCT_ON "n \<in> nat" "A`n \<le>\<^sub>R B`n") *})

definition dedekind_has_boundary :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "dedekind_has_boundary(R,U) \<longleftrightarrow> (\<exists>x\<in>.R. \<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U)"
  
lemma dedekind_has_boundaryE [resolve]:
  "dedekind_has_boundary(R,U) \<Longrightarrow> \<exists>x\<in>.R. \<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U" by auto2

lemma dedekind_has_boundaryI [forward]:
  "x \<in>. R \<Longrightarrow> \<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U \<Longrightarrow> dedekind_has_boundary(R,U)" by auto2
setup {* del_prfstep_thm @{thm dedekind_has_boundary_def} *}

lemma dedekind_complete [resolve]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> dedekind_cut(R,U) \<Longrightarrow> dedekind_has_boundary(R,U)"
  by (tactic {* auto2s_tac @{context} (
    LET "A = fst(DCSeqs(R,U)), B = snd(DCSeqs(R,U))" THEN
    HAVE "converges(A)" WITH (
      HAVE "seq_incr(A)" WITH HAVE "\<forall>n\<in>.\<nat>. A`(n +\<^sub>\<nat> 1) \<ge>\<^sub>R A`n" THEN
      HAVE "upper_bounded(A)" WITH
        HAVE "\<forall>n\<in>.\<nat>. A`n \<le>\<^sub>R B`0" WITH INDUCT_ON "n \<in> nat" "A`n \<le>\<^sub>R B`0") THEN
    HAVE "converges(B)" WITH (
      HAVE "seq_decr(B)" WITH HAVE "\<forall>n\<in>.\<nat>. B`(n +\<^sub>\<nat> 1) \<le>\<^sub>R B`n" THEN
      HAVE "lower_bounded(B)" WITH
        HAVE "\<forall>n\<in>.\<nat>. B`n \<ge>\<^sub>R A`0" WITH INDUCT_ON "n \<in> nat" "B`n \<ge>\<^sub>R A`0") THEN
    CHOOSE "x, converges_to(B,x)" THEN
    LET "S = seq_ring(R)" THEN
    HAVE "vanishes(B -\<^sub>S A)" WITH HAVE "half_seq(B -\<^sub>S A)" THEN
    HAVE_RULE "\<forall>n\<in>nat. A`n \<in> U" WITH INDUCT_ON "n \<in> nat" "A`n \<in> U" THEN
    HAVE_RULE "\<forall>n\<in>nat. B`n \<notin> U" WITH INDUCT_ON "n \<in> nat" "B`n \<notin> U" THEN
    HAVE "\<forall>y\<in>.R. y <\<^sub>R x \<longleftrightarrow> y \<in> U" WITH (
      CASE "y <\<^sub>R x" WITH CHOOSE "n\<in>nat, y <\<^sub>R A`n" THEN
      HAVE "x \<in> U" THEN CHOOSE "x' >\<^sub>R x, x' \<in> U" THEN
      CHOOSE "n\<in>nat, x' >\<^sub>R B`n" THEN HAVE "B`n \<notin> U")) *})

section {* Least upper bound property *}

lemma least_upper_bound_complete [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> S \<noteq> \<emptyset> \<Longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<Longrightarrow> has_sup(R,S)"
  by (tactic {* auto2s_tac @{context} (
    LET "U = carrier(R) \<midarrow> upper_bound(R,S)" THEN
    HAVE "dedekind_cut(R,U)" WITH (
      HAVE "U \<noteq> \<emptyset>" WITH (
        CHOOSE "x, x \<in> S" THEN CHOOSE "y, y <\<^sub>R x" THEN HAVE "y \<in> U") THEN
      HAVE "U \<noteq> carrier(R)" WITH (
        CHOOSE "z, z \<in> upper_bound(R,S)" THEN HAVE "z \<notin> U") THEN
      HAVE "\<forall>a\<in>U. \<exists>b >\<^sub>R a. b \<in> U" WITH (
        CHOOSE "c \<in> S, a <\<^sub>R c" THEN CHOOSE "b, a <\<^sub>R b \<and> b <\<^sub>R c" THEN HAVE "b \<in> U")) THEN
    HAVE "dedekind_has_boundary(R,U)" THEN
    CHOOSE "y\<in>.R, \<forall>z\<in>.R. z <\<^sub>R y \<longleftrightarrow> z \<in> U" THEN
    HAVE "y \<notin> U" THEN HAVE "y \<in> upper_bound(R,S)" THEN
    HAVE "has_sup(R,S) \<and> sup(R,S) = y") *})

lemma complete_to_linear_continuum [forward]:
  "cauchy_complete_field(R) \<Longrightarrow> is_archimedean(R) \<Longrightarrow> linear_continuum(R)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>S. S \<noteq> \<emptyset> \<longrightarrow> upper_bound(R,S) \<noteq> \<emptyset> \<longrightarrow> has_sup(R,S)") *})

end
