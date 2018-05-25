theory Real
imports CompleteOrder Rat OrderTopology
begin

section {* Real numbers as a quotient set *}

abbreviation seq_ring_rat :: i where
  "seq_ring_rat \<equiv> seq_ring(\<rat>)"
notation seq_ring_rat ("S")

definition cauchy_seqs :: i where [rewrite]:
  "cauchy_seqs = {X \<in>. S. cauchy(X)}"

lemma cauchy_seqsI [forward]: "cauchy(X) \<Longrightarrow> X \<in> seqs(\<rat>) \<Longrightarrow> X \<in> cauchy_seqs" by auto2
lemma cauchy_seqs_iff [rewrite]: "X \<in> cauchy_seqs \<longleftrightarrow> (cauchy(X) \<and> X \<in> seqs(\<rat>))" by auto2
setup {* del_prfstep_thm @{thm cauchy_seqs_def} *}

definition real_rel :: i where [rewrite]:
  "real_rel = Equiv(cauchy_seqs, \<lambda>X Y. vanishes(X -\<^sub>S Y))"
notation real_rel ("\<R>")

lemma real_rel_sym [resolve]:
  "X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(Y -\<^sub>S X)"
@proof @have "Y -\<^sub>S X = -\<^sub>S (X -\<^sub>S Y)" @qed

lemma real_rel_trans [backward2]:
  "X \<in>. S \<Longrightarrow> Y \<in>. S \<Longrightarrow> Z \<in>. S \<Longrightarrow>
   vanishes(X -\<^sub>S Y) \<Longrightarrow> vanishes(Y -\<^sub>S Z) \<Longrightarrow> vanishes(X -\<^sub>S Z)"
@proof @have "X -\<^sub>S Z = (X -\<^sub>S Y) +\<^sub>S (Y -\<^sub>S Z)" @qed

lemma real_rel_is_rel [typing]: "\<R> \<in> equiv_space(cauchy_seqs)" by auto2
setup {* fold del_prfstep_thm [@{thm real_rel_sym}, @{thm real_rel_trans}] *}

lemma real_rel_eval:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> X \<sim>\<^sub>\<R> Y \<longleftrightarrow> vanishes(X -\<^sub>S Y)" by auto2
setup {* add_rewrite_rule_cond @{thm real_rel_eval} [with_cond "?X \<noteq> ?Y"] *}
setup {* del_prfstep_thm @{thm real_rel_def} *}
  
definition real :: i where real_def [rewrite_bidir]:
  "real = cauchy_seqs // \<R>"
  
abbreviation Real :: "i \<Rightarrow> i" where "Real(X) \<equiv> equiv_class(\<R>,X)"

section {* Real numbers as a ring *}

definition nonneg_real :: "i \<Rightarrow> o" where [rewrite]:
  "nonneg_real(x) \<longleftrightarrow> nonneg_seq(rep(\<R>,x))"

definition nonneg_reals :: i where [rewrite]:
  "nonneg_reals = {x\<in>real. nonneg_real(x)}"

lemma nonneg_reals_in_real: "nonneg_reals \<subseteq> real" by auto2
setup {* add_forward_prfstep_cond @{thm nonneg_reals_in_real} [with_term "nonneg_reals"] *}

definition real_ring :: i where [rewrite]:
  "real_ring = Ring(real, Real(\<zero>\<^sub>S), \<lambda>x y. Real(rep(\<R>,x) +\<^sub>S rep(\<R>,y)),
                          Real(\<one>\<^sub>S), \<lambda>x y. Real(rep(\<R>,x) *\<^sub>S rep(\<R>,y)))"

lemma real_ring_is_ring_raw [forward]: "ring_form(real_ring)" by auto2
    
definition real_ord_ring :: i where [rewrite]:
  "real_ord_ring = ord_ring_from_nonneg(real_ring, nonneg_reals)"
  
definition real_ord_ring_top :: i  ("\<real>") where [rewrite]:
  "\<real> = ord_ring_top_from_ord_ring(real_ord_ring)"

lemma real_is_ring_raw [forward]: "is_ring_raw(\<real>)" by auto2
lemma real_carrier [rewrite_bidir]: "carrier(\<real>) = real" by auto2
lemma real_evals [rewrite]:
  "\<zero>\<^sub>\<real> = Real(\<zero>\<^sub>S)"
  "\<one>\<^sub>\<real> = Real(\<one>\<^sub>S)"
  "x \<in>. \<real> \<Longrightarrow> y \<in>. \<real> \<Longrightarrow> x +\<^sub>\<real> y = Real(rep(\<R>,x) +\<^sub>S rep(\<R>,y))"
  "x \<in>. \<real> \<Longrightarrow> y \<in>. \<real> \<Longrightarrow> x *\<^sub>\<real> y = Real(rep(\<R>,x) *\<^sub>S rep(\<R>,y))"
  "x \<in>. \<real> \<Longrightarrow> y \<in>. \<real> \<Longrightarrow> is_abgroup(\<real>) \<Longrightarrow> x \<le>\<^sub>\<real> y \<longleftrightarrow> y -\<^sub>\<real> x \<in> nonneg_reals" by auto2+

setup {* register_wellform_data ("nonneg_compat(R,A)", ["A \<subseteq> carrier(R)"]) *}

lemma nonneg_compat_prop [forward]:
  "is_ring_raw(R) \<Longrightarrow> is_ring(T) \<Longrightarrow> A \<subseteq> carrier(R) \<Longrightarrow> eq_str_ring(R,T) \<Longrightarrow>
   nonneg_compat(R,A) \<Longrightarrow> nonneg_compat(T,A)" by auto2

lemma real_is_ord_field_prep [forward]:
  "is_field(\<real>) \<Longrightarrow> nonneg_compat(\<real>,nonneg_reals) \<Longrightarrow> is_ord_field(\<real>)" by auto2

lemma ord_ring_card_ge2 [forward]:
  "is_ord_ring(R) \<Longrightarrow> card_ge2(carrier(R))"
@proof @have "{\<zero>\<^sub>R,\<one>\<^sub>R} \<subseteq> carrier(R)" @qed

lemma real_is_order_top_prep [backward]:
  "is_ord_ring(\<real>) \<Longrightarrow> order_topology(\<real>)" by auto2
setup {* fold del_prfstep_thm [@{thm real_ring_def}, @{thm real_ord_ring_def}, @{thm real_ord_ring_top_def}] *}

lemma seq_const_in_cauchy_seqs [typing]: "r \<in>. \<rat> \<Longrightarrow> {r}\<^sub>\<rat> \<in>. \<R>" by auto2
    
lemma real_choose_rep: "x \<in>. \<real> \<Longrightarrow> x = Real(rep(\<R>,x))" by auto2
setup {* add_rewrite_rule_cond @{thm real_choose_rep} [with_filt (size1_filter "x")] *}

section {* Addition on real numbers *}
  
lemma real_add_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Real(x) +\<^sub>\<real> Real(y) = Real(x +\<^sub>S y)"
@proof @have "compat_meta_bin(\<R>, \<lambda>X Y. X +\<^sub>S Y)" @qed
setup {* del_prfstep_thm @{thm real_evals(3)} *}

lemma real_add_comm [forward]: "is_plus_comm(\<real>)" by auto2
lemma real_add_assoc [forward]: "is_plus_assoc(\<real>)" by auto2

section {* Multiplication on real numbers *}

lemma real_mult_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Real(x) *\<^sub>\<real> Real(y) = Real(x *\<^sub>S y)"
@proof
  @have "\<forall>X Y Z. X \<in>. \<R> \<longrightarrow> Y \<sim>\<^sub>\<R> Z \<longrightarrow> X *\<^sub>S Y \<sim>\<^sub>\<R> X *\<^sub>S Z" @with
    @have "X *\<^sub>S Y -\<^sub>S X *\<^sub>S Z = X *\<^sub>S (Y -\<^sub>S Z)"
  @end
  @have "\<forall>X Y Z. X \<in>. \<R> \<longrightarrow> Y \<sim>\<^sub>\<R> Z \<longrightarrow> Y *\<^sub>S X \<sim>\<^sub>\<R> Z *\<^sub>S X" @with
    @have "Y *\<^sub>S X -\<^sub>S Z *\<^sub>S X = (Y -\<^sub>S Z) *\<^sub>S X"
  @end
  @have "compat_meta_bin(\<R>, \<lambda>X Y. X *\<^sub>S Y)"
@qed
setup {* del_prfstep_thm @{thm real_evals(4)} *}
  
lemma real_mult_comm [forward]: "is_times_comm(\<real>)" by auto2
lemma real_mult_assoc [forward]: "is_times_assoc(\<real>)" by auto2
lemma real_distrib_l [forward]: "is_left_distrib(\<real>)" by auto2

section {* 0 and 1 *}
  
lemma real_is_add_id [forward]: "is_add_id(\<real>)" by auto2
lemma real_is_mult_id [forward]: "is_mult_id(\<real>)" by auto2
lemma real_zero_neq_one [resolve]: "\<zero>\<^sub>\<real> \<noteq> \<one>\<^sub>\<real>" by auto2

section {* Negation on real numbers *}

lemma real_is_comm_ring [forward]: "is_comm_ring(\<real>)"
@proof @have "\<forall>x\<in>.\<real>. x +\<^sub>\<real> Real(-\<^sub>S rep(\<R>,x)) = \<zero>\<^sub>\<real>" @qed

section {* Inverse in real numbers *}

lemma real_is_field [forward]: "is_field(\<real>)"
@proof @have "\<forall>x\<in>.\<real>. x \<noteq> \<zero>\<^sub>\<real> \<longrightarrow> x *\<^sub>\<real> Real(seq_inverse(rep(\<R>,x))) = \<one>\<^sub>\<real>" @qed

section {* Nonnegative real numbers *}

lemma real_neg_eval [rewrite]: "x \<in>. \<R> \<Longrightarrow> -\<^sub>\<real> Real(x) = Real(-\<^sub>S x)"
@proof @have "Real(x) +\<^sub>\<real> Real(-\<^sub>S x) = \<zero>\<^sub>\<real>" @qed

lemma nonneg_real_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> nonneg_real(Real(x)) \<longleftrightarrow> nonneg_seq(x)" by auto2
setup {* del_prfstep_thm @{thm nonneg_real_def} *}

lemma real_is_ord_field [forward]: "is_ord_field(\<real>)"
@proof
  @have "nonneg_compat(\<real>, nonneg_reals)" @with
    @have "subset_add_closed(\<real>, nonneg_reals)"
    @have "subset_mult_closed(\<real>, nonneg_reals)"
  @end
@qed
setup {* del_prfstep_thm @{thm real_is_ord_field_prep} *}

section {* of_nat, of_int, of_rat in terms of sequences *}

lemma real_of_nat [rewrite]:
  "n \<in> nat \<Longrightarrow> of_nat(\<real>,n) = Real({of_nat(\<rat>,n)}\<^sub>\<rat>)"
@proof @var_induct "n \<in> nat" @qed

lemma real_diff_eval [rewrite]:
  "x \<in>. \<R> \<Longrightarrow> y \<in>. \<R> \<Longrightarrow> Real(x) -\<^sub>\<real> Real(y) = Real(x -\<^sub>S y)"
@proof @have "Real(x) -\<^sub>\<real> Real(y) = Real(x) +\<^sub>\<real> (-\<^sub>\<real> Real(y))" @qed

lemma real_diff_eval_seq [rewrite]:
  "r \<in>. \<rat> \<Longrightarrow> s \<in>. \<rat> \<Longrightarrow> Real({r}\<^sub>\<rat>) -\<^sub>\<real> Real({s}\<^sub>\<rat>) = Real({r -\<^sub>\<rat> s}\<^sub>\<rat>)" by auto2

lemma real_inv_eval [rewrite]:
  "r \<in> units(\<rat>) \<Longrightarrow> inv(\<real>,Real({r}\<^sub>\<rat>)) = Real({inv(\<rat>,r)}\<^sub>\<rat>)"
@proof @have "Real({r}\<^sub>\<rat>) *\<^sub>\<real> Real({inv(\<rat>,r)}\<^sub>\<rat>) = \<one>\<^sub>\<real>" @qed

lemma real_mult_eval_seq [rewrite]:
  "r \<in>. \<rat> \<Longrightarrow> s \<in>. \<rat> \<Longrightarrow> Real({r}\<^sub>\<rat>) *\<^sub>\<real> Real({s}\<^sub>\<rat>) = Real({r *\<^sub>\<rat> s}\<^sub>\<rat>)" by auto2

lemma real_divide_eval [rewrite]:
  "r \<in>. \<rat> \<Longrightarrow> s \<in> units(\<rat>) \<Longrightarrow> Real({r}\<^sub>\<rat>) /\<^sub>\<real> Real({s}\<^sub>\<rat>) = Real({r /\<^sub>\<rat> s}\<^sub>\<rat>)"
@proof 
  @have "Real({r}\<^sub>\<rat>) /\<^sub>\<real> Real({s}\<^sub>\<rat>) = Real({r}\<^sub>\<rat>) *\<^sub>\<real> inv(\<real>,Real({s}\<^sub>\<rat>))"
  @have "r /\<^sub>\<rat> s = r *\<^sub>\<rat> inv(\<rat>,s)"
@qed
  
lemma real_of_int [rewrite]:
  "z \<in>. \<int> \<Longrightarrow> of_int(\<real>,z) = Real({of_int(\<rat>,z)}\<^sub>\<rat>)"
@proof @obtain "a\<in>.\<nat>" "b\<in>.\<nat>" where "z = of_nat(\<int>,a) -\<^sub>\<int> of_nat(\<int>,b)" @qed

lemma of_rat_divide [rewrite_bidir]:
  "is_ord_field(R) \<Longrightarrow> x \<in>. \<rat> \<Longrightarrow> y \<in> units(\<rat>) \<Longrightarrow> of_rat(R,x /\<^sub>\<rat> y) = of_rat(R,x) /\<^sub>R of_rat(R,y)"
@proof 
  @have "of_rat(R,x) /\<^sub>R of_rat(R,y) = of_rat(R,x) *\<^sub>R inv(R,of_rat(R,y))"
@qed

lemma real_of_rat [backward]:
  "r \<in>. \<rat> \<Longrightarrow> of_rat(\<real>,r) = Real({r}\<^sub>\<rat>)"
@proof 
  @obtain "a\<in>.\<int>" b where "b>\<^sub>\<int>0\<^sub>\<int>" "r = of_int(\<rat>,a) /\<^sub>\<rat> of_int(\<rat>,b)"
@qed

setup {* fold del_prfstep_thm [@{thm real_of_nat}, @{thm real_of_int}] *}
setup {* del_prfstep_thm @{thm real_choose_rep} *}

section {* Ordering on real numbers *}

lemma le_Real1 [rewrite]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> Real(X) \<le>\<^sub>\<real> Real(Y) \<longleftrightarrow> nonneg_seq(Y -\<^sub>S X)" by auto2
setup {* fold del_prfstep_thm [@{thm real_evals(5)}, @{thm nonneg_real_eval}, @{thm nonneg_reals_def}] *}

lemma le_Real [rewrite]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> Real(X) \<le>\<^sub>\<real> Real(Y) \<longleftrightarrow> (\<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> r)"
@proof @have "Y -\<^sub>S X = -\<^sub>S (X -\<^sub>S Y)" @qed
setup {* del_prfstep_thm @{thm le_Real1} *}
  
lemma le_RealI [resolve]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> \<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> r \<Longrightarrow> Real(X) \<le>\<^sub>\<real> Real(Y)" by auto2

lemma le_RealD [backward2]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> Real(X) \<le>\<^sub>\<real> Real(Y) \<Longrightarrow> r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> r" by auto2  
setup {* del_prfstep_thm @{thm le_Real} *}

lemma le_Real_all_n [resolve]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> \<forall>n\<in>.\<nat>. X`n \<le>\<^sub>\<rat> Y`n \<Longrightarrow> Real(X) \<le>\<^sub>\<real> Real(Y)"
@proof 
  @have "\<forall>r. r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> r)" @with
    @have "\<forall>n\<ge>\<^sub>\<nat>0. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> r" @end
@qed

lemma archimedeal_Real [forward]: "is_archimedean(\<real>)"
@proof 
  @have "\<forall>x>\<^sub>\<real>0\<^sub>\<real>. \<exists>r\<in>.\<rat>. of_rat(\<real>,r) \<ge>\<^sub>\<real> x" @with
    @let "X = rep(\<R>,x)"
    @obtain b where "b >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> b"
    @have "of_rat(\<real>,b) = Real({b}\<^sub>\<rat>)"
    @have "\<forall>n\<in>.\<nat>. X`n \<le>\<^sub>\<rat> {b}\<^sub>\<rat>`n"
  @end
@qed
      
lemma le_rat_real [backward1]:
  "X \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> Real(X) \<le>\<^sub>\<real> of_rat(\<real>,c) \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
@proof 
  @have "of_rat(\<real>,c) = Real({c}\<^sub>\<rat>)"
  @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S {c}\<^sub>\<rat>)`n \<le>\<^sub>\<rat> r"
  @have "\<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @with @have "X`n -\<^sub>\<rat> c \<le>\<^sub>\<rat> r" @end
@qed

lemma diff_le_rat_real2 [backward1]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> Real(X) -\<^sub>\<real> Real(Y) \<le>\<^sub>\<real> of_rat(\<real>,c) \<Longrightarrow>
   \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. X`m -\<^sub>\<rat> Y`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
@proof 
  @obtain s t where "s >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "t >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "r = s +\<^sub>\<rat> t"
  @obtain "i\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>i. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> s"
  @obtain j where "j\<ge>\<^sub>\<nat>i" "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>\<rat> X`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> t"
  @have "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. X`m -\<^sub>\<rat> Y`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @with
    @have "X`m -\<^sub>\<rat> Y`n = (X`m -\<^sub>\<rat> X`n) +\<^sub>\<rat> (X`n -\<^sub>\<rat> Y`n)"
    @have "t +\<^sub>\<rat> (c +\<^sub>\<rat> s) = c +\<^sub>\<rat> (s +\<^sub>\<rat> t)" @end
@qed
 
lemma abs_diff_le_rat_real2D [backward1]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> \<bar>Real(X) -\<^sub>\<real> Real(Y)\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,c) \<Longrightarrow>
   \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
@proof
  @obtain "i\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. X`m -\<^sub>\<rat> Y`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @with
    @have "Real(X) -\<^sub>\<real> Real(Y) \<le>\<^sub>\<real> of_rat(\<real>,c)" @end
  @obtain "j\<in>.\<nat>" where "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. Y`m -\<^sub>\<rat> X`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @with
    @have "Real(Y) -\<^sub>\<real> Real(X) \<le>\<^sub>\<real> of_rat(\<real>,c)" @end
  @let "k = max(\<nat>,i,j)"
  @have "\<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
@qed
setup {* del_prfstep_thm @{thm diff_le_rat_real2} *}

lemma le_rat_realI [resolve]:
  "X \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> \<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r \<Longrightarrow> Real(X) \<le>\<^sub>\<real> of_rat(\<real>,c)"
@proof
  @have "of_rat(\<real>,c) = Real({c}\<^sub>\<rat>)"
  @have "\<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S {c}\<^sub>\<rat>)`n \<le>\<^sub>\<rat> r" @with
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. X`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S {c}\<^sub>\<rat>)`n \<le>\<^sub>\<rat> r" @with @have "X`n -\<^sub>\<rat> c \<le>\<^sub>\<rat> r" @end
  @end
@qed

lemma diff_le_rat_realI [resolve]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> \<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r \<Longrightarrow>
   Real(X) -\<^sub>\<real> Real(Y) \<le>\<^sub>\<real> of_rat(\<real>,c)" by auto2
setup {* del_prfstep_thm @{thm le_rat_realI} *}
  
lemma abs_diff_le_rat_realI [resolve]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> \<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r \<Longrightarrow>
   \<bar>Real(X) -\<^sub>\<real> Real(Y)\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,c)"
@proof 
  @have "Real(X) -\<^sub>\<real> Real(Y) \<le>\<^sub>\<real> of_rat(\<real>,c)" @with
    @have "\<forall>r. r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r)" @with
      @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
      @have "\<forall>n\<ge>\<^sub>\<nat>k. (X -\<^sub>S Y)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @end @end
  @have "Real(Y) -\<^sub>\<real> Real(X) \<le>\<^sub>\<real> of_rat(\<real>,c)" @with
    @have "\<forall>r. r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. (Y -\<^sub>S X)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r)" @with
      @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r"
      @have "\<forall>n\<ge>\<^sub>\<nat>k. (Y -\<^sub>S X)`n \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @end @end
@qed
setup {* del_prfstep_thm @{thm diff_le_rat_realI} *}
  
lemma abs_diff_le_rat_realI' [backward1]:
  "X \<in>. \<R> \<Longrightarrow> Y \<in>. \<R> \<Longrightarrow> c \<in>. \<rat> \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow> \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> c \<Longrightarrow>
   \<bar>Real(X) -\<^sub>\<real> Real(Y)\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,c)"
@proof 
  @have "\<forall>r. r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r)" @with
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> c"
    @have "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<rat> Y`n\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> c +\<^sub>\<rat> r" @end
@qed
  
lemma converges_to_in_rat [resolve]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> s \<in>. R \<Longrightarrow> is_archimedean(R) \<Longrightarrow>
   \<forall>r>\<^sub>\<rat>\<zero>\<^sub>\<rat>. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R \<le>\<^sub>R of_rat(R,r) \<Longrightarrow> converges_to(X,s)"
@proof 
  @have "\<forall>r'. r' >\<^sub>R \<zero>\<^sub>R \<longrightarrow> (\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r')" @with
    @obtain r where "r >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "of_rat(R,r) <\<^sub>R r'"
    @obtain "k\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R \<le>\<^sub>R of_rat(R,r)" @end
@qed

section {* A sequence that converges to zero *}

definition err :: i where [rewrite]:
  "err = Seq(\<rat>, \<lambda>n. inv(\<rat>,of_nat(\<rat>,n +\<^sub>\<nat> 1)))"

lemma err_type [typing]: "err \<in> seqs(\<rat>)" by auto2

lemma err_gt_zero: "n \<in>. \<nat> \<Longrightarrow> err`n >\<^sub>\<rat> \<zero>\<^sub>\<rat>" by auto2
setup {* add_forward_prfstep_cond @{thm err_gt_zero} [with_term "err`?n"] *}

lemma err_decreasing [backward]: "m >\<^sub>\<nat> n \<Longrightarrow> err`m <\<^sub>\<rat> err`n"
@proof @have "of_nat(\<rat>,n +\<^sub>\<nat> 1) >\<^sub>\<rat> \<zero>\<^sub>\<rat>" @qed

lemma err_less_than_r [backward]: "r >\<^sub>\<rat> \<zero>\<^sub>\<rat>\<Longrightarrow> \<exists>n\<in>.\<nat>. err`n <\<^sub>\<rat> r"
@proof @obtain "n\<in>nat" where "inv(\<rat>,of_nat(\<rat>,n +\<^sub>\<nat> 1)) <\<^sub>\<rat> r" @qed
  
lemma err_converge_to_zero [backward]: "r >\<^sub>\<rat> \<zero>\<^sub>\<rat> \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. err`n <\<^sub>\<rat> r"
@proof 
  @obtain "k\<in>.\<nat>" where "err`k <\<^sub>\<rat> r"
  @have "\<forall>n\<ge>\<^sub>\<nat>k. err`n <\<^sub>\<rat> r"
@qed
setup {* del_prfstep_thm @{thm err_def} *}

section {* Cauchy completeness of real numbers *}

(* We start by defining, for each Cauchy sequence X of real numbers, a "diagonal"
   sequence for the double sequence of representatives of X. *)
definition Diag :: "i \<Rightarrow> i" where [rewrite]:
  "Diag(X) = Seq(\<rat>,\<lambda>n. rep(\<R>,X`n)`(SOME k\<in>.\<nat>. \<forall>i\<ge>\<^sub>\<nat>k. \<bar>rep(\<R>,X`n)`i -\<^sub>\<rat> rep(\<R>,X`n)`k\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n))"
setup {* register_wellform_data ("Diag(X)", ["X \<in> seqs(\<real>)"]) *}

lemma Diag_type [typing]:
  "X \<in> seqs(\<real>) \<Longrightarrow> Diag(X) \<in> seqs(\<rat>)" by auto2

lemma Diag_prop [backward]:
  "X \<in> seqs(\<real>) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>i\<ge>\<^sub>\<nat>k. \<bar>rep(\<R>,X`n)`i -\<^sub>\<rat> Diag(X)`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n" by auto2

lemma Diag_prop_ge_nat [backward]:
  "X \<in> seqs(\<real>) \<Longrightarrow> n \<in>. \<nat> \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow> \<exists>k\<ge>\<^sub>\<nat>i. \<forall>i\<ge>\<^sub>\<nat>k. \<bar>rep(\<R>,X`n)`i -\<^sub>\<rat> Diag(X)`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n"
@proof 
  @obtain "k\<in>.\<nat>" where "\<forall>i\<ge>\<^sub>\<nat>k. \<bar>rep(\<R>,X`n)`i -\<^sub>\<rat> Diag(X)`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n"
  @have "max(\<nat>,k,i) \<ge>\<^sub>\<nat> i"
@qed
setup {* del_prfstep_thm @{thm Diag_def} *}

lemma Diag_is_cauchy [forward]:
  "cauchy(X) \<Longrightarrow> X \<in> seqs(\<real>) \<Longrightarrow> cauchy(Diag(X))"
@proof @contradiction
  @let "W = Diag(X)"
  @obtain r where "r >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "\<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>W`m -\<^sub>\<rat> W`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> r)"
  @obtain r1 r2 r3 where "r1 >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "r2 >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "r3 >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "r = r1 +\<^sub>\<rat> (r2 +\<^sub>\<rat> r3) +\<^sub>\<rat> r1" @with
    @have "r = r /\<^sub>\<rat> 4\<^sub>\<rat> +\<^sub>\<rat> (r /\<^sub>\<rat> 4\<^sub>\<rat> +\<^sub>\<rat> r /\<^sub>\<rat> 4\<^sub>\<rat>) +\<^sub>\<rat> r /\<^sub>\<rat> 4\<^sub>\<rat>" @end
  @obtain "i\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>i. err`n <\<^sub>\<rat> r1"
  @obtain j where "j\<ge>\<^sub>\<nat>i" "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>\<real> X`n\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,r2)"
  @have "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>W`m -\<^sub>\<rat> W`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> r" @with
    @let "Sm = rep(\<R>,X`m)" "Sn = rep(\<R>,X`n)"
    @obtain "k1\<in>.\<nat>" where "\<forall>k'\<ge>\<^sub>\<nat>k1. \<bar>Sm`k' -\<^sub>\<rat> W`m\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`m"
    @obtain "k2\<in>.\<nat>" where "\<forall>k'\<ge>\<^sub>\<nat>k2. \<bar>Sn`k' -\<^sub>\<rat> W`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n"
    @obtain "k3\<in>.\<nat>" where "\<forall>k'\<ge>\<^sub>\<nat>k3. \<forall>k''\<ge>\<^sub>\<nat>k3. \<bar>Sm`k' -\<^sub>\<rat> Sn`k''\<bar>\<^sub>\<rat> \<le>\<^sub>\<rat> r2 +\<^sub>\<rat> r3"
    @obtain k where "k \<ge>\<^sub>\<nat> k1" "k \<ge>\<^sub>\<nat> k2" "k \<ge>\<^sub>\<nat> k3"
    @have "\<bar>W`m -\<^sub>\<rat> Sn`k\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`m +\<^sub>\<rat> (r2 +\<^sub>\<rat> r3)"
  @end
@qed

lemma Diag_converges [forward]:
  "cauchy(X) \<Longrightarrow> X \<in> seqs(\<real>) \<Longrightarrow> converges_to(X,Real(Diag(X)))"
@proof @contradiction
  @let "W = Diag(X)"
  @obtain r where "r >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "\<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>\<real> Real(W)\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,r))"
  @obtain s t where "s >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "t >\<^sub>\<rat> \<zero>\<^sub>\<rat>" "r = s +\<^sub>\<rat> t"
  @obtain "i\<in>.\<nat>" where "\<forall>n\<ge>\<^sub>\<nat>i. err`n <\<^sub>\<rat> s"
  @obtain j where "j\<ge>\<^sub>\<nat>i" "\<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>W`m -\<^sub>\<rat> W`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> t"
  @have "\<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n -\<^sub>\<real> Real(W)\<bar>\<^sub>\<real> \<le>\<^sub>\<real> of_rat(\<real>,r)" @with
    @let "Sn = rep(\<R>,X`n)"
    @obtain k where "k\<ge>\<^sub>\<nat>j" "\<forall>k'\<ge>\<^sub>\<nat>k. \<bar>Sn`k' -\<^sub>\<rat> W`n\<bar>\<^sub>\<rat> <\<^sub>\<rat> err`n"
    @have "\<forall>p\<ge>\<^sub>\<nat>k. \<bar>Sn`p -\<^sub>\<rat> W`p\<bar>\<^sub>\<rat> <\<^sub>\<rat> r"
  @end
@qed

lemma real_cauchy_complete [forward]: "cauchy_complete_field(\<real>)"
@proof @have "\<forall>X\<in>seqs(\<real>). cauchy(X) \<longrightarrow> converges(X)" @qed
setup {* fold del_prfstep_thm [@{thm Diag_is_cauchy}, @{thm Diag_converges}] *}
setup {* fold del_prfstep_thm [@{thm abs_diff_le_rat_real2D}, @{thm abs_diff_le_rat_realI},
  @{thm abs_diff_le_rat_realI'}, @{thm converges_to_in_rat}] *}

lemma real_continuum [forward]: "linear_continuum(\<real>)" by auto2

lemma real_order_topology [forward]: "order_topology(\<real>)" by auto2
setup {* del_prfstep_thm @{thm real_is_order_top_prep} *}

no_notation seq_ring_rat ("S")
no_notation real_rel ("\<R>") 
setup {* del_prfstep_thm @{thm real_def} *}
setup {* fold del_prfstep_thm @{thms real_evals(1-2)} *}
setup {* fold del_prfstep_thm [@{thm real_add_eval}, @{thm real_mult_eval}] *}

end
