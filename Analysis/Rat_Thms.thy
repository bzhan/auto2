(* Setup of proof steps related to arithmetic on rational numbers. *)

theory Rat_Thms
imports "../Auto2"
begin

subsection {* Basic properties of absolute values *}

setup {* add_rewrite_rule @{thm abs_zero} *}
setup {* add_resolve_prfstep @{thm abs_ge_zero} *}
setup {* add_rewrite_rule @{thm abs_minus_cancel} *}
setup {* add_rewrite_rule @{thm abs_of_pos} *}
setup {* add_rewrite_rule @{thm abs_of_neg} *}
setup {* add_rewrite_rule @{thm zero_less_abs_iff} *}
setup {* add_rewrite_rule_cond @{thm abs_mult}
  [with_filt (canonical_split_filter @{const_name times} "a" "b")] *}
setup {* add_rewrite_rule_cond @{thm abs_inverse}
  [with_filt (ac_atomic_filter @{const_name times} "a")] *}
setup {* add_rewrite_rule @{thm abs_numeral} *}
lemma abs_ge_cases [forward]: fixes x :: "'a::linordered_idom"
  shows "\<bar>x\<bar> \<ge> r \<Longrightarrow> x > -r \<Longrightarrow> x \<ge> r" "\<bar>x\<bar> \<ge> r \<Longrightarrow> x < r \<Longrightarrow> x \<le> -r" by arith+
lemma abs_gt_cases [forward]: fixes x :: "'a::linordered_idom"
  shows "\<bar>x\<bar> > r \<Longrightarrow> x \<ge> -r \<Longrightarrow> x > r" "\<bar>x\<bar> > r \<Longrightarrow> x \<le> r \<Longrightarrow> x < -r" by arith+
setup {* add_forward_prfstep (equiv_forward_th @{thm abs_le_iff}) *}
setup {* add_forward_prfstep (equiv_forward_th @{thm abs_less_iff}) *}
theorem abs_diff_nonneg [rewrite]: "(a::('a::linordered_idom)) \<ge> b \<Longrightarrow> \<bar>a - b\<bar> = a - b" by simp

(* Shifting negation to the other side of inequality. *)
theorem le_diff_conv_left: "(a::('a::linordered_idom)) + -c \<le> b \<longleftrightarrow> a \<le> b + c" by auto
theorem le_diff_conv_right: "(a::('a::linordered_idom)) \<le> b + -c \<longleftrightarrow> a + c \<le> b" by auto
theorem less_diff_conv_left: "(a::('a::linordered_idom)) + -c < b \<longleftrightarrow> a < b + c" by auto
theorem less_diff_conv_right: "(a::('a::linordered_idom)) < b + -c \<longleftrightarrow> a + c < b" by auto

ML_file "rat_arith.ML"
ML_file "rat_arith_test.ML"

subsection {* Equalities on rationals *}

theorem divide_cancel_gt0 [rewrite]:
  "(a::('a::linordered_field)) > 0 \<Longrightarrow> bu * a * inverse a = bu" by simp

lemma diff_inverse: "(a::('a::field)) \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> inverse a - inverse b = (b-a)/(a*b)"
  by (simp add: diff_divide_distrib inverse_eq_divide)
lemma diff_inverse_bound [backward2]:
  "(a::('a::linordered_field)) \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> \<bar>inverse a - inverse b\<bar> = \<bar>a-b\<bar>/\<bar>a*b\<bar>"
  by (simp add: abs_minus_commute diff_inverse)

subsection {* Inequalities on rationals *}

setup {* add_forward_prfstep_cond @{thm positive_imp_inverse_positive} [with_term "inverse ?a"] *}
setup {* add_backward_prfstep @{thm positive_imp_inverse_positive} *}
setup {* add_backward2_prfstep @{thm add_strict_mono} *}
setup {* add_backward2_prfstep @{thm add_pos_pos} *}
setup {* add_backward2_prfstep @{thm mult_pos_pos} *}
theorem mult_strict_mono' [forward]:
  "(b::('a::linordered_field)) * d \<le> a * c \<Longrightarrow> a < b \<Longrightarrow> 0 < b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c \<ge> d"
  by (meson leD leI mult_strict_mono)
setup {* add_backward2_prfstep @{thm less_imp_inverse_less} *}
setup {* add_resolve_prfstep @{thm le_of_int_ceiling} *}
theorem two_power_gt_zero: "2 ^ k > (0::('a::linordered_field))" by simp
setup {* add_forward_prfstep_cond @{thm two_power_gt_zero} [with_term "(2::(?'a::linordered_field)) ^ ?k"] *}
setup {* add_forward_prfstep (equiv_forward_th @{thm pos_le_divide_eq}) *}
setup {* add_forward_prfstep (equiv_forward_th @{thm pos_divide_less_eq}) *}
theorem mult_left_less_imp_less' [forward]:
  "(a::('a::linordered_field)) * b < a * c \<Longrightarrow> a > 0 \<Longrightarrow> b < c" by simp

subsection {* of_nat, of_int, of_rat *}

setup {* add_rewrite_rule @{thm of_nat_0} *}
theorem of_nat_ge_0 [rewrite]: "x \<noteq> 0 \<Longrightarrow> of_nat x = of_nat (x - 1) + 1"
  by (metis One_nat_def Suc_pred add.commute not_gr0 of_nat_Suc)
setup {* add_backward_prfstep @{thm less_imp_of_nat_less} *}
setup {* add_forward_prfstep @{thm of_nat_less_imp_less} *}
setup {* add_rewrite_rule @{thm of_nat_power} *}

setup {* add_rewrite_rule @{thm Fract_of_int_quotient} *}
setup {* add_rewrite_rule @{thm of_int_of_nat_eq} *}
setup {* add_rewrite_rule @{thm of_int_diff} *}
lemma ge_0_int_to_rat: "b > 0 \<Longrightarrow> rat_of_int b > 0" by simp
setup {* add_forward_prfstep_cond @{thm ge_0_int_to_rat} [with_term "rat_of_int ?b"] *}
lemma le_0_nat_to_rat [forward]: "rat_of_nat n \<le> 0 \<Longrightarrow> n = 0" by simp
setup {* add_rewrite_rule @{thm Rat.zero_less_of_rat_iff} *}

setup {* add_rewrite_rule @{thm of_rat_divide} *}
setup {* add_rewrite_rule @{thm of_rat_of_int_eq} *}
setup {* add_rewrite_rule @{thm of_rat_inverse} *}
setup {* add_rewrite_rule @{thm of_rat_of_nat_eq} *}

subsection {* Induction and case check on int, rat *}

theorem int_diff_cases' [resolve]: "\<exists>m n. z = int m - int n" using int_diff_cases by blast

theorem rat_cases [resolve]: "\<exists>a b. b > 0 \<and> r = Fract a b" by (induct r) auto

subsection {* Archimedean fields *}

setup {* add_resolve_prfstep @{thm ex_le_of_nat} *}
setup {* add_resolve_prfstep @{thm ex_less_of_nat} *}
setup {* add_backward_prfstep @{thm ex_inverse_of_nat_less} *}
setup {* add_backward_prfstep @{thm ex_less_of_nat_mult} *}

subsection {* Misc *}

theorem Max_ge_nat_finite: "i < (k::nat) \<Longrightarrow> f i \<le> Max (f ` {..<k})" by simp
setup {* add_backward_prfstep_cond @{thm Max_ge_nat_finite} [with_term "Max (?f ` {..<?k})"] *}

theorem lift_Suc_mono_le' [backward2]: fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<forall>n. f n \<le> f (n + 1)) \<Longrightarrow> n \<le> n' \<Longrightarrow> f n \<le> f n'" using lift_Suc_mono_le by auto

theorem lift_Suc_mono_ge' [backward2]: fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<forall>n. f n \<ge> f (n + 1)) \<Longrightarrow> n \<le> n' \<Longrightarrow> f n \<ge> f n'"
  using order.lift_Suc_mono_le[OF dual_order, of "f"] by auto

end
