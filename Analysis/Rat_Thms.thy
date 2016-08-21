(* Setup of proof steps related to arithmetic on rational numbers. *)

theory Rat_Thms
imports "../Auto2"
begin

subsection {* Basic properties of absolute values *}

setup {* add_rewrite_rule @{thm abs_zero} *}
setup {* add_resolve_prfstep @{thm abs_not_less_zero} *}
setup {* add_rewrite_rule @{thm abs_minus_cancel} *}
setup {* add_rewrite_rule @{thm abs_minus_commute} *}
setup {* add_rewrite_rule @{thm abs_of_pos} *}
setup {* add_rewrite_rule @{thm abs_of_neg} *}
theorem abs_positive: "(a::'a::linordered_idom) \<noteq> 0 \<Longrightarrow> is_positive \<bar>a\<bar>" by simp
setup {* add_forward_prfstep_cond @{thm abs_positive} [with_term "\<bar>?a\<bar>"] *}
theorem abs_positive_to_nonzero [forward]: "is_positive \<bar>a::'a::linordered_idom\<bar> \<Longrightarrow> a \<noteq> 0" by simp
setup {* add_rewrite_rule @{thm abs_mult} *}
setup {* add_rewrite_rule @{thm abs_inverse} *}
setup {* add_rewrite_rule @{thm abs_numeral} *}
lemma abs_ge_cases [forward]: fixes x :: "'a::linordered_idom"
  shows "\<bar>x\<bar> \<ge> r \<Longrightarrow> x > -r \<Longrightarrow> x \<ge> r" "\<bar>x\<bar> \<ge> r \<Longrightarrow> x < r \<Longrightarrow> x \<le> -r" by arith+
lemma abs_gt_cases [forward]: fixes x :: "'a::linordered_idom"
  shows "\<bar>x\<bar> > r \<Longrightarrow> x \<ge> -r \<Longrightarrow> x > r" "\<bar>x\<bar> > r \<Longrightarrow> x \<le> r \<Longrightarrow> x < -r" by arith+
theorem abs_le_on_diff: "\<bar>(a::('a::linordered_idom)) - b\<bar> \<le> r \<Longrightarrow> a \<le> b + r \<and> b \<le> a + r" by auto
setup {* add_forward_prfstep_cond @{thm abs_le_on_diff} [with_filt (order_filter "a" "b"), with_cond "?a \<noteq> ?b", with_cond "?r \<noteq> 0"] *}
theorem abs_less_on_diff: "\<bar>(a::('a::linordered_idom)) - b\<bar> < r \<Longrightarrow> a < b + r \<and> b < a + r" by auto
setup {* add_forward_prfstep_cond @{thm abs_less_on_diff} [with_filt (order_filter "a" "b"), with_cond "?a \<noteq> ?b", with_cond "?r \<noteq> 0"] *}
theorem abs_le_zero [forward]: "\<bar>(a::('a::linordered_idom)) - b\<bar> \<le> 0 \<Longrightarrow> a = b" by simp
theorem abs_diff_nonneg [rewrite]: "(a::('a::linordered_idom)) \<ge> b \<Longrightarrow> \<bar>a - b\<bar> = a - b" by simp

(* Special definition for nonzero. *)
definition nonzero :: "'a::zero \<Rightarrow> bool" where "nonzero a = (a \<noteq> 0)"
theorem ineq_to_nonzero: "(a::'a::comm_ring_1) \<noteq> b \<Longrightarrow> nonzero (a - b)" by (simp add: nonzero_def)
theorem nonzero_resolve: "nonzero 0 \<Longrightarrow> False" by (simp add: nonzero_def)
theorem nonzero_multiple: "(c::'a::field) \<noteq> 0 \<Longrightarrow> nonzero a \<Longrightarrow> nonzero (a * c)" by (simp add: nonzero_def)

(* Positivity property on linordered_field *)
setup {* add_forward_prfstep (equiv_backward_th @{thm is_positive_def}) *}
setup {* add_resolve_prfstep (equiv_forward_th @{thm is_positive_def}) *}
theorem positive_props:
  fixes x y :: "'a::linordered_idom"
  fixes r s :: "'b::linordered_field" shows
  "is_positive x \<Longrightarrow> is_positive y \<Longrightarrow> is_positive (x + y)"
  "is_positive x \<Longrightarrow> is_positive y \<Longrightarrow> is_positive (x * y)"
  "is_positive r \<Longrightarrow> is_positive (inverse r)"
  "is_positive r \<Longrightarrow> is_positive s \<Longrightarrow> is_positive (r / s)"
  "is_positive n \<Longrightarrow> is_positive ((of_nat n)::'a)"
  "is_positive a \<Longrightarrow> is_positive ((of_int a)::'a)"
  "is_positive b \<Longrightarrow> is_positive ((of_rat b)::'b)" by simp+
setup {* fold add_property_update @{thms positive_props} *}
declare is_positive_def [property_rewrites]

theorem is_positive_on_disj [forward]: "x > 0 \<Longrightarrow> (\<not>x > 0) \<or> P \<Longrightarrow> P" by simp
theorem nat_is_positive_plus1: "is_positive ((n::nat) + 1)" by simp
setup {* add_forward_prfstep_cond @{thm nat_is_positive_plus1} [with_term "?n + 1"] *}

theorem less_to_is_positive: "(a::'a::linordered_idom) < b \<longleftrightarrow> is_positive (b - a)" by simp
theorem le_to_is_nonneg: "(a::'a::linordered_idom) \<le> b \<longleftrightarrow> is_non_negative (b - a)" by auto

ML_file "rat_arith.ML"
ML_file "algebra.ML"

subsection {* Equalities on rationals *}

lemma diff_inverse: "(a::('a::field)) \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> 1 / a - 1 / b = (b-a)/(a*b)"
  by (simp add: diff_divide_distrib inverse_eq_divide)
lemma diff_inverse_bound [backward2]:
  "(a::('a::linordered_field)) \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> \<bar>1 / a - 1 / b\<bar> = \<bar>a-b\<bar>/\<bar>a*b\<bar>"
  by (simp add: abs_minus_commute diff_inverse)

theorem divide_by_numc [rewrite]: "(a::'a::linordered_field) / NUMC = a * inverse NUMC" by algebra
setup {* add_rewrite_rule @{thm diff_minus_eq_add} *}

lemma diff_eq_zero [forward]: "(a::('a::comm_ring)) - b = 0 \<Longrightarrow> a = b" by simp

setup {* add_rewrite_rule @{thm diff_self} *}
setup {* add_rewrite_rule @{thm left_minus} *}
setup {* add_rewrite_rule @{thm right_minus} *}

subsection {* Inequalities on rationals *}

theorem positive_diff: "(a::'a::linordered_idom) > b \<Longrightarrow> is_positive (a - b)" by simp
setup {* add_forward_prfstep_cond @{thm positive_diff} [with_term "?a - ?b"] *}
setup {* add_backward2_prfstep @{thm add_strict_mono} *}
theorem mult_strict_mono' [forward]:
  "b > 0 \<Longrightarrow> (b::('a::linordered_field)) * d \<le> a * c \<Longrightarrow> a < b \<Longrightarrow> 0 \<le> c \<Longrightarrow> c \<ge> d"
  by (meson leD leI mult_strict_mono)
theorem less_imp_inverse_less' [backward]:
  "(a::'a::linordered_field) > 0 \<Longrightarrow> a < b \<Longrightarrow> inverse b < inverse a" by simp
setup {* add_resolve_prfstep @{thm le_of_int_ceiling} *}
theorem two_power_gt_zero: "2 ^ k > (0::('a::linordered_field))" by simp
setup {* add_forward_prfstep_cond @{thm two_power_gt_zero} [with_term "(2::(?'a::linordered_field)) ^ ?k"] *}
theorem pos_le_divide_eq' [forward]:
  "c > 0 \<Longrightarrow> (a::('a::linordered_field)) \<le> b / c \<Longrightarrow> a * c \<le> b" using pos_le_divide_eq by blast
theorem pos_divide_less_eq' [forward]:
  "c > 0 \<Longrightarrow> (a::('a::linordered_field)) > b / c \<Longrightarrow> a * c > b" using pos_divide_less_eq by blast
theorem mult_cancel_side [forward]:
  fixes a b c :: "'a::linordered_field" shows
  "a > 0 \<Longrightarrow> a * b < a * c \<Longrightarrow> b < c"
  "a > 0 \<Longrightarrow> b * a < a * c \<Longrightarrow> b < c"
  "a > 0 \<Longrightarrow> a * b \<le> a * c \<Longrightarrow> b \<le> c"
  "a > 0 \<Longrightarrow> b * a \<le> a * c \<Longrightarrow> b \<le> c" by simp+

subsection {* of_nat, of_int, of_rat *}

theorem of_nat_ge_0 [rewrite]: "x \<noteq> 0 \<Longrightarrow> of_nat x = of_nat (x - 1) + 1"
  by (metis One_nat_def Suc_pred add.commute not_gr0 of_nat_Suc)
setup {* add_backward_prfstep @{thm less_imp_of_nat_less} *}
setup {* add_forward_prfstep @{thm of_nat_less_imp_less} *}
setup {* fold add_rewrite_rule @{thms Num.of_nat_simps} *}
setup {* add_rewrite_rule @{thm of_nat_numeral} *}
setup {* add_rewrite_rule @{thm of_nat_power} *}

setup {* add_rewrite_rule @{thm Fract_of_int_quotient} *}
setup {* add_rewrite_rule @{thm of_int_of_nat_eq} *}
setup {* add_rewrite_rule @{thm of_int_diff} *}
lemma le_0_nat_to_rat [forward]: "rat_of_nat n \<le> 0 \<Longrightarrow> n = 0" by simp

setup {* add_rewrite_rule @{thm of_rat_divide} *}
setup {* add_rewrite_rule @{thm of_rat_of_int_eq} *}
setup {* add_rewrite_rule @{thm of_rat_inverse} *}
setup {* add_rewrite_rule @{thm of_rat_of_nat_eq} *}

subsection {* Induction and case check on int, rat *}

theorem int_diff_cases' [resolve]: "\<exists>m n. z = int m - int n" using int_diff_cases by blast

theorem rat_cases [resolve]: "\<exists>b a. b > 0 \<and> r = Fract a b" by (induct r) auto

subsection {* Archimedean fields *}

setup {* add_resolve_prfstep @{thm ex_le_of_nat} *}
setup {* add_resolve_prfstep @{thm ex_less_of_nat} *}
setup {* add_resolve_prfstep @{thm ex_inverse_of_nat_less} *}
setup {* add_resolve_prfstep @{thm ex_less_of_nat_mult} *}

subsection {* Misc *}

setup {* add_rewrite_rule @{thm power2_eq_square} *}

theorem Max_ge_nat_finite: "i < (k::nat) \<Longrightarrow> f i \<le> Max (f ` {..<k})" by simp
setup {* add_backward_prfstep_cond @{thm Max_ge_nat_finite} [with_term "Max (?f ` {..<?k})"] *}

theorem lift_Suc_mono_le' [backward2]: fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<forall>n. f n \<le> f (n + 1)) \<Longrightarrow> n \<le> n' \<Longrightarrow> f n \<le> f n'" using lift_Suc_mono_le by auto

theorem lift_Suc_mono_ge' [backward2]: fixes f :: "nat \<Rightarrow> 'a::order"
  shows "(\<forall>n. f n \<ge> f (n + 1)) \<Longrightarrow> n \<le> n' \<Longrightarrow> f n \<ge> f n'"
  using order.lift_Suc_mono_le[OF dual_order, of "f"] by auto

end
