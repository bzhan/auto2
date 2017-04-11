(* Setup for proof steps related to arithmetic, mostly on natural numbers. *)

theory Arith_Thms
imports Order_Thms Binomial
begin

(* Reducing inequality on natural numbers. *)
theorem reduce_le_plus_consts: "(x::nat) + n1 \<le> y + n2 \<Longrightarrow> x \<le> y + (n2-n1)" by simp
theorem reduce_le_plus_consts': "n1 \<ge> n2 \<Longrightarrow> (x::nat) + n1 \<le> y + n2 \<Longrightarrow> x + (n1-n2) \<le> y" by simp
theorem reduce_less_plus_consts: "(x::nat) + n1 < y + n2 \<Longrightarrow> x < y + (n2-n1)" by simp
theorem reduce_less_plus_consts': "n1 \<ge> n2 \<Longrightarrow> (x::nat) + n1 < y + n2 \<Longrightarrow> x + (n1-n2) < y" by simp

(* To normal form. *)
theorem norm_less_lminus: "(x::nat) - n < y \<Longrightarrow> x \<le> y + (n-1)" by simp
theorem norm_less_lplus:  "(x::nat) + n < y \<Longrightarrow> x + (n+1) \<le> y" by simp
theorem norm_less_rminus: "(x::nat) < y - n \<Longrightarrow> x + (n+1) \<le> y" by simp
theorem norm_less_rplus:  "(x::nat) < y + n \<Longrightarrow> x \<le> y + (n-1)" by simp
theorem norm_less:        "(x::nat) < y     \<Longrightarrow> x + 1 \<le> y"     by simp
theorem norm_le_lminus: "(x::nat) - n \<le> y \<Longrightarrow> x \<le> y + n"  by simp
theorem norm_le_rminus: "(x::nat) \<le> y - n \<Longrightarrow> x \<le> y + 0"  by simp
theorem norm_le: "(x::nat) \<le> y \<Longrightarrow> x \<le> y + 0" by simp

(* Transitive resolve. *)
theorem trans_resolve1: "n1 > 0 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> (y::nat) + n2 \<le> x \<Longrightarrow> False" by simp
theorem trans_resolve2: "n1 > n2 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> (y::nat) \<le> x + n2 \<Longrightarrow> False" by simp

(* Transitive. *)
theorem trans1: "(x::nat) + n1 \<le> y \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x + (n1+n2) \<le> z" by simp
theorem trans2: "(x::nat) \<le> y + n1 \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x \<le> z + (n1+n2)" by simp
theorem trans3: "(x::nat) + n1 \<le> y \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x \<le> z + (n2-n1)" by simp
theorem trans4: "n1 > n2 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x + (n1-n2) \<le> z" by simp
theorem trans5: "(x::nat) \<le> y + n1 \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x \<le> z + (n1-n2)" by simp
theorem trans6: "n2 > n1 \<Longrightarrow> (x::nat) \<le> y + n1 \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x + (n2-n1) \<le> z" by simp

(* Resolve. *)
theorem single_resolve: "n > 0 \<Longrightarrow> (x::nat) + n \<le> x \<Longrightarrow> False" by simp
theorem single_resolve_const: "n > 0 \<Longrightarrow> (x::nat) + n \<le> 0 \<Longrightarrow> False" by simp

(* Comparison with constants. *)
theorem cv_const1: "(x::nat) + n \<le> y \<Longrightarrow> 0 + (x+n) \<le> y" by simp  (* x is const *)
theorem cv_const2: "(x::nat) + n \<le> y \<Longrightarrow> x \<le> 0 + (y-n)" by simp  (* y is const *)
theorem cv_const3: "y < n \<Longrightarrow> (x::nat) + n \<le> y \<Longrightarrow> x + (n-y) \<le> 0" by simp  (* y is const (contradiction with 0 \<le> x) *)
theorem cv_const4: "(x::nat) \<le> y + n \<Longrightarrow> 0 + (x-n) \<le> y" by simp  (* x is const *)
theorem cv_const5: "(x::nat) \<le> y + n \<Longrightarrow> 0 \<le> y + (n-x)" by simp  (* x is const (trivial) *)
theorem cv_const6: "(x::nat) \<le> y + n \<Longrightarrow> x \<le> 0 + (y+n)" by simp  (* y is const *)

(* Misc *)
theorem nat_eq_to_ineqs: "(x::nat) = y + n \<Longrightarrow> x \<le> y + n \<and> x \<ge> y + n" by simp
theorem nat_ineq_impl_not_eq: "(x::nat) + n \<le> y \<Longrightarrow> n > 0 \<Longrightarrow> x \<noteq> y" by simp

ML_file "arith.ML"
ML_file "order.ML"

(* General rings. *)
theorem double_neg [rewrite]: "-b = (a::('a::ring)) \<Longrightarrow> -a = b" by auto
theorem divide_cancel [rewrite]: "(a::('a::field)) \<noteq> 0 \<Longrightarrow> a * inverse a * bu = bu" by simp
theorem ring_distrib: "((a::('a::{semiring,one})) + b) * c = a * c + b * c" by (simp add: ring_distribs)
setup {* add_rewrite_rule_back_cond @{thm ring_distrib}
  [with_cond "?c \<noteq> 1", with_filt (order_filter "a" "b")] *}
theorem ring_distrib_minus: "((a::('a::{ring,one})) - b) * c = a * c - b * c" by (simp add: left_diff_distrib)
setup {* add_rewrite_rule_back_cond @{thm ring_distrib_minus} [with_cond "?c \<noteq> 1"] *}

theorem of_int_neg_one: "of_int (-1) = -1" by simp

theorem of_rat_inverse_numeral: "of_rat (inverse (numeral x)) = inverse (numeral x)"
  by (metis of_rat_inverse of_rat_numeral_eq)

theorem power_ge_0 [rewrite]: "m \<noteq> 0 \<Longrightarrow> p ^ m = p * (p ^ (m - 1))" by (simp add: power_eq_if)

(* Functions used in split_polynomial_by_sign. *)
theorem split_by_sign1: "((a::'a::comm_ring) - b) + c = (a + c) - b" by simp
theorem split_by_sign2: "((a::'a::comm_ring) - b) + c * (-n) = a - (b + c * n)" by simp
theorem split_by_sign3: "(a::'a::comm_ring) - 0 = a" by simp
theorem split_by_sign4: "(c::'a::comm_ring) * (-n) = 0 - c * n" by simp

ML_file "rings.ML"
ML_file "rings_test.ML"

(* Property predicates on numbers. *)
definition is_positive :: "'a::{ord,zero} \<Rightarrow> bool" where
  "is_positive x \<longleftrightarrow> (x > 0)"
definition is_negative :: "'a::{ord,zero} \<Rightarrow> bool" where
  "is_negative x \<longleftrightarrow> (x < 0)"
definition is_non_negative :: "'a::{ord,zero} \<Rightarrow> bool" where
  "is_non_negative x \<longleftrightarrow> (x \<ge> 0)"
setup {* fold add_property_const [@{term "is_positive"}, @{term "is_negative"}] *}
declare is_positive_def [simp]
declare is_non_negative_def [simp]

(* Ordering on Nats. *)
setup {* add_forward_prfstep_cond @{thm Nat.le_neq_implies_less} [with_cond "?m \<noteq> ?n"] *}
theorem lt_one: "(m::nat) < 1 \<Longrightarrow> m = 0" by simp
setup {* add_forward_prfstep_cond @{thm lt_one} [with_cond "?m \<noteq> 0"] *}
setup {* add_resolve_prfstep @{thm Nat.le0} *}
setup {* add_backward_prfstep_cond @{thm Nat.mult_le_mono1} [with_term "?k", with_cond "?k \<noteq> 1"] *}
setup {* add_resolve_prfstep_cond @{thm Nat.not_add_less1} [with_term "?i"] *}
theorem not_minus_less: "\<not>(i::nat) < (i - j)" by simp
setup {* add_resolve_prfstep @{thm not_minus_less} *}
theorem nat_le_prod_with_same [backward]: "m \<noteq> 0 \<Longrightarrow> (n::nat) \<le> m * n" by simp
theorem nat_le_prod_with_le [backward1]: "k \<noteq> 0 \<Longrightarrow> (n::nat) \<le> m \<Longrightarrow> (n::nat) \<le> k * m"
  using le_trans nat_le_prod_with_same by blast
theorem nat_plus_le_to_less [backward1]: "b \<noteq> 0 \<Longrightarrow> (a::nat) + b \<le> c \<Longrightarrow> a < c" by simp

setup {* add_forward_prfstep_cond (equiv_forward_th @{thm Nat.le_diff_conv}) [with_term "?i + ?k", with_filt (not_numc_filter "k")] *}
setup {* add_rewrite_rule_cond @{thm Nat.le_diff_conv2} [with_term "?i + ?k"] *}
theorem nat_less_diff_conv: "(i::nat) < j - k \<Longrightarrow> i + k < j" by simp
setup {* add_forward_prfstep_cond @{thm nat_less_diff_conv} [with_filt (not_numc_filter "k"), with_term "?i + ?k"]*}
theorem Nat_le_diff_conv2_same [forward]: "(i::nat) \<le> i - j \<Longrightarrow> j \<le> i \<Longrightarrow> j = 0" by simp
theorem Nat_le_diff1_conv [forward]: "(n::nat) \<le> n - 1 \<Longrightarrow> n = 0" by simp
theorem nat_gt_zero [forward]: "b - a > 0 \<Longrightarrow> b > (a::nat)" by simp
theorem n_minus_1_less_n [backward]: "(n::nat) \<noteq> 0 \<Longrightarrow> n - 1 < n" by simp
setup {* add_rewrite_rule @{thm le_add_diff_inverse} *}
setup {* add_rewrite_rule @{thm Nat.diff_diff_cancel} *}

(* Intervals. *)
definition open_interval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ < _ < _" [50,50,50] 50) where "a < b < c \<longleftrightarrow> a < b \<and> b < c"
definition closed_interval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<le> _ \<le> _" [50,50,50] 50) where "a \<le> b \<le> c \<longleftrightarrow> a \<le> b \<and> b \<le> c"
setup {* fold add_rewrite_rule [@{thm open_interval_def}, @{thm closed_interval_def}] *}

(* Set intervals. *)
theorem interval_empty [rewrite]: "{a::nat. x \<le> a \<and> a < x} = {}" by simp
theorem interval_single [rewrite]: "{a::nat. x \<le> a \<and> a < x + 1} = {x}" using Collect_cong by auto

(* Addition. *)
theorem nat_add_eq_self_zero': "(m::nat) = m + n \<Longrightarrow> n = 0" by simp
setup {* add_forward_prfstep @{thm nat_add_eq_self_zero'} *}
theorem nat_mult_2: "(a::nat) + a = 2 * a" by simp
setup {* add_rewrite_rule_cond @{thm nat_mult_2} [with_cond "?a \<noteq> 0"] *}
theorem plus_one_non_zero [resolve]: "\<not>(n::nat) + 1 = 0" by simp

(* Diff. *)
setup {* add_rewrite_rule @{thm Nat.minus_nat.diff_0} *}
setup {* add_rewrite_rule @{thm Nat.diff_self_eq_0} *}
setup {* add_rewrite_rule @{thm Nat.diff_add_inverse} *}
setup {* add_rewrite_rule @{thm Nat.diff_add_inverse2} *}
theorem n_minus_1_eq_0 [forward]: "(n::nat) \<noteq> 0 \<Longrightarrow> n - 1 = 0 \<Longrightarrow> n = 1" by simp
theorem diff_distrib: "(i::nat) \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> j - (k - i) = j - k + i" by simp
setup {* add_rewrite_rule_cond @{thm diff_distrib} (with_filts [size1_filter "j", size1_filter "k", size1_filter "i"]) *}
theorem nat_minus_add_1 [rewrite]: "(n::nat) \<noteq> 0 \<Longrightarrow> (n - 1) + 1 = n" by simp
theorem plus_1_plus_minus_1 [rewrite]: "(b::nat) \<noteq> 0 \<Longrightarrow> (a + 1) + (b - 1) = a + b" by simp
theorem nat_same_minus_ge [forward]: "(c::nat) - a \<ge> c - b \<Longrightarrow> a \<le> c \<Longrightarrow> a \<le> b" by arith

theorem diff_eq_zero [forward]: "j - k = 0 \<Longrightarrow> (k::nat) \<le> j \<Longrightarrow> j = k" by simp
theorem diff_eq_zero' [forward]: "j - k + i = j \<Longrightarrow> (k::nat) \<le> j \<Longrightarrow> k = i" by simp

(* Divides. *)
setup {* add_forward_prfstep_cond (equiv_forward_th @{thm dvd_def}) (with_conds ["?a \<noteq> ?b", "?a \<noteq> ?b * ?k"]) *}
setup {* add_gen_prfstep ("shadow_exists_triv",
  [WithFact @{term_pat "\<exists>x. (?a::nat) = ?a * x"}, ShadowFirst]) *}
setup {* add_forward_prfstep_cond @{thm dvd_trans}
  (with_conds ["?a \<noteq> ?b", "?b \<noteq> ?c", "?a \<noteq> ?c"]) *}
setup {* add_forward_prfstep_cond @{thm Nat.dvd_antisym} [with_cond "?x \<noteq> ?y"] *}
theorem dvd_cancel [backward1]: "c > 0 \<Longrightarrow> (a::nat) * c dvd b * c \<Longrightarrow> a dvd b" by simp
setup {* add_forward_prfstep (equiv_forward_th @{thm dvd_add_right_iff}) *}

(* Divisibility: existence. *)
setup {* add_resolve_prfstep @{thm dvd_refl} *}
theorem exists_n_dvd_n [backward]: "P (n::nat) \<Longrightarrow> \<exists>k. k dvd n \<and> P k" using dvd_refl by blast
setup {* add_resolve_prfstep @{thm one_dvd} *}

theorem any_n_dvd_0 [forward]: "\<not> (\<exists> k. k dvd (0::nat) \<and> P k) \<Longrightarrow> \<not> (\<exists> k. P k)" by simp

theorem n_dvd_one: "(n::nat) dvd 1 \<Longrightarrow> n = 1" by simp
setup {* add_forward_prfstep_cond @{thm n_dvd_one} [with_cond "?n \<noteq> 1"] *}

(* Products. *)
setup {* add_rewrite_rule @{thm mult_zero_left} *}
theorem prod_ineqs [forward]: "m * k > (0::nat) \<Longrightarrow> 1 \<le> m \<and> m \<le> m * k \<and> 1 \<le> k \<and> k \<le> m * k" by simp
setup {* add_prfstep_custom
  ("prod_ineqs'",
   [WithFact @{term_pat "(?NUMC::nat) = ?m * ?k"},
    Filter (fn _ => fn (_, inst) => Nat_Arith.lookup_numc0 inst >= 2),
    Filter (not_numc_filter "m")],
   PRIORITY_ADD,
   (fn ((id, inst), ths) => fn _ => fn _ =>
      let
        val less_th = (Nat_Arith.nat_less_th 0 (Nat_Arith.lookup_numc0 inst))
                        |> apply_to_thm' (Conv.arg_conv (rewr_obj_eq (the_single ths)))
      in
        [Update.thm_update (id, [less_th] MRS @{thm prod_ineqs})]
      end)) *}

theorem prod_cancel: "(a::nat) * b = a * c \<Longrightarrow> a > 0 \<Longrightarrow> b = c" by auto
setup {* add_forward_prfstep_cond @{thm prod_cancel} [with_cond "?b \<noteq> ?c"] *}

theorem mult_n1n: "(n::nat) = m * n \<Longrightarrow> n > 0 \<Longrightarrow> m = 1" by auto
setup {* add_forward_prfstep_cond @{thm mult_n1n} [with_cond "?m \<noteq> 1"] *}

theorem prod_is_one [forward]: "(x::nat) * y = 1 \<Longrightarrow> x = 1" by simp

theorem prod_dvd_intro [backward]: "(k::nat) dvd m \<or> k dvd n \<Longrightarrow> k dvd m * n"
  using dvd_mult dvd_mult2 by blast

(* Definition of gcd. *)
setup {* add_forward_prfstep_cond @{thm gcd_dvd1} [with_term "gcd ?a ?b"] *}
setup {* add_forward_prfstep_cond @{thm gcd_dvd2} [with_term "gcd ?a ?b"] *}

(* Coprimality. *)
setup {* add_backward_prfstep @{thm coprime_exp} *}
setup {* add_backward1_prfstep @{thm coprime_dvd_mult} *}
theorem coprime_dvd [forward]:
  "coprime (a::nat) b \<Longrightarrow> p dvd a \<Longrightarrow> p > 1 \<Longrightarrow> \<not> p dvd b" by (metis coprime_nat neq_iff)

(* Powers. *)
setup {* add_rewrite_rule @{thm power_0} *}
setup {* add_rewrite_rule_cond @{thm power_one} [with_cond "?n \<noteq> 0"] *}
setup {* add_rewrite_rule_cond @{thm power_one_right} [with_cond "?a \<noteq> 1"] *}
setup {* add_gen_prfstep ("power_case_intro",
  [WithTerm @{term_pat "?p ^ (?FREE::nat)"}, CreateCase @{term_pat "(?FREE::nat) = 0"}]) *}

theorem one_is_power_of_any: "\<exists>i. (1::nat) = a ^ i" by (metis power.simps(1))
setup {* add_resolve_prfstep @{thm one_is_power_of_any} *}

theorem power_add_one: "(p::nat) ^ i * p = p ^ (i + 1)" by (metis Suc_eq_plus1 mult.commute power_Suc)
setup {* add_rewrite_rule_cond @{thm power_add_one} [with_filt (size1_filter "i")] *}

theorem power_dvd [forward]: "(p::nat)^n dvd a \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p dvd a" using dvd_power dvd_trans by blast

theorem power_eq_one: "(b::nat) ^ n = 1 \<Longrightarrow> b = 1 \<or> n = 0"
  by (metis One_nat_def Suc_lessI nat_zero_less_power_iff power_0 power_inject_exp)
setup {* add_forward_prfstep_cond @{thm power_eq_one} (with_conds ["?b \<noteq> 1", "?n \<noteq> 0"]) *}

(* Factorial. *)
theorem fact_ge_1_nat: "fact (n::nat) \<ge> (1::nat)" by simp
setup {* add_forward_prfstep_cond @{thm fact_ge_1_nat} [with_term "fact ?n"] *}
setup {* add_backward1_prfstep @{thm dvd_fact} *}

(* Successor function. *)
setup {* add_rewrite_rule @{thm Nat.Suc_eq_plus1} *}

(* Induction. *)
theorem nat_induct': "P 0 \<Longrightarrow> (\<forall>n. P (n-1) \<longrightarrow> P n) \<Longrightarrow> P (n::nat)"
  by (metis One_nat_def diff_Suc_Suc diff_zero nat_induct)

theorem nat_upper_strong_induct:
  "n < M \<Longrightarrow> (\<And>n. \<forall>m. m > n \<longrightarrow> m < M \<longrightarrow> P m \<Longrightarrow> P n) \<Longrightarrow> P (n::nat)"
  apply (induct "M - n" arbitrary: n rule: nat_less_induct)
  using diff_less_mono2 by blast

setup {*
  add_prfstep_induction @{thm nat_induct'} #>
  add_prfstep_strong_induction @{thm nat_less_induct} #>
  add_prfstep_upper_strong_induction @{thm nat_upper_strong_induct}
*}

end
