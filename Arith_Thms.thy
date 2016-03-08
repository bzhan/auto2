(* Setup for proof steps related to arithmetic, mostly on natural numbers. *)

theory Arith_Thms
imports Auto2_Base Order_Thms Logic_Thms Binomial
begin

setup {* fold add_rew_const [@{term "0::nat"}, @{term "1::nat"}] *}

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
theorem divide_cancel [rewrite]: "(a::('a::field)) \<noteq> 0 \<Longrightarrow> bu * a * inverse a = bu" by simp
setup {* add_rewrite_rule_back_cond @{thm ring_distribs(2)} [with_filt (order_filter "a" "b")] *}
setup {* add_rewrite_rule_back @{thm left_diff_distrib} *}

ML_file "rings.ML"
ML_file "rings_test.ML"

(* Ordering on Nats. *)
theorem lt_one: "(m::nat) < 1 \<Longrightarrow> m = 0" by simp
setup {* add_forward_prfstep_cond @{thm lt_one} [with_cond "?m \<noteq> 0"] *}
setup {* add_resolve_prfstep @{thm Nat.le0} *}
setup {* add_backward_prfstep_cond @{thm Nat.mult_le_mono1} [with_cond "?k \<noteq> 1"] *}
setup {* add_resolve_prfstep @{thm Nat.trans_le_add2} *}
setup {* add_resolve_prfstep_cond @{thm Nat.not_add_less1} [with_filt (not_numc_filter "j")] *}
theorem not_minus_less: "\<not>(i::nat) < (i - j)" by simp
setup {* add_resolve_prfstep_cond @{thm not_minus_less} [with_filt (not_numc_filter "j")] *}

setup {* add_forward_prfstep_cond (equiv_forward_th @{thm Nat.le_diff_conv}) [with_term "?i + ?k", with_filt (not_numc_filter "k")] *}
setup {* add_rewrite_rule_cond @{thm Nat.le_diff_conv2} [with_term "?i + ?k"] *}
theorem nat_less_diff_conv: "(i::nat) < j - k \<Longrightarrow> i + k < j" by simp
setup {* add_forward_prfstep_cond @{thm nat_less_diff_conv} [with_filt (not_numc_filter "k"), with_term "?i + ?k"]*}
theorem Nat_le_diff_conv2_same [forward]: "(i::nat) \<le> i - j \<Longrightarrow> j \<le> i \<Longrightarrow> j = 0" by simp
theorem Nat_le_diff1_conv [forward]: "(n::nat) \<le> n - 1 \<Longrightarrow> n = 0" by simp
theorem nat_gt_zero [forward]: "b - a > 0 \<Longrightarrow> b > (a::nat)" by simp
theorem Nat_le_add_diff_inverse [rewrite]: "(b::nat) \<le> a \<Longrightarrow> b + (a - b) = a" by simp
setup {* add_rewrite_rule @{thm Nat.diff_diff_cancel} *}

(* Intervals. *)
definition open_interval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ < _ < _" [50,50,50] 50) where "a < b < c \<longleftrightarrow> a < b \<and> b < c"
definition closed_interval :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" ("_ \<le> _ \<le> _" [50,50,50] 50) where "a \<le> b \<le> c \<longleftrightarrow> a \<le> b \<and> b \<le> c"
setup {* fold add_rewrite_rule [@{thm open_interval_def}, @{thm closed_interval_def}] *}

(* Addition. *)
setup {* add_forward_prfstep @{thm Nat.add_eq_self_zero} *}
theorem nat_mult_2: "(a::nat) + a = 2 * a" by simp
setup {* add_rewrite_rule_cond @{thm nat_mult_2} [with_cond "?a \<noteq> 0"] *}

(* Diff. *)
setup {* add_rewrite_rule @{thm Nat.minus_nat.diff_0} *}
setup {* add_rewrite_rule @{thm Nat.diff_self_eq_0} *}
setup {* add_rewrite_rule @{thm Nat.diff_add_inverse} *}
theorem n_minus_1_eq_0 [forward]: "(n::nat) \<noteq> 0 \<Longrightarrow> n - 1 = 0 \<Longrightarrow> n = 1" by simp
theorem diff_distrib: "(i::nat) \<le> k \<Longrightarrow> k \<le> j \<Longrightarrow> j - (k - i) = j - k + i" by simp
setup {* add_rewrite_rule_cond @{thm diff_distrib} (with_filts [size1_filter "j", size1_filter "k", size1_filter "i"]) *}
theorem nat_minus_add_1 [rewrite]: "(n::nat) \<noteq> 0 \<Longrightarrow> (n - 1) + 1 = n" by simp

theorem diff_eq_zero [forward]: "j - k = 0 \<Longrightarrow> (k::nat) \<le> j \<Longrightarrow> j = k" by simp
theorem diff_eq_zero' [forward]: "j - k + i = j \<Longrightarrow> (k::nat) \<le> j \<Longrightarrow> k = i" by simp

(* Divides. *)
setup {* add_forward_prfstep_cond (equiv_forward_th @{thm dvd_def}) (with_conds ["?a \<noteq> ?b", "?a \<noteq> ?b * ?k"]) *}
setup {* add_forward_prfstep_cond @{thm Nat.dvd.order.trans}
  (with_conds ["?a \<noteq> ?b", "?b \<noteq> ?c", "?a \<noteq> ?c"]) *}
setup {* add_forward_prfstep_cond @{thm Nat.dvd.antisym} [with_cond "?x \<noteq> ?y"] *}
theorem dvd_cancel [backward1]: "c > 0 \<Longrightarrow> (a::nat) * c dvd b * c \<Longrightarrow> a dvd b" by simp
setup {* add_forward_prfstep (equiv_forward_th @{thm dvd_add_right_iff}) *}

(* Divisibility: existence. *)
setup {* add_resolve_prfstep @{thm dvd_refl} *}
theorem exists_n_dvd_n [backward]: "P (n::nat) \<Longrightarrow> \<exists>k. k dvd n \<and> P k" using dvd_refl by blast
theorem exists_dvd_prod: "\<forall>m::nat. m dvd a * b \<longrightarrow> P m \<Longrightarrow> P a" using dvd_triv_left by blast
setup {* add_forward_prfstep_cond @{thm exists_dvd_prod}
  (with_filt (ac_atomic_filter @{const_name times} "a") :: with_conds ["?a \<noteq> 1", "?b \<noteq> 1"]) *}
setup {* add_resolve_prfstep @{thm one_dvd} *}

theorem any_n_dvd_0 [forward]: "\<not> (\<exists> k. k dvd (0::nat) \<and> P k) \<Longrightarrow> \<not> (\<exists> k. P k)" by simp

theorem n_dvd_one: "(n::nat) dvd 1 \<Longrightarrow> n = 1" by simp
setup {* add_forward_prfstep_cond @{thm n_dvd_one} [with_cond "?n \<noteq> 1"] *}

(* Products. *)
setup {* add_rewrite_rule @{thm mult_zero_left} *}
theorem prod_ineqs: "(n::nat) = m * k \<Longrightarrow> n > 0 \<Longrightarrow> 1 \<le> m \<and> m \<le> n" by simp
setup {* add_forward_prfstep_cond @{thm prod_ineqs}
  ([with_filt (ac_atomic_filter @{const_name times} "m"),
    with_filt (size1_filter "n")] @
   (with_conds ["?m \<noteq> 1", "?k \<noteq> 1", "?n \<noteq> ?m", "?n \<noteq> ?k"])) *}
setup {* add_prfstep_custom
  ("prod_ineqs'",
   [WithFact @{term_pat "(?NUMC::nat) = ?m * ?k"},
    Filter (fn _ => fn (_, inst) => Nat_Arith.lookup_numc0 inst >= 2),
    Filter (ac_atomic_filter @{const_name times} "m"),
    Filter (not_numc_filter "m")],
   [Update.ADD_ITEMS],
   (fn ((id, inst), ths) => fn _ => fn _ =>
       [Update.thm_update (id, [the_single ths, Nat_Arith.nat_less_th 0 (Nat_Arith.lookup_numc0 inst)] MRS @{thm prod_ineqs})])) *}

theorem prod_cancel: "(a::nat) * b = a * c \<Longrightarrow> a > 0 \<Longrightarrow> b = c" by auto
setup {* add_forward_prfstep_cond @{thm prod_cancel} [with_cond "?b \<noteq> ?c"] *}

theorem mult_n1n: "(n::nat) = m * n \<Longrightarrow> n > 0 \<Longrightarrow> m = 1" by auto
setup {* add_forward_prfstep_cond @{thm mult_n1n} [with_cond "?m \<noteq> 1"] *}

theorem prod_is_one [forward]: "(x::nat) * y = 1 \<Longrightarrow> x = 1" by simp

theorem prod_dvd_intro: "(k::nat) dvd m \<or> k dvd n \<Longrightarrow> k dvd m * n" using dvd_mult dvd_mult2 by blast
setup {* add_backward_prfstep_cond @{thm prod_dvd_intro}
  [with_filt (canonical_split_filter @{const_name times} "m" "n")] *}

(* Definition of gcd. *)
setup {* add_forward_prfstep_cond @{thm gcd_dvd1_nat} [with_term "gcd ?a ?b"] *}

(* Coprimality. *)
setup {* add_backward_prfstep @{thm coprime_exp_nat} *}
setup {* add_backward1_prfstep @{thm coprime_dvd_mult_nat} *}
theorem coprime_dvd [forward]:
  "coprime (a::nat) b \<Longrightarrow> p dvd a \<Longrightarrow> p > 1 \<Longrightarrow> \<not> p dvd b" by (metis coprime_nat neq_iff)

(* Powers. *)
setup {* add_rewrite_rule @{thm power_0} *}
setup {* add_rewrite_rule_cond @{thm power_one} [with_cond "?n \<noteq> 0"] *}
setup {* add_rewrite_rule_cond @{thm power_one_right} [with_cond "?a \<noteq> 1"] *}
theorem power_ge_0 [rewrite]: "m \<noteq> 0 \<Longrightarrow> p ^ m = p * (p ^ (m - 1))" by (simp add: power_eq_if)
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
setup {*
  add_prfstep_induction @{thm nat_induct'} #>
  add_prfstep_strong_induction @{thm nat_less_induct}
*}

end
