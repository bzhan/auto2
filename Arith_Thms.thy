theory Arith_Thms
imports Auto2_Base Logic_Thms GCD Binomial
begin

setup {* fold add_rew_const [@{term "0::nat"}, @{term "1::nat"}] *}

(* Ordering: lattice. *)
setup {* add_forward_prfstep (equiv_forward_th @{thm Orderings.linorder_not_less}) *}
setup {* add_forward_prfstep (equiv_forward_th @{thm Orderings.linorder_not_le}) *}
setup {* add_resolve_prfstep @{thm Nat.less_not_refl} *}
setup {* add_forward_prfstep @{thm Nat.less_imp_le_nat} *}
setup {* add_forward_prfstep_cond @{thm Nat.le_trans} (with_conds ["?i \<noteq> ?j", "?j \<noteq> ?k"]) *}
setup {* add_forward_prfstep_cond @{thm Nat.le_neq_implies_less} [with_cond "?m \<noteq> ?n"] *}
setup {* add_forward_prfstep_cond @{thm Nat.le_antisym} [with_filt (order_filter "m" "n"), with_cond "?m \<noteq> ?n"] *}

(* Ordering: max and min. *)
theorem min_le_same: "(a::nat) \<le> b \<Longrightarrow> a \<le> c \<Longrightarrow> a \<le> min b c" by simp
setup {* add_backward2_prfstep @{thm min_le_same} *}
theorem max_le_same: "(a::nat) \<le> c \<Longrightarrow> b \<le> c \<Longrightarrow> max a b \<le> c" by simp
setup {* add_backward2_prfstep @{thm max_le_same} *}
theorem min_le_pair: "(a::nat) \<le> b \<Longrightarrow> c \<le> d \<Longrightarrow> min a c \<le> min b d" using min.mono by blast
setup {* add_backward2_prfstep @{thm min_le_pair} *}
setup {* add_simp_rule @{thm min.idem} *}

(* Ordering on Nats. *)
theorem nat_not_sym: "(m::nat) \<noteq> n \<Longrightarrow> n \<noteq> m" by simp
setup {* add_forward_prfstep @{thm nat_not_sym} *}
setup {* add_backward_prfstep_cond @{thm Nat.mult_le_mono1} [with_cond "?k \<noteq> 1"] *}
theorem lt_one: "(m::nat) < 1 \<Longrightarrow> m = 0" by simp
setup {* add_forward_prfstep_cond @{thm lt_one} [with_cond "?m \<noteq> 0"] *}
theorem gt_zero: "(m::nat) > C \<Longrightarrow> m > 0" by simp
setup {* add_forward_prfstep_cond @{thm gt_zero} [with_cond "?C \<noteq> 0"] *}
setup {* add_resolve_prfstep @{thm Nat.trans_le_add2} *}

(* Natural numbers. *)
setup {* add_simp_rule @{thm Nat.minus_nat.diff_0} *}
theorem n_minus_1_eq_0: "(n::nat) \<noteq> 0 \<Longrightarrow> n - 1 = 0 \<Longrightarrow> n = 1" by simp
setup {* add_forward_prfstep @{thm n_minus_1_eq_0} *}
setup {* add_rewrite_rule_cond @{thm Nat.nat_distrib(2)}
  (with_filt (canonical_split_filter @{const_name plus} "m" "n") ::
   with_conds ["?k \<noteq> 1", "?m \<noteq> 0", "?n \<noteq> 0"]) *}
setup {* add_forward_prfstep @{thm Nat.add_eq_self_zero} *}

(* Divides. *)
setup {* add_rewrite_rule @{thm dvd_def} *}
theorem dvd_transitive: "(m::nat) dvd n \<Longrightarrow> n dvd p \<Longrightarrow> m dvd p" using dvd_trans by blast
theorem dvd_transitive': "(m::nat) dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n" by (simp add: dvd.eq_iff)
setup {*
  add_forward_prfstep_cond @{thm dvd_transitive} (with_conds ["?m \<noteq> ?n", "?n \<noteq> ?p", "?m \<noteq> ?p"]) #>
  add_forward_prfstep_cond @{thm dvd_transitive'} [with_cond "?m \<noteq> ?n"] *}
theorem dvd_cancel: "c > 0 \<Longrightarrow> (a::nat) * c dvd b * c \<Longrightarrow> a dvd b" by simp
setup {* add_backward1_prfstep @{thm dvd_cancel} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm dvd_add_right_iff}) *}

(* Divisibility: existence. *)
theorem n_dvd_n: "(n::nat) dvd n" by simp
setup {* add_resolve_prfstep @{thm n_dvd_n} *}
setup {* add_prfstep_two_stage ("exists_n_dvd_n",
  [WithGoal @{term_pat "\<exists> k. k dvd (?n::nat) \<and> ?A"},
   GetFact (@{term_pat "(?n::nat) dvd ?n"}, @{thm n_dvd_n})],
  @{thm exists_intro}) *}

theorem dvd_prod: "(a::nat) dvd a * b" by simp
setup {* add_prfstep_two_stage ("dvd_prod",
  [WithFact @{term_pat "\<forall> m::nat. m dvd (?a * ?b) \<longrightarrow> ?C"},
   GetFact (@{term_pat "(?a::nat) dvd (?a * ?b)"}, @{thm dvd_prod}),
   Filter (ac_atomic_filter @{const_name times} "a"),
   Filter (neqt_filter "a" @{term "1::nat"}),
   Filter (neqt_filter "b" @{term "1::nat"})],
  @{thm forall_resolve}) *}

theorem one_dvd_any: "1 dvd (n::nat)" by simp
setup {* add_resolve_prfstep @{thm one_dvd_any} *}

theorem any_n_dvd_0: "\<not> (\<exists> k. k dvd (0::nat) \<and> P k) \<Longrightarrow> \<not> (\<exists> k. P k)" by simp
setup {* add_prfstep_thm ("any_n_dvd_0",
  [WithGoal @{term_pat "(\<exists> k. k dvd (0::nat) \<and> ?A)"}], @{thm any_n_dvd_0}) *}

theorem n_dvd_one: "(n::nat) dvd 1 \<Longrightarrow> n = 1" by simp
setup {* add_forward_prfstep_cond @{thm n_dvd_one} [with_cond "?n \<noteq> 1"] *}

(* Products. *)
setup {* add_simp_rule @{thm mult_zero_left} *}
theorem prod_ineqs: "(m::nat) * k > 0 \<Longrightarrow> 1 \<le> m \<and> m \<le> m * k" by simp
setup {* add_forward_prfstep_cond @{thm prod_ineqs}
  (with_filt (ac_atomic_filter @{const_name times} "m") :: with_conds ["?m \<noteq> 1", "?k \<noteq> 1"]) *}

theorem prod_cancel: "(a::nat) > 0 \<Longrightarrow> a * b = a * c \<Longrightarrow> b = c" by simp
setup {* add_forward_prfstep_cond @{thm prod_cancel} [with_cond "?b \<noteq> ?c"] *}

theorem mult_n1n: "(n::nat) = m * n \<Longrightarrow> n > 0 \<Longrightarrow> m = 1" by simp
setup {* add_forward_prfstep_cond @{thm mult_n1n} [with_cond "?m \<noteq> 1"] *}

theorem prod_is_one: "(x::nat) * y = 1 \<Longrightarrow> x = 1" by simp
setup {* add_forward_prfstep @{thm prod_is_one} *}

theorem prod_dvd_intro: "(k::nat) dvd m \<or> k dvd n \<Longrightarrow> k dvd m * n" using dvd_mult dvd_mult2 by blast
setup {* add_backward_prfstep_cond @{thm prod_dvd_intro}
  [with_filt (canonical_split_filter @{const_name times} "m" "n")] *}

(* Definition of gcd. *)
setup {* add_forward_prfstep_cond @{thm gcd_dvd1_nat} [with_term "gcd ?a ?b"] *}

(* Coprimality. *)
setup {* add_backward_prfstep @{thm coprime_exp_nat} *}
setup {* add_backward1_prfstep @{thm coprime_dvd_mult_nat} *}
theorem coprime_dvd: "coprime (a::nat) b \<Longrightarrow> p dvd a \<Longrightarrow> (p > 1 \<longrightarrow> (\<not> p dvd b))" by (metis coprime_nat neq_iff)
setup {* add_forward_prfstep @{thm coprime_dvd} *}

(* Powers. *)
setup {* add_simp_rule @{thm power_0} *}
setup {* add_simp_rule_cond @{thm power_one} [with_cond "?n \<noteq> 0"] *}
setup {* add_simp_rule_cond @{thm power_one_right} [with_cond "?a \<noteq> 1"] *}
setup {* add_rewrite_rule_cond @{thm power_eq_if} (with_conds ["?p \<noteq> 1", "?m \<noteq> 0", "?m \<noteq> 1"]) *}

theorem power_0': "(1::nat) = a ^ 0" by simp
setup {* add_prfstep_two_stage ("one_is_power_zero",
  [WithGoal @{term_pat "\<exists> i. (1::nat) = ?a ^ i"},
   GetFact (@{term_pat "(1::nat) = ?a ^ 0"}, @{thm power_0'})],
  @{thm exists_resolve}) *}

theorem power_add_one: "(p::nat) ^ i * p = p ^ (i + 1)" by (metis Suc_eq_plus1 mult.commute power_Suc)
setup {* add_rewrite_rule_cond @{thm power_add_one} [with_filt (size1_filter "i")] *}

theorem power_dvd: "(p::nat)^n dvd a \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p dvd a" using dvd_power dvd_trans by blast
setup {* add_forward_prfstep @{thm power_dvd} *}

theorem power_eq_one: "(b::nat) ^ n = 1 \<Longrightarrow> b = 1 \<or> n = 0"
  by (metis One_nat_def Suc_lessI nat_zero_less_power_iff power_0 power_inject_exp)
setup {* add_forward_prfstep_cond @{thm power_eq_one} (with_conds ["?b \<noteq> 1", "?n \<noteq> 0"]) *}

(* Factorial. *)
theorem fact_ge_1_nat: "fact (n::nat) \<ge> (1::nat)" by simp
setup {* add_forward_prfstep_cond @{thm fact_ge_1_nat} [with_term "fact ?n"] *}
setup {* add_backward1_prfstep @{thm dvd_fact} *}

(* Induction. *)
theorem nat_induct': "P 0 \<Longrightarrow> (\<forall>n. P (n-1) \<longrightarrow> P n) \<Longrightarrow> P (n::nat)"
by (metis One_nat_def diff_Suc_Suc diff_zero nat_induct)
setup {*
  add_prfstep_induction @{thm nat_induct'} #>
  add_prfstep_strong_induction @{thm nat_less_induct}
*}

(* Extra proofsteps in ML. *)
ML_file "arith.ML"

end
