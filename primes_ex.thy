theory primes_ex
imports auto2
begin

definition prime :: "nat \<Rightarrow> bool"
  where "prime p = (1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p))"

setup {* add_rewrite_rule ([WithTerm @{term_pat "prime ?p"}], @{thm prime_def}) *}

(* Exists a prime p. *)
theorem exists_prime: "\<exists>p. prime p"
  by (metis One_nat_def antisym_conv dvd_def gcd_dvd2_nat gcd_nat.absorb2
            less_Suc_eq nat_dvd_not_less not_less one_le_mult_iff prime_def)
setup {*
  add_gen_prfstep ("exists_prime",
    [WithGoal @{term_pat "EX p. prime p"},
     GetResolve @{thm exists_prime}])
*}

lemma prime_odd_nat: "prime (p::nat) \<Longrightarrow> p > 2 \<Longrightarrow> odd p"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_imp_coprime_nat: "prime p \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n"
  apply ( tactic {* auto2_tac @{context} *} ) done

setup {*
  add_gen_prfstep ("prime_imp_coprime_nat",
    [WithFact @{term_pat "prime (?p::nat)"},
     WithGoal @{term_pat "coprime (?p::nat) ?n"},
     GetGoal (@{term_pat "\<not> (?p::nat) dvd ?n"}, @{thm prime_imp_coprime_nat})])
*}

lemma prime_dvd_mult_nat: "prime p \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  apply ( tactic {* auto2_tac @{context} *} ) done

setup {*
  add_gen_prfstep ("prime_dvd_mult_nat",
    [WithFact @{term_pat "prime (?p::nat)"},
     WithFact @{term_pat "(?p::nat) dvd ?m * ?n"},
     GetFact (@{term_pat "(?p::nat) dvd ?m \<or> ?p dvd ?n"}, @{thm prime_dvd_mult_nat}),
     Filter (canonical_split_filter @{const_name times} "m" "n"),
     Filter (term_neq_filter @{const_name times} "p" "m"),
     Filter (term_neq_filter @{const_name times} "p" "n")])
*}

theorem prime_dvd_intro: "prime p \<Longrightarrow> p * q = m * n \<Longrightarrow> p dvd m \<or> p dvd n"
by (metis dvd_triv_left prime_dvd_mult_nat)
setup {*
  add_gen_prfstep ("prime_dvd_intro",
    [WithFact @{term_pat "prime (?p::nat)"},
     WithFact @{term_pat "?p * ?q = (?m::nat) * ?n"},
     GetFact (@{term_pat "(?p::nat) dvd ?m \<or> ?p dvd ?n"}, @{thm prime_dvd_intro}),
     Filter (canonical_split_filter @{const_name times} "m" "n"),
     Filter (term_neq_filter @{const_name times} "p" "m"),
     Filter (term_neq_filter @{const_name times} "p" "n")])
*}

lemma prime_dvd_mult_eq_nat: "prime p \<Longrightarrow>
    p dvd m * n = (p dvd m \<or> p dvd n)"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma not_prime_eq_prod_nat: "(n::nat) > 1 \<Longrightarrow> ~ prime n \<Longrightarrow>
    EX m k. n = m * k & 1 < m & m < n & 1 < k & k < n"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_dvd_power_nat: "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p dvd x"
  apply ( tactic {* auto2_tac @{context} *} ) done

setup {*
  add_gen_prfstep ("prime_dvd_power_nat",
    [WithFact @{term_pat "prime (?p::nat)"},
     WithFact @{term_pat "(?p::nat) dvd ?x^?n"},
     GetFact (@{term_pat "(?p::nat) dvd ?x"}, @{thm prime_dvd_power_nat}),
     Filter (neq_filter "p" "x")])
*}

lemma prime_dvd_power_nat_iff: "prime p \<Longrightarrow> n > 0 \<Longrightarrow>
    p dvd x^n \<longleftrightarrow> p dvd x"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_nat_code: "prime p = (1 < p \<and> (\<forall>x. 1 < x \<and> x < p \<longrightarrow> \<not> x dvd p))"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_factor_nat: "n \<noteq> (1::nat) \<Longrightarrow> \<exists> p. p dvd n \<and> prime p"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_divprod_pow_nat: "prime p \<Longrightarrow> coprime a b \<Longrightarrow> p^n dvd a * b \<Longrightarrow>
                              p^n dvd a \<or> p^n dvd b"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_product: "prime ((p::nat) * q) \<Longrightarrow> p = 1 \<or> q = 1"
  apply ( tactic {* auto2_tac @{context} *} ) done

setup {*
  add_gen_prfstep ("prime_product",
    [WithFact @{term_pat "prime ((?p::nat) * ?q)"},
     GetFact (@{term_pat "(?p::nat) = 1 | (?q::nat) = 1"}, @{thm prime_product}),
     Filter (canonical_split_filter @{const_name times} "p" "q")])
*}

lemma prime_exp: "prime ((p::nat) ^ n) \<longleftrightarrow> n = 1 \<and> prime p"
  apply ( tactic {* auto2_tac @{context} *} ) done

lemma prime_power_mult: "prime p \<Longrightarrow> x * y = p ^ k \<Longrightarrow>
                         \<exists>i j. x = p ^ i \<and> y = p ^ j"
  apply ( tactic {* auto2_tac @{context} *} ) done

end