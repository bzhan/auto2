(* Elementary number theory of primes, up to the proof of infinitude
   of primes and the unique factorization theorem. Follows theories
   Primes and UniqueFactorization in HOL/Number_Theory. *)

theory Primes_Ex
imports Auto2_Main
begin

section {* Definition and basic properties of primes *}

definition prime :: "nat \<Rightarrow> bool" where [rewrite]:
  "prime p = (1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p))"

lemma primeD1 [forward]: "prime p \<Longrightarrow> 1 < p" by auto2
lemma primeD2: "prime p \<Longrightarrow> m dvd p \<Longrightarrow> m = 1 \<or> m = p" by auto2
setup {* add_forward_prfstep_cond @{thm primeD2} [with_cond "?m \<noteq> 1", with_cond "?m \<noteq> ?p"] *}
setup {* del_prfstep_thm_eqforward @{thm prime_def} *}

(* Exists a prime p. *)
theorem exists_prime [resolve]: "\<exists>p. prime p"
@proof @have "prime 2" @qed

lemma prime_odd_nat: "prime p \<Longrightarrow> p > 2 \<Longrightarrow> odd p" by auto2

lemma prime_imp_coprime_nat [backward2]: "prime p \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n" by auto2

lemma prime_dvd_mult_nat: "prime p \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" by auto2
setup {* add_forward_prfstep_cond @{thm prime_dvd_mult_nat}
  (with_conds ["?m \<noteq> ?p", "?n \<noteq> ?p", "?m \<noteq> ?p * ?m'", "?n \<noteq> ?p * ?n'"]) *}

theorem prime_dvd_intro: "prime p \<Longrightarrow> p * q = m * n \<Longrightarrow> p dvd m \<or> p dvd n"
@proof @have "p dvd m * n" @qed
setup {* add_forward_prfstep_cond @{thm prime_dvd_intro}
  (with_conds ["?m \<noteq> ?p", "?n \<noteq> ?p", "?m \<noteq> ?p * ?m'", "?n \<noteq> ?p * ?n'"]) *}

lemma prime_dvd_mult_eq_nat: "prime p \<Longrightarrow> p dvd m * n = (p dvd m \<or> p dvd n)" by auto2

lemma not_prime_eq_prod_nat [backward1]: "n > 1 \<Longrightarrow> \<not> prime n \<Longrightarrow>
    \<exists>m k. n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n"
@proof
  @obtain m where "m dvd n \<and> m \<noteq> 1 \<and> m \<noteq> n"
  @obtain k where "n = m * k" @have "m \<le> m * k" @have "k \<le> m * k"
@qed

lemma prime_dvd_power_nat: "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p dvd x" by auto2
setup {* add_forward_prfstep_cond @{thm prime_dvd_power_nat} [with_cond "?p \<noteq> ?x"] *}

lemma prime_dvd_power_nat_iff: "prime p \<Longrightarrow> n > 0 \<Longrightarrow> p dvd x^n \<longleftrightarrow> p dvd x" by auto2

lemma prime_nat_code: "prime p = (1 < p \<and> (\<forall>x. 1 < x \<and> x < p \<longrightarrow> \<not> x dvd p))" by auto2

lemma prime_factor_nat [backward]: "n \<noteq> 1 \<Longrightarrow> \<exists>p. p dvd n \<and> prime p"
@proof
  @strong_induct n
  @case "prime n" @then @case "n = 0" @then
  @obtain k where "k \<noteq> 1" "k \<noteq> n" "k dvd n"
  @apply_induct_hyp k
@qed

lemma prime_divprod_pow_nat:
  "prime p \<Longrightarrow> coprime a b \<Longrightarrow> p^n dvd a * b \<Longrightarrow> p^n dvd a \<or> p^n dvd b" by auto2

lemma prime_product [forward]: "prime (p * q) \<Longrightarrow> p = 1 \<or> q = 1"
@proof @have "p dvd q * p" @qed

lemma prime_exp: "prime (p ^ n) \<longleftrightarrow> n = 1 \<and> prime p" by auto2

lemma prime_power_mult: "prime p \<Longrightarrow> x * y = p ^ k \<Longrightarrow> \<exists>i j. x = p ^ i \<and> y = p ^ j"
@proof
  @induct k arbitrary x y @with
    @subgoal "k = Suc k'"
      @case "p dvd x" @with
        @obtain x' where "x = p * x'" @then @have "x * y = p * (x' * y)" @then
        @obtain i j where "x' = p ^ i" "y = p ^ j" @then @have "x = p ^ Suc i" @end
      @case "p dvd y" @with
        @obtain y' where "y = p * y'" @then @have "x * y = p * (x * y')" @then
        @obtain i j where "x = p ^ i" "y' = p ^ j" @then @have "y = p ^ Suc j" @end
    @endgoal
  @end
@qed

section {* Infinitude of primes *}

theorem bigger_prime [resolve]: "\<exists>p. prime p \<and> n < p"
@proof
  @obtain p where "prime p" "p dvd fact n + 1"
  @case "n \<ge> p" @with @have "(p::nat) dvd fact n" @end
@qed

theorem primes_infinite: "\<not> finite {p. prime p}"
@proof
  @obtain b where "prime b" "Max {p. prime p} < b"
@qed

section {* Existence and uniqueness of prime factorization *}

theorem factorization_exists: "n > 0 \<Longrightarrow> \<exists>M. (\<forall>p\<in>#M. prime p) \<and> n = (\<Prod>i\<in>#M. i)"
@proof
  @strong_induct n
  @case "n = 1" @with @have "n = (\<Prod>i\<in># {#}. i)" @end
  @case "prime n" @with @have "n = (\<Prod>i\<in># {#n#}. i)" @end
  @obtain m k where "n = m * k" "1 < m" "m < n" "1 < k" "k < n"
  @apply_induct_hyp m
  @obtain M where "(\<forall>p\<in>#M. prime p)" "m = (\<Prod>i\<in>#M. i)"
  @apply_induct_hyp k
  @obtain K where "(\<forall>p\<in>#K. prime p)" "k = (\<Prod>i\<in>#K. i)"
  @have "n = (\<Prod>i\<in>#(M+K). i)"
@qed

theorem prime_dvd_multiset [backward1]: "prime p \<Longrightarrow> p dvd (\<Prod>i\<in>#M. i) \<Longrightarrow> \<exists>n. n\<in>#M \<and> p dvd n"
@proof
  @strong_induct M
  @case "M = {#}" @then
  @obtain M' m where "M = M' + {#m#}"
  @contradiction @apply_induct_hyp M'
@qed
  
theorem factorization_unique_aux:
  "\<forall>p\<in>#M. prime p \<Longrightarrow> \<forall>p\<in>#N. prime p \<Longrightarrow> (\<Prod>i\<in>#M. i) dvd (\<Prod>i\<in>#N. i) \<Longrightarrow> M \<subseteq># N"
@proof
  @strong_induct M arbitrary N
  @case "M = {#}" @then
  @obtain M' m where "M = M' + {#m#}" @then
  @have "m dvd (\<Prod>i\<in>#M. i)" @then
  @obtain n where "n \<in># N" "m dvd n" @then
  @obtain N' where "N = N' + {#n#}" @then
  @have "m = n" @then
  @have "(\<Prod>i\<in>#M'. i) dvd (\<Prod>i\<in>#N'. i)"
  @apply_induct_hyp M' N'
@qed
setup {* add_forward_prfstep_cond @{thm factorization_unique_aux} [with_cond "?M \<noteq> ?N"] *}

theorem factorization_unique:
  "\<forall>p\<in>#M. prime p \<Longrightarrow> \<forall>p\<in>#N. prime p \<Longrightarrow> (\<Prod>i\<in>#M. i) = (\<Prod>i\<in>#N. i) \<Longrightarrow> M = N"
@proof @have "M \<subseteq># N" @qed
setup {* del_prfstep_thm @{thm factorization_unique_aux} *}

end
