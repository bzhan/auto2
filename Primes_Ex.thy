(* Elementary number theory of primes, up to the proof of infinitude
   of primes and the unique factorization theorem. Follows theories
   Primes and UniqueFactorization in HOL/Number_Theory. *)

theory Primes_Ex
imports Auto2
begin

section {* Definition and basic properties of primes *}

definition prime :: "nat \<Rightarrow> bool"
  where "prime p = (1 < p \<and> (\<forall>m. m dvd p \<longrightarrow> m = 1 \<or> m = p))"
setup {* add_rewrite_rule @{thm prime_def} *}

(* Exists a prime p. *)
theorem exists_prime [resolve]: "\<exists>p. prime p"
  by (tactic {* auto2s_tac @{context} (OBTAIN "prime 2") *})

lemma prime_odd_nat: "prime p \<Longrightarrow> p > 2 \<Longrightarrow> odd p" by auto2

lemma prime_imp_coprime_nat [backward2]: "prime p \<Longrightarrow> \<not> p dvd n \<Longrightarrow> coprime p n" by auto2

lemma prime_dvd_mult_nat: "prime p \<Longrightarrow> p dvd m * n \<Longrightarrow> p dvd m \<or> p dvd n" by auto2
setup {* add_forward_prfstep_cond @{thm prime_dvd_mult_nat}
  (with_conds ["?m \<noteq> ?p", "?n \<noteq> ?p", "?m \<noteq> ?p * ?m'", "?n \<noteq> ?p * ?n'"]) *}

theorem prime_dvd_intro: "prime p \<Longrightarrow> p * q = m * n \<Longrightarrow> p dvd m \<or> p dvd n"
  by (tactic {* auto2s_tac @{context} (OBTAIN "p dvd m * n") *})
setup {* add_forward_prfstep_cond @{thm prime_dvd_intro}
  (with_conds ["?m \<noteq> ?p", "?n \<noteq> ?p", "?m \<noteq> ?p * ?m'", "?n \<noteq> ?p * ?n'"]) *}

lemma prime_dvd_mult_eq_nat: "prime p \<Longrightarrow> p dvd m * n = (p dvd m \<or> p dvd n)" by auto2

lemma not_prime_eq_prod_nat [backward1]: "n > 1 \<Longrightarrow> \<not> prime n \<Longrightarrow>
    \<exists>m k. n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n" by auto2

lemma prime_dvd_power_nat: "prime p \<Longrightarrow> p dvd x^n \<Longrightarrow> p dvd x" by auto2
setup {* add_forward_prfstep_cond @{thm prime_dvd_power_nat} [with_cond "?p \<noteq> ?x"] *}

lemma prime_dvd_power_nat_iff: "prime p \<Longrightarrow> n > 0 \<Longrightarrow> p dvd x^n \<longleftrightarrow> p dvd x" by auto2

lemma prime_nat_code: "prime p = (1 < p \<and> (\<forall>x. 1 < x \<and> x < p \<longrightarrow> \<not> x dvd p))" by auto2

lemma prime_factor_nat [backward]: "n \<noteq> 1 \<Longrightarrow> \<exists>p. p dvd n \<and> prime p"
  by (tactic {* auto2s_tac @{context} (STRONG_INDUCT ("n", [])) *})

lemma prime_divprod_pow_nat:
  "prime p \<Longrightarrow> coprime a b \<Longrightarrow> p^n dvd a * b \<Longrightarrow> p^n dvd a \<or> p^n dvd b" by auto2

lemma prime_product: "prime (p * q) \<Longrightarrow> p = 1 \<or> q = 1"
  by (tactic {* auto2s_tac @{context} (OBTAIN "p dvd p * q") *})
setup {* add_forward_prfstep @{thm prime_product} *}

lemma prime_exp: "prime (p ^ n) \<longleftrightarrow> n = 1 \<and> prime p" by auto2

lemma prime_power_mult: "prime p \<Longrightarrow> x * y = p ^ k \<Longrightarrow> \<exists>i j. x = p ^ i \<and> y = p ^ j"
  by (tactic {* auto2s_tac @{context} (
    CASE "k = 0" THEN INDUCT ("k", Arbitraries ["x", "y"])) *})

section {* Infinitude of primes *}

theorem bigger_prime [resolve]: "\<exists>p. prime p \<and> n < p"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "p, prime p \<and> p dvd fact n + 1" THEN
    CASE "p \<le> n" WITH OBTAIN "p dvd fact n") *})

theorem primes_infinite: "\<not> finite {p. prime p}"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "b, prime b \<and> Max {p. prime p} < b") *})

section {* Existence and uniqueness of prime factorization *}

theorem factorization_exists: "n > 0 \<Longrightarrow> \<exists>M. (\<forall>p\<in>set_mset M. prime p) \<and> n = (\<Prod>i\<in>#M. i)"
  by (tactic {* auto2s_tac @{context} (
    STRONG_INDUCT ("n", []) THEN
    CASE "n = 1" WITH OBTAIN "n = (\<Prod>i\<in># {#}. i)" THEN
    CASE "prime n" WITH OBTAIN "n = (\<Prod>i\<in># {#n#}. i)" THEN
    CHOOSES ["m, k, n = m * k \<and> 1 < m \<and> m < n \<and> 1 < k \<and> k < n",
             "M, (\<forall>p\<in>set_mset M. prime p) \<and> m = (\<Prod>i\<in>#M. i)",
             "K, (\<forall>p\<in>set_mset K. prime p) \<and> k = (\<Prod>i\<in>#K. i)"] THEN
    OBTAIN "n = (\<Prod>i\<in>#(M+K). i)") *})

theorem prime_dvd_multiset [backward1]: "prime p \<Longrightarrow> p dvd (\<Prod>i\<in>#M. i) \<Longrightarrow> \<exists>n. n\<in>#M \<and> p dvd n"
  by (tactic {* auto2s_tac @{context} (
    CASE "M = {#}" THEN
    CHOOSE "M', m, M = M' + {#m#}" THEN
    STRONG_INDUCT ("M", [ApplyOn "M'"])) *})

theorem factorization_unique_aux:
  "\<forall>p\<in>set_mset M. prime p \<Longrightarrow> \<forall>p\<in>set_mset N. prime p \<Longrightarrow> (\<Prod>i\<in>#M. i) dvd (\<Prod>i\<in>#N. i) \<Longrightarrow> M \<subseteq># N"
  by (tactic {* auto2s_tac @{context} (
    CASE "M = {#}" THEN
    CHOOSE "M', m, M = M' + {#m#}" THEN
    OBTAIN "m dvd (\<Prod>i\<in>#N. i)" THEN
    CHOOSES ["n, n\<in>#N \<and> m dvd n",
             "N', N = N' + {#n#}"] THEN
    OBTAIN "m = n" THEN
    OBTAIN "(\<Prod>i\<in>#M'. i) dvd (\<Prod>i\<in>#N'. i)" THEN
    STRONG_INDUCT ("M", [Arbitrary "N", ApplyOn "M'"])) *})

setup {* add_forward_prfstep_cond @{thm factorization_unique_aux} [with_cond "?M \<noteq> ?N"] *}
theorem factorization_unique:
  "\<forall>p\<in>set_mset M. prime p \<Longrightarrow> \<forall>p\<in>set_mset N. prime p \<Longrightarrow> (\<Prod>i\<in>#M. i) = (\<Prod>i\<in>#N. i) \<Longrightarrow> M = N"
  by (tactic {* auto2s_tac @{context} (OBTAIN "M \<subseteq># N") *})
setup {* del_prfstep_thm @{thm factorization_unique_aux} *}

end
