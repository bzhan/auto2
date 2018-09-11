(*
  File: Divides.thy
  Author: Bohua Zhan

  Basics of divisibility and prime numbers.
*)

theory Divides
  imports Nat
begin

section {* Divisibility *}
  
definition divides :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "divides(R,a,b) \<longleftrightarrow> (a \<in>. R \<and> b \<in>. R \<and> (\<exists>k\<in>.R. b = a *\<^sub>R k))"

lemma dividesI [resolve]:
  "is_group_raw(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> k \<in>. R \<Longrightarrow> divides(R, a, a *\<^sub>R k)" by auto2
lemma dividesD1 [forward]: "divides(R,a,b) \<Longrightarrow> a \<in>. R \<and> b \<in>. R" by auto2
lemma dividesD2 [backward]: "divides(R,a,b) \<Longrightarrow> \<exists>k\<in>.R. b = a *\<^sub>R k" by auto2
setup {* del_prfstep_thm @{thm divides_def} *}

lemma divides_id [resolve]: "is_semiring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> divides(R,a,a)"
@proof @have "a = a *\<^sub>R \<one>\<^sub>R" @qed

lemma divides_trans [forward]:
  "is_semiring(R) \<Longrightarrow> divides(R,a,b) \<Longrightarrow> divides(R,b,c) \<Longrightarrow> divides(R,a,c)"
@proof
  @obtain "k\<in>.R" where "b = a *\<^sub>R k"
  @obtain "l\<in>.R" where "c = b *\<^sub>R l"
  @have "c = (a *\<^sub>R k) *\<^sub>R l" @have "c = a *\<^sub>R (k *\<^sub>R l)"
@qed

lemma divides_one [resolve]:
  "is_semiring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> divides(R,\<one>\<^sub>R,a)"
@proof @have "a = \<one>\<^sub>R *\<^sub>R a" @qed
    
lemma divides_zero [resolve]:
  "is_semiring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> divides(R,a,\<zero>\<^sub>R)"
@proof @have "\<zero>\<^sub>R = a *\<^sub>R \<zero>\<^sub>R" @qed

section {* Divides on natural numbers *}

lemma nat_divides_cancel [forward]:
  "a \<in>. \<nat> \<Longrightarrow> b \<in>. \<nat> \<Longrightarrow> c \<in>. \<nat> \<Longrightarrow> c \<noteq> 0 \<Longrightarrow>
   divides(\<nat>, a *\<^sub>\<nat> c, b *\<^sub>\<nat> c) \<Longrightarrow> divides(\<nat>, a, b)"
@proof
  @obtain "k\<in>.\<nat>" where "b *\<^sub>\<nat> c = a *\<^sub>\<nat> c *\<^sub>\<nat> k"
  @have "a *\<^sub>\<nat> k *\<^sub>\<nat> c = b *\<^sub>\<nat> c"
@qed

lemma nat_le_prod [backward]:
  "a \<in>. \<nat> \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> a \<le>\<^sub>\<nat> a *\<^sub>\<nat> k"
@proof @have "k \<ge>\<^sub>\<nat> 1" @have "a = a *\<^sub>\<nat> 1" @qed
      
lemma nat_divides_le [forward]:
  "b \<noteq> 0 \<Longrightarrow> divides(\<nat>,a,b) \<Longrightarrow> 1 \<le>\<^sub>\<nat> a \<and> a \<le>\<^sub>\<nat> b"
@proof @obtain "k\<in>.\<nat>" where "b = a *\<^sub>\<nat> k" @qed

definition even :: "i \<Rightarrow> o" where [rewrite]:
  "even(x) \<longleftrightarrow> divides(\<nat>,2,x)"
  
definition odd :: "i \<Rightarrow> o" where [rewrite]:
  "odd(x) \<longleftrightarrow> (\<not>divides(\<nat>,2,x))"
  
section {* Quotient and Remainder *}

lemma quotient_remainder_theorem:
  "m >\<^sub>\<nat> 0 \<Longrightarrow> n \<in> nat \<Longrightarrow> \<exists>q\<in>nat. \<exists>r\<in>nat. n = m *\<^sub>\<nat> q +\<^sub>\<nat> r \<and> 0 \<le>\<^sub>\<nat> r \<and> r <\<^sub>\<nat> m"
@proof
  @strong_induct "n \<in> nat"
  @case "n <\<^sub>\<nat> m"
  @let "n' = n -\<^sub>\<nat> m"
  @have "n' <\<^sub>\<nat> n" @with @have "n' +\<^sub>\<nat> m <\<^sub>\<nat> n +\<^sub>\<nat> m" @end
  @obtain "q\<in>nat" "r\<in>nat" where "n' = m *\<^sub>\<nat> q +\<^sub>\<nat> r" "0 \<le>\<^sub>\<nat> r" "r <\<^sub>\<nat> m"
  @have "n = (m *\<^sub>\<nat> q +\<^sub>\<nat> r) +\<^sub>\<nat> m"
  @have "n = (m *\<^sub>\<nat> (q +\<^sub>\<nat> \<one>\<^sub>\<nat>)) +\<^sub>\<nat> r"
@qed

section {* Prime *}

definition prime :: "i \<Rightarrow> o" where [rewrite]:
  "prime(p) \<longleftrightarrow> (p >\<^sub>\<nat> 1 \<and> (\<forall>m. divides(\<nat>,m,p) \<longrightarrow> m = 1 \<or> m = p))"
  
lemma primeD1 [forward]: "prime(p) \<Longrightarrow> p >\<^sub>\<nat> 1" by auto2
lemma primeD2 [forward]: "prime(p) \<Longrightarrow> divides(\<nat>,m,p) \<Longrightarrow> m = 1 \<or> m = p" by auto2
setup {* del_prfstep_thm_eqforward @{thm prime_def} *}
  
lemma prime_odd_nat: "prime(p) \<Longrightarrow> p >\<^sub>\<nat> 2 \<Longrightarrow> odd(p)" by auto2

lemma exists_prime [resolve]: "\<exists>p. prime(p)"
@proof
  @have "prime(2)" @with @have "2 \<noteq> 0" @end
@qed

lemma prime_factor_nat: "n \<in> nat \<Longrightarrow> n \<noteq> 1 \<Longrightarrow> \<exists>p. divides(\<nat>,p,n) \<and> prime(p)"
@proof
  @strong_induct "n \<in> nat"
  @case "prime(n)" @with @have "divides(\<nat>,n,n)" @end
  @case "n = \<zero>\<^sub>\<nat>" @with
    @obtain q where "prime(q)"
    @have "divides(\<nat>,q,0)"
  @end
@qed

end
