theory Arith_Thms
imports Main "~~/src/HOL/GCD"
begin

theorem n_minus_1_eq_0: "(n::nat) \<noteq> 0 \<Longrightarrow> n - 1 = 0 \<Longrightarrow> n = 1" by simp
theorem le_contra: "\<not> (n::nat) < n" by simp
theorem ge_and_le: "(m::nat) \<ge> n \<Longrightarrow> m \<le> n \<Longrightarrow> m = n" by simp
theorem le_and_ne: "(m::nat) \<le> n \<Longrightarrow> m \<noteq> n \<Longrightarrow> m < n" by simp
theorem lt_one: "(m::nat) < 1 \<Longrightarrow> m = 0" by simp
theorem gt_zero: "(m::nat) > C \<Longrightarrow> m > 0" by simp
theorem prod_ineqs1: "(m::nat) * k > 0 \<Longrightarrow> 1 \<le> m" by simp
theorem prod_ineqs2: "(m::nat) * k > 0 \<Longrightarrow> m \<le> m * k" by simp
theorem prod_ineqs3: "(m::nat) * k > 0 \<Longrightarrow> 1 \<le> k" by simp
theorem prod_ineqs4: "(m::nat) * k > 0 \<Longrightarrow> k \<le> m * k" by simp
theorem mult_n1n: "(n::nat) = m * n \<Longrightarrow> n > 0 \<Longrightarrow> m = 1" by simp
theorem prod_dvd_intro: "(k::nat) dvd m \<or> k dvd n \<Longrightarrow> k dvd m * n" using dvd_mult dvd_mult2 by blast
theorem n_dvd_one: "(n::nat) dvd 1 \<Longrightarrow> n = 1" by simp
theorem prod_is_one: "(x::nat) * y = 1 \<Longrightarrow> x = 1" by simp
theorem one_dvd_any: "1 dvd (n::nat)" by simp
theorem dvd_transitive: "(m::nat) dvd n \<Longrightarrow> n dvd p \<Longrightarrow> m dvd p" using dvd_trans by blast
theorem dvd_transitive': "(m::nat) dvd n \<Longrightarrow> n dvd m \<Longrightarrow> m = n" by (simp add: dvd.eq_iff)
theorem n_dvd_n: "(n::nat) dvd n" by simp
theorem dvd_prod1: "(a::nat) dvd a * b" by simp
theorem dvd_prod2: "(b::nat) dvd a * b" by simp
theorem power_0': "(1::nat) = a ^ 0" by simp
theorem prod_cancel: "(a::nat) > 0 \<Longrightarrow> a * b = a * c \<Longrightarrow> b = c" by simp
theorem power_add_one: "(p::nat) ^ i * p = p ^ (i + 1)" by (metis Suc_eq_plus1 mult.commute power_Suc)
theorem power_dvd: "(p::nat)^n dvd a \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p dvd a" using dvd_power dvd_trans by blast
theorem coprime_dvd: "coprime (a::nat) b \<Longrightarrow> p dvd a \<Longrightarrow> (p > 1 \<longrightarrow> (\<not> p dvd b))" by (metis coprime_nat neq_iff)
theorem power_eq_one: "(b::nat) ^ n = 1 \<Longrightarrow> b = 1 \<or> n = 0"
  by (metis One_nat_def Suc_lessI nat_zero_less_power_iff power_0 power_inject_exp)

theorem any_n_dvd_0: "\<not> (\<exists> k. k dvd (0::nat) \<and> P k) \<Longrightarrow> \<not> (\<exists> k. P k)" by simp

(* Induction. *)
thm nat.induct
theorem nat_shift: "(\<And>n::nat. P (n-1) \<Longrightarrow> P n) \<Longrightarrow> P n \<Longrightarrow> P (Suc n)" by simp
theorem nat_zero: "(\<And>n::nat. n = 0 \<Longrightarrow> P n) \<Longrightarrow> P 0" by blast

thm nat_less_induct

end
