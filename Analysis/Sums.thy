theory Sums
imports Rat_Thms
begin

(* Use standard induction in this theory. *)
setup {* add_prfstep_var_induction @{thm nat_induct} *}

fun interval_sum :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::comm_ring) \<Rightarrow> 'a" where
  "interval_sum 0 f = 0"
| "interval_sum (Suc n) f = interval_sum n f + f (Suc n)"
setup {* fold add_rewrite_rule @{thms interval_sum.simps} *}

theorem sum_on_plus [rewrite]: fixes f :: "nat \<Rightarrow> rat" shows
  "interval_sum n (\<lambda>k. f k + g k) = interval_sum n f + interval_sum n g"
  by auto2

theorem sum_on_const_times [rewrite]: fixes f :: "nat \<Rightarrow> rat" shows
  "interval_sum n (\<lambda>k. c * f k) = c * interval_sum n f"
  by auto2

theorem sum_power1 [rewrite]:
  "interval_sum n (\<lambda>k. rat_of_nat k) = (of_nat n) * (of_nat n + 1) / 2"
  by auto2

theorem sum_power2 [rewrite]:
  "interval_sum n (\<lambda>k. (rat_of_nat k)\<^sup>2) = (of_nat n) * (of_nat n + 1) * (2 * of_nat n + 1) / 6"
  by auto2

theorem sum_power3 [rewrite]:
  "interval_sum n (\<lambda>k. (rat_of_nat k)^3) = (of_nat n)\<^sup>2 * (of_nat n + 1)\<^sup>2 / 4"
  by auto2

theorem sum_ex1:
  "interval_sum n (\<lambda>k. rat_of_nat k + (of_nat k)\<^sup>2) = (of_nat n) ^ 3 / 3 + (of_nat n)\<^sup>2 + 2 * (of_nat n) / 3"
  by auto2

theorem sum_ex2:
  "interval_sum n (\<lambda>k. 2 * rat_of_nat k) = (of_nat n) * (of_nat n + 1)"
  by auto2

end
