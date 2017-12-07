(* Setup for discrete log *)

theory DiscreteLog_Thms
  imports "../Auto2_Main" "~~/src/HOL/Library/Discrete"
begin

section {* Average and standard results *}

fun avg :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "avg l r = (l + r) div 2"

lemma avg_eq [rewrite]:
  "l + r = 2 * k \<Longrightarrow> avg l r = k"
  "l + r = 2 * k + 1 \<Longrightarrow> avg l r = k" by auto

lemma avg_between_triv [backward]:
  "l \<le> r \<Longrightarrow> r \<ge> avg l r"
  "l \<le> r \<Longrightarrow> avg l r \<ge> l" by auto

lemma avg_between [backward]:
  "l + 1 < r \<Longrightarrow> r > avg l r"
  "l + 1 < r \<Longrightarrow> avg l r > l" by auto

lemma avg_diff [backward]:
  "l + 1 < r \<Longrightarrow> r - avg l r < r - l"
  "l + 1 < r \<Longrightarrow> avg l r - l < r - l" by auto

section {* Discrete log *}

abbreviation "dlog \<equiv> Discrete.log"

lemma dlog_double [rewrite]: "n > 0 \<Longrightarrow> dlog (2 * n) = dlog n + 1" by auto
setup {* add_backward_prfstep @{thm Discrete.log_le_iff} *}
lemma oddE' [resolve]: "odd (n::nat) \<Longrightarrow> \<exists>i. n = 2 * i + 1" using oddE by blast

lemma dlog_avg_diff_bound1 [backward]:
  "l + 1 < r \<Longrightarrow> dlog (avg l r - l) + 1 \<le> dlog (r - l)"
@proof
  @case "even (r - l)" @with
    @obtain i where "r - l = 2 * i"
    @have "i > 0"
    @have "r - l + l = 2 * i + l"
    @have "l + r = 2 * (i + l)"
    @have "avg l r = l + i"
    @have "avg l r - l = i"
  @end
  @case "odd (r - l)" @with
    @obtain i where "r - l = 2 * i + 1"
    @case "i = 0" @with @have "1 + l = l + 1" @end
    @have "r = 2 * i + 1 + l"
    @have "l + r = 2 * (l + i) + 1"
    @have "avg l r = l + i"
    @have "avg l r - l = i"
    @have "dlog (r - l) \<ge> dlog (2 * i)"
  @end
@qed

lemma dlog_avg_diff_bound2 [backward]:
  "l + 1 < r \<Longrightarrow> dlog (r - (avg l r + 1)) + 1 \<le> dlog (r - l)"
@proof
  @case "even (r - l)" @with
    @obtain i where "r - l = 2 * i"
    @have "i > 0"
    @have "r - l + l = 2 * i + l"
    @have "l + r = 2 * (l + i)"
    @have "avg l r = r - i" @with
      @have "l + i + i = r"
      @have "l + i = r - i"
    @end
    @have "r - avg l r = i"
  @end
  @case "odd (r - l)" @with
    @obtain i where "r - l = 2 * i + 1"
    @case "i = 0" @with @have "1 + l = l + 1" @end
    @have "r = 2 * i + 1 + l"
    @have "l + r = 2 * (l + i) + 1"
    @have "avg l r = r - i - 1" @with
      @have "l + i + i + 1 = r"
      @have "l + i = r - i - 1"
    @end
    @have "r - (avg l r + 1) = i"
    @have "dlog (r - l) \<ge> dlog (2 * i)"
  @end
@qed

section {* Second version of discrete log *}

definition dlog' :: "nat \<Rightarrow> nat" where [rewrite]:
  "dlog' n = dlog (n - 1) + 1"

lemma even_div_2 [rewrite]: "(2 * i) div 2 = (i::nat)" by auto
lemma odd_div_2 [rewrite]: "(2 * i + 1) div 2 = (i::nat)" by auto

lemma dlog_div_2 [backward]:
  "(n::nat) > 1 \<Longrightarrow> dlog n \<ge> dlog (n div 2) + 1"
  by (metis One_nat_def Suc_eq_plus1 Suc_leI less_or_eq_imp_le log_rec numerals(2))

lemma dlog'_properties1 [backward]:
  "x > 2 \<Longrightarrow> dlog' x \<ge> dlog' (x div 2) + 1"
@proof
  @case "even x" @with
    @obtain i where "x = 2 * i"
    @have "x div 2 = i"
    @have "dlog' x = dlog (x - 1) + 1"
    @have "dlog' (x div 2) = dlog (i - 1) + 1"
    @have "2 * i - 1 = 2 * (i - 1) + 1"
    @have "i - 1 = (2 * i - 1) div 2"
    @have "dlog (2 * i - 1) \<ge> dlog (i - 1) + 1"
  @end
  @case "odd x" @with
    @obtain i where "x = 2 * i + 1"
    @have "x div 2 = i"
    @have "dlog' x = dlog (x - 1) + 1"
    @have "dlog' (x div 2) = dlog (i - 1) + 1"
    @have "dlog (2 * i) \<ge> dlog (i - 1) + 1"
  @end
@qed

lemma dlog_ge_one [backward]:
  "x > 2 \<Longrightarrow> dlog' x \<ge> 2"
  by (metis Nat.le_diff_conv2 add_leD2 dlog'_def dlog'_properties1 one_add_one)

lemma dlog'_properties2 [backward]:
  "x > 2 \<Longrightarrow> dlog' x \<ge> dlog' (x - x div 2) + 1"
@proof
  @case "even x" @with
    @obtain i where "x = 2 * i"
    @have "x div 2 = i"
    @have "x - x div 2 = i"
    @have "dlog' x = dlog (x - 1) + 1"
    @have "dlog' (x - x div 2) = dlog (i - 1) + 1"
    @have "2 * i - 1 = 2 * (i - 1) + 1"
    @have "i - 1 = (2 * i - 1) div 2"
  @end
  @case "odd x" @with
    @obtain i where "x = 2 * i + 1"
    @have "x div 2 = i"
    @have "x - x div 2 = i + 1"
    @have "dlog' x = dlog (x - 1) + 1"
    @have "dlog' (x - x div 2) = dlog' (i + 1)"
    @have "dlog' (x - x div 2) = dlog i + 1"
  @end
@qed

end
