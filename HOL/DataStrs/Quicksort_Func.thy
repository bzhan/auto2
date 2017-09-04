theory Quicksort_Func
imports Arrays_Ex
begin

section {* Outer remains *}
  
definition outer_remains :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "outer_remains xs xs' l r \<longleftrightarrow> (\<forall>i. i < l \<or> r < i \<longrightarrow> xs ! i = xs' ! i)"

lemma outer_remainsD1: "outer_remains xs xs' l r \<Longrightarrow> i < l \<Longrightarrow> xs ! i = xs' ! i" by auto2
setup {* add_forward_prfstep_cond @{thm outer_remainsD1} [with_term "?xs' ! ?i"] *}

lemma outer_remainsD2: "outer_remains xs xs' l r \<Longrightarrow> r < i \<Longrightarrow> xs ! i = xs' ! i" by auto2
setup {* add_forward_prfstep_cond @{thm outer_remainsD2} [with_term "?xs' ! ?i"] *}
setup {* del_prfstep_thm_eqforward @{thm outer_remains_def} *}

section {* part1 function *}  

function part1 :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a list)" where
  "part1 xs l r a = (
     if r \<le> l then (r, xs)
     else if xs ! l \<le> a then part1 xs (l + 1) r a
     else part1 (list_swap xs l r) l (r - 1) a)"
  by auto
  termination by (relation "measure (\<lambda>(_,l,r,_). r - l)") auto
setup {* add_rewrite_rule_cond @{thm part1.simps} [with_filt (size1_filter "l"), with_filt (size1_filter "r")] *}
setup {* register_wellform_data ("part1 xs l r a", ["r < length xs"]) *}
setup {* add_prfstep_check_req ("part1 xs l r a", "r < length xs") *}

lemma part1_basic: "r < length xs \<Longrightarrow> xs' = snd (part1 xs l r a) \<Longrightarrow>
  length xs' = length xs \<and> outer_remains xs xs' l r \<and> mset xs' = mset xs"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @case "r \<le> l"
  @case "xs ! l \<le> a" @with @apply_induct_hyp "d - 1" "l + 1" r xs @end
  @apply_induct_hyp "d - 1" l "r - 1" "list_swap xs l r"
@qed
setup {* add_forward_prfstep_cond @{thm part1_basic} [with_term "?xs'"] *}

lemma part1_returns_index_in_bounds:
  "r < length xs \<Longrightarrow> rs = fst (part1 xs l r a) \<Longrightarrow> l \<le> r \<Longrightarrow> l \<le> rs \<and> rs \<le> r"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @case "r \<le> l"
  @case "xs ! l \<le> a" @with @apply_induct_hyp "d - 1" "l + 1" r xs @end
  @apply_induct_hyp "d - 1" l "r - 1" "list_swap xs l r"
@qed
setup {* add_forward_prfstep_cond @{thm part1_returns_index_in_bounds} [with_term "?rs"] *}

lemma part1_partitions1:
  "r < length xs \<Longrightarrow> rs = fst (part1 xs l r a) \<Longrightarrow> xs' = snd (part1 xs l r a) \<Longrightarrow>
   l \<le> i \<Longrightarrow> i < rs \<Longrightarrow> xs' ! i \<le> a"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs i
  @case "r \<le> l"
  @case "xs ! l \<le> a" @with
    @case "l + 1 \<le> i" @with @apply_induct_hyp "d - 1" "l + 1" r xs i @end
  @end
  @apply_induct_hyp "d - 1" l "r - 1" "list_swap xs l r"
@qed
setup {* add_forward_prfstep_cond @{thm part1_partitions1} [with_term "?xs' ! ?i"] *}

lemma part1_partitions2:
  "r < length xs \<Longrightarrow> rs = fst (part1 xs l r a) \<Longrightarrow> xs' = snd (part1 xs l r a) \<Longrightarrow>
   rs < i \<Longrightarrow> i \<le> r \<Longrightarrow> xs' ! i \<ge> a"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs i
  @case "r \<le> l"
  @case "xs ! l \<le> a" @with @apply_induct_hyp "d - 1" "l + 1" r xs @end
  @case "i \<le> r - 1" @with @apply_induct_hyp "d - 1" l "r - 1" "list_swap xs l r" i @end
@qed
setup {* add_forward_prfstep_cond @{thm part1_partitions2} [with_term "?xs' ! ?i"] *}

setup {* del_prfstep_thm @{thm part1.simps} *}

section {* Paritition function *}

definition partition :: "('a::linorder list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a list)" where [rewrite]:
  "partition xs l r = (
    let p = xs ! r;
      m = fst (part1 xs l (r - 1) p);
      xs' = snd (part1 xs l (r - 1) p);
      m' = if xs' ! m \<le> p then m + 1 else m
    in
      (m', list_swap xs' m' r))"
setup {* register_wellform_data ("partition xs l r", ["l < r", "r < length xs"]) *}

lemma partition_return_in_bounds:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> rs = fst (partition xs l r) \<Longrightarrow> l \<le> rs \<and> rs \<le> r" by auto2
setup {* add_forward_prfstep_cond @{thm partition_return_in_bounds} [with_term "?rs"] *}

lemma partition_basic:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> xs' = snd (partition xs l r) \<Longrightarrow>
   length xs' = length xs \<and> outer_remains xs xs' l r \<and> mset xs' = mset xs" by auto2
setup {* add_forward_prfstep_cond @{thm partition_basic} [with_term "?xs'"] *}

lemma partition_partitions1':
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> rs = fst (partition xs l r) \<Longrightarrow> xs' = snd (partition xs l r) \<Longrightarrow>
   i \<ge> l \<Longrightarrow> i < rs \<Longrightarrow> xs' ! i \<le> xs' ! rs"
@proof
  @let "p = xs ! r"
  @let "xs'' = snd (part1 xs l (r - 1) p)"
  @have "xs'' ! r = p"
  @have (@rule) "\<forall>j. j \<ge> l \<longrightarrow> j < rs \<longrightarrow> xs'' ! j \<le> p"
@qed
setup {* add_forward_prfstep_cond @{thm partition_partitions1'} [with_term "?xs' ! ?i"] *}
  
lemma partition_partitions1 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> rs = fst (partition xs l r) \<Longrightarrow> xs' = snd (partition xs l r) \<Longrightarrow>
   x \<in> set (sublist l rs xs') \<Longrightarrow> x \<le> xs' ! rs"
@proof @obtain i where "i \<ge> l" "i < rs" "x = xs' ! i" @qed
setup {* del_prfstep_thm @{thm partition_partitions1'} *}

lemma partition_partitions2':
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> rs = fst (partition xs l r) \<Longrightarrow> xs' = snd (partition xs l r) \<Longrightarrow>
   i \<ge> rs + 1 \<Longrightarrow> i \<le> r \<Longrightarrow> xs' ! i \<ge> xs' ! rs"
@proof
  @let "p = xs ! r"
  @let "m = fst (part1 xs l (r - 1) p)"
  @let "xs'' = snd (part1 xs l (r - 1) p)"
  @have "xs'' ! r = p"
  @have (@rule) "\<forall>j. rs \<le> j \<longrightarrow> j < r - 1 \<longrightarrow> xs'' ! j \<ge> p" @with @case "m = j" @end
@qed
setup {* add_forward_prfstep_cond @{thm partition_partitions2'} [with_term "?xs' ! ?i"] *}
  
lemma partition_partitions2 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> rs = fst (partition xs l r) \<Longrightarrow> xs' = snd (partition xs l r) \<Longrightarrow>
   x \<in> set (sublist (rs + 1) (r + 1) xs') \<Longrightarrow> x \<ge> xs' ! rs"
@proof @obtain i where "i \<ge> rs + 1" "i < r + 1" "x = xs' ! i" @qed
setup {* del_prfstep_thm @{thm partition_partitions2'} *}
setup {* del_prfstep_thm @{thm partition_def} *}

function quicksort :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "quicksort xs l r = (
    if l < r \<and> r < length xs then
      let p = fst (partition xs l r);
        xs1 = snd (partition xs l r);
        xs2 = quicksort xs1 l (p - 1)
      in
        quicksort xs2 (p + 1) r
    else xs)"
  by auto
  termination apply (relation "measure (\<lambda>(a, l, r). (r - l))")
  apply auto
  apply (smt Suc_diff_Suc Suc_le_lessD diff_is_0_eq le_diff_iff less_imp_diff_less less_imp_le
             not_less partition_return_in_bounds)
  by (simp add: diff_less_mono2 less_Suc_eq_le partition_return_in_bounds)

setup {* add_rewrite_rule_cond @{thm quicksort.simps}
  [with_filt (size1_filter "l"), with_filt (size1_filter "r")] *}
setup {* register_wellform_data ("quicksort xs l r", ["l < length xs", "r < length xs"]) *}
setup {* add_prfstep_check_req ("quicksort xs l r", "l < length xs \<and> r < length xs") *}

setup {* add_backward2_prfstep @{thm Nat.diff_less_mono} *}

lemma quicksort_trivial [rewrite]:
  "r < length xs \<Longrightarrow> l \<ge> r \<Longrightarrow> quicksort xs l r = xs" by auto2

lemma quicksort_basic:
  "l < length xs \<Longrightarrow> r < length xs \<Longrightarrow> xs3 = quicksort xs l r \<Longrightarrow>
   length xs3 = length xs \<and> mset xs3 = mset xs \<and> outer_remains xs xs3 l r"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs xs3
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @case "l \<ge> r"
  @have "l < r \<and> r < length xs"
  @have "length xs2 = length xs1 \<and> mset xs2 = mset xs1 \<and> outer_remains xs1 xs2 l r" @with
    @case "p - 1 \<le> l" @then
    @have "p - 1 - l < r - l" @with @have "p - 1 < r" @end
    @apply_induct_hyp "p - 1 - l" l "p - 1" xs1 xs2
  @end
  @have "length xs3 = length xs2 \<and> mset xs3 = mset xs2 \<and> outer_remains xs2 xs3 l r" @with
    @case "p + 1 \<ge> r" @then
    @apply_induct_hyp "r - (p + 1)" "p + 1" r xs2 xs3
  @end
@qed
setup {* add_forward_prfstep_cond @{thm quicksort_basic} [with_term "?xs3.0"] *}

lemma quicksort_permutes [rewrite]:
  "l < length xs \<Longrightarrow> r < length xs \<Longrightarrow> xs' = quicksort xs l r \<Longrightarrow>
   set (sublist l (r + 1) xs') = set (sublist l (r + 1) xs)"
@proof
  @case "l \<ge> r"
  @have "xs = take l xs @ sublist l (r + 1) xs @ drop (r + 1) xs"
  @have "xs' = take l xs' @ sublist l (r + 1) xs' @ drop (r + 1) xs'"
  @have "take l xs = take l xs'"
  @have "drop (r + 1) xs = drop (r + 1) xs'"
@qed

lemma quicksort_sorts:
  "l < length xs \<Longrightarrow> r < length xs \<Longrightarrow> sorted (sublist l (r + 1) (quicksort xs l r))"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @let "xs3 = quicksort xs l r"
  @case "l \<ge> r"
  @have "l < r \<and> r < length xs"
  @have "xs1 ! p = xs3 ! p" @then
  @have "sublist l p xs2 = sublist l p xs3"
  @have "set (sublist l p xs1) = set (sublist l p xs2)" @with
    @case "p = 0" @have "p = p - 1 + 1" @end
  @have "sublist (p + 1) (r + 1) xs1 = sublist (p + 1) (r + 1) xs2"
  @have "set (sublist (p + 1) (r + 1) xs2) = set (sublist (p + 1) (r + 1) xs3)"
  @have "\<forall>x\<in>set (sublist l p xs3). x \<le> xs3 ! p"
  @have "\<forall>x\<in>set (sublist (p + 1) (r + 1) xs1). x \<ge> xs1 ! p"
  @have "sorted (sublist l p xs3)" @with
    @case "p = 0" @then
    @case "l < p - 1" @with
      @have "p - 1 - l < r - l" @with @have "p - 1 < r" @end
      @apply_induct_hyp "p - 1 - l" l "p - 1" xs1
    @end
    @have "p = p - 1 + 1"
  @end
  @have "sorted (sublist (p + 1) (r + 1) xs3)" @with
    @case "p + 1 < r" @with
      @apply_induct_hyp "r - (p + 1)" "p + 1" r xs2
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm quicksort_sorts} [with_term "quicksort ?xs ?l ?r"] *}

setup {* del_prfstep_thm @{thm quicksort.simps} *}

end
