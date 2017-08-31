theory Quicksort_Func2
imports Quicksort_Func "../SepLogic/More_Lists"
begin

lemma quicksort_permutes:
  "l < length xs \<Longrightarrow> r < length xs \<Longrightarrow> xs' = quicksort xs l r \<Longrightarrow>
   mset (sublist' l (r + 1) xs') = mset (sublist' l (r + 1) xs)" by auto2
setup {* add_forward_prfstep_cond @{thm quicksort_permutes} [with_term "?xs'"] *}

setup {* add_rewrite_rule_cond @{thm quicksort.simps}
  [with_filt (size1_filter "l"), with_filt (size1_filter "r")] *}

lemma quicksort_sorts:
  "l < length xs \<Longrightarrow> r < length xs \<Longrightarrow> sorted (sublist' l (r + 1) (quicksort xs l r))"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @let "xs3 = quicksort xs l r"
  @case "l \<ge> r"
  @have "l < r \<and> r < length xs"
  @have "sublist' l p xs2 = sublist' l p xs3"
  @have "xs1 ! p = xs3 ! p" @then
  @have "\<forall>x\<in>set (sublist' l p xs3). x \<le> xs3 ! p" @with
    @case "l < p - 1" @with @case "p = 0" @end
  @end
  @have "\<forall>x\<in>set (sublist' (p + 1) (r + 1) xs3). x \<ge> xs3 ! p" @with
    @case "p = 0" @case "p + 1 < r"
  @end
  @have "sorted (sublist' l p xs3)" @with
    @case "p = 0" @then
    @case "l < p - 1" @with
      @have "p - 1 - l < r - l" @with @have "p - 1 < r" @end
      @apply_induct_hyp "p - 1 - l" l "p - 1" xs1
    @end
    @have "p = p - 1 + 1"
  @end
  @have "sorted (sublist' (p + 1) (r + 1) xs3)" @with
    @case "p + 1 < r" @with
      @have "r - (p + 1) < r - l"
      @apply_induct_hyp "r - (p + 1)" "p + 1" r xs2
    @end
  @end
@qed
setup {* add_forward_prfstep_cond @{thm quicksort_sorts} [with_term "quicksort ?xs ?l ?r"] *}

setup {* del_prfstep_thm @{thm quicksort.simps} *}

end
