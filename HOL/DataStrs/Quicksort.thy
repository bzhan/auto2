theory Quicksort
imports Arrays_Ex
begin

section {* Outer remains *}
  
definition outer_remains :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "outer_remains xs xs' l r \<longleftrightarrow> (length xs = length xs' \<and> (\<forall>i. i < l \<or> r < i \<longrightarrow> xs ! i = xs' ! i))"

lemma outer_remainsD1: "outer_remains xs xs' l r \<Longrightarrow> i < l \<Longrightarrow> xs ! i = xs' ! i" by auto2
setup {* add_forward_prfstep_cond @{thm outer_remainsD1} [with_term "?xs' ! ?i"] *}

lemma outer_remainsD2: "outer_remains xs xs' l r \<Longrightarrow> r < i \<Longrightarrow> xs ! i = xs' ! i" by auto2
setup {* add_forward_prfstep_cond @{thm outer_remainsD2} [with_term "?xs' ! ?i"] *}
  
lemma outer_remainsD3 [forward]: "outer_remains xs xs' l r \<Longrightarrow> length xs = length xs'" by auto2

lemma outer_remainsD_take [rewrite]:
  "i \<le> length xs \<Longrightarrow> outer_remains xs xs' l r \<Longrightarrow> i < l \<Longrightarrow> take i xs = take i xs'" by auto2

lemma outer_remainsD_drop [rewrite]:
  "outer_remains xs xs' l r \<Longrightarrow> r < i \<Longrightarrow> drop i xs = drop i xs'" by auto2

setup {* del_prfstep_thm_eqforward @{thm outer_remains_def} *}

section {* part1 function *}  

function part1 :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> (nat \<times> 'a list)" where
  "part1 xs l r a = (
     if r \<le> l then (r, xs)
     else if xs ! l \<le> a then part1 xs (l + 1) r a
     else part1 (list_swap xs l r) l (r - 1) a)"
  by auto
  termination by (relation "measure (\<lambda>(_,l,r,_). r - l)") auto
setup {* register_wellform_data ("part1 xs l r a", ["r < length xs"]) *}
setup {* add_prfstep_check_req ("part1 xs l r a", "r < length xs") *}

lemma part1_basic:
  "r < length xs \<Longrightarrow> l \<le> r \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow>
   outer_remains xs xs' l r \<and> mset xs' = mset xs \<and> l \<le> rs \<and> rs \<le> r"
@proof @fun_induct "part1 xs l r a" @with
  @subgoal "(xs = xs, l = l, r = r, a = a)" @unfold "part1 xs l r a" @end
@qed
setup {* add_forward_prfstep_cond @{thm part1_basic} [with_term "part1 ?xs ?l ?r ?a"] *}

lemma part1_partitions1 [backward]:
  "r < length xs \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow> l \<le> i \<Longrightarrow> i < rs \<Longrightarrow> xs' ! i \<le> a"
@proof @fun_induct "part1 xs l r a" @with
  @subgoal "(xs = xs, l = l, r = r, a = a)" @unfold "part1 xs l r a" @end
@qed

lemma part1_partitions2 [backward]:
  "r < length xs \<Longrightarrow> (rs, xs') = part1 xs l r a \<Longrightarrow> rs < i \<Longrightarrow> i \<le> r \<Longrightarrow> xs' ! i \<ge> a"
@proof @fun_induct "part1 xs l r a" @with
  @subgoal "(xs = xs, l = l, r = r, a = a)" @unfold "part1 xs l r a" @end
@qed

section {* Paritition function *}

definition partition :: "('a::linorder list) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a list)" where
  "partition xs l r = (
    let p = xs ! r;
      (m, xs') = part1 xs l (r - 1) p;
      m' = if xs' ! m \<le> p then m + 1 else m
    in
      (m', list_swap xs' m' r))"
setup {* register_wellform_data ("partition xs l r", ["l < r", "r < length xs"]) *}

lemma partition_basic:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs') = partition xs l r \<Longrightarrow>
   outer_remains xs xs' l r \<and> mset xs' = mset xs \<and> l \<le> rs \<and> rs \<le> r"
@proof @unfold "partition xs l r" @qed
setup {* add_forward_prfstep_cond @{thm partition_basic} [with_term "partition ?xs ?l ?r"] *}
  
lemma partition_partitions1 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs') = partition xs l r \<Longrightarrow>
   x \<in> set (sublist l rs xs') \<Longrightarrow> x \<le> xs' ! rs"
@proof @unfold "partition xs l r" @obtain i where "i \<ge> l" "i < rs" "x = xs' ! i" @qed

lemma partition_partitions2 [forward]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> (rs, xs'') = partition xs l r \<Longrightarrow>
   x \<in> set (sublist (rs + 1) (r + 1) xs'') \<Longrightarrow> x \<ge> xs'' ! rs"
@proof @unfold "partition xs l r"
  @obtain i where "i \<ge> rs + 1" "i < r + 1" "x = xs'' ! i"
  @let "p = xs ! r"
  @let "m = fst (part1 xs l (r - 1) p)"
  @let "xs' = snd (part1 xs l (r - 1) p)"
  @case "xs' ! m \<le> p"
@qed

lemma quicksort_term1 [resolve]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> fst (partition xs l r) - (l + 1) < r - l"
@proof @have "fst (partition xs l r) - l - 1 < r - l" @qed

lemma quicksort_term2 [resolve]:
  "l < r \<Longrightarrow> r < length xs \<Longrightarrow> r - (fst (partition xs l r) + 1) < r - l"
@proof @have "r - fst (partition xs l r) - 1 < r - l" @qed

function quicksort :: "('a::linorder) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "quicksort xs l r = (
    if l \<ge> r then xs
    else if r < length xs then
      let (p, xs1) = partition xs l r;
        xs2 = quicksort xs1 l (p - 1)
      in
        quicksort xs2 (p + 1) r
    else xs)"
  by auto
  termination apply (relation "measure (\<lambda>(a, l, r). (r - l))")
  apply auto by auto2+

lemma quicksort_trivial [rewrite]:
  "l \<ge> r \<Longrightarrow> quicksort xs l r = xs"
@proof @unfold "quicksort xs l r" @qed

lemma quicksort_basic:
  "mset (quicksort xs l r) = mset xs \<and> outer_remains xs (quicksort xs l r) l r"
@proof
  @let "d = r - l"
  @strong_induct d arbitrary l r xs
  @unfold "quicksort xs l r"
  @case "l \<ge> r" @case "r \<ge> length xs"
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @let "xs3 = quicksort xs l r"
  @have "mset xs2 = mset xs1 \<and> outer_remains xs1 xs2 l r" @with
    @case "p - 1 \<le> l"
    @apply_induct_hyp "(p-1)-l" l "p-1" xs1
  @end
  @have "mset xs3 = mset xs2 \<and> outer_remains xs2 xs3 l r" @with
    @case "p + 1 \<ge> r"
    @apply_induct_hyp "r-(p+1)" "p+1" r xs2
  @end
@qed
setup {* add_forward_prfstep_cond @{thm quicksort_basic} [with_term "quicksort ?xs ?l ?r"] *}

lemma quicksort_permutes [rewrite]:
  "xs' = quicksort xs l r \<Longrightarrow> set (sublist l (r + 1) xs') = set (sublist l (r + 1) xs)"
@proof @unfold "quicksort xs l r"
  @case "l \<ge> r" @case "r \<ge> length xs"
  @have "xs = take l xs @ sublist l (r + 1) xs @ drop (r + 1) xs"
  @have "xs' = take l xs' @ sublist l (r + 1) xs' @ drop (r + 1) xs'"
  @have "take l xs = take l xs'"
  @have "drop (r + 1) xs = drop (r + 1) xs'"
@qed

lemma quicksort_sorts:
  "r < length xs \<Longrightarrow> sorted (sublist l (r + 1) (quicksort xs l r))"
@proof
  @let "d = r - l"
  @case "l \<ge> r" @case "r \<ge> length xs"
  @strong_induct d arbitrary l r xs
  @let "p = fst (partition xs l r)"
  @let "xs1 = snd (partition xs l r)"
  @let "xs2 = quicksort xs1 l (p - 1)"
  @let "xs3 = quicksort xs2 (p + 1) r"
  @have "xs1 ! p = xs3 ! p"
  @have "sublist l p xs2 = sublist l p xs3"
  @have "set (sublist l p xs1) = set (sublist l p xs2)" @with
    @case "p = 0" @have "p = p - 1 + 1" @end
  @have "sublist (p + 1) (r + 1) xs1 = sublist (p + 1) (r + 1) xs2"
  @have "set (sublist (p + 1) (r + 1) xs2) = set (sublist (p + 1) (r + 1) xs3)"
  @have "\<forall>x\<in>set (sublist l p xs3). x \<le> xs3 ! p"
  @have "\<forall>x\<in>set (sublist (p + 1) (r + 1) xs1). x \<ge> xs1 ! p"
  @have "sorted (sublist l p xs3)" @with
    @case "p = 0"
    @case "l \<ge> p - 1" @with @have "p = p - 1 + 1" @end
    @apply_induct_hyp "(p-1)-l" l "p-1" xs1
  @end
  @have "sorted (sublist (p + 1) (r + 1) xs3)" @with
    @case "r \<le> p + 1"
    @apply_induct_hyp "r-(p+1)" "p+1" r xs2
  @end
  @unfold "quicksort xs l r"
@qed
setup {* add_forward_prfstep_cond @{thm quicksort_sorts} [with_term "quicksort ?xs ?l ?r"] *}

lemma quicksort_sorts_all [rewrite]:
  "xs \<noteq> [] \<Longrightarrow> quicksort xs 0 (length xs - 1) = sort xs"
@proof
  @let "xs' = quicksort xs 0 (length xs - 1)"
  @have "sublist 0 (length xs) xs' = xs'"
@qed

end
