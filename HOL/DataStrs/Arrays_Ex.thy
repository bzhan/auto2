theory Arrays_Ex
imports "../Auto2_Main"
begin

section {* List swap *}

definition list_swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "list_swap xs i j = xs[i := xs ! j, j := xs ! i]"
setup {* add_rewrite_rule @{thm list_swap_def} *}
setup {* register_wellform_data ("list_swap xs i j", ["i < length xs", "j < length xs"]) *}
setup {* add_prfstep_check_req ("list_swap xs i j", "i < length xs \<and> j < length xs") *}

lemma list_swap_eval:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   (list_swap xs i j) ! k = (if k = i then xs ! j else if k = j then xs ! i else xs ! k)" by auto2
setup {* add_rewrite_rule_cond @{thm list_swap_eval} [with_cond "?k \<noteq> ?i", with_cond "?k \<noteq> ?j"] *}

lemma list_swap_eval_triv [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! i = xs ! j"
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> (list_swap xs i j) ! j = xs ! i" by auto2+

lemma length_list_swap:
  "length (list_swap xs i j) = length xs" by auto2
setup {* add_forward_prfstep_cond @{thm length_list_swap} [with_term "list_swap ?xs ?i ?j"] *}

lemma mset_list_swap [rewrite]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow> mset (list_swap xs i j) = mset xs" by auto2
setup {* del_prfstep_thm @{thm list_swap_def} *}
setup {* add_rewrite_rule_back @{thm list_swap_def} *}

section {* Reverse *}

lemma nat_sub1 [rewrite]: "(a::nat) - n - 1 = a - 1 - n" by simp

lemma rev_nth [rewrite]:
  "n < length xs \<Longrightarrow> rev xs ! n = xs ! (length xs - 1 - n)"
@proof @induct xs @qed
  
fun rev_swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "rev_swap xs i j = (if i < j then rev_swap (list_swap xs i j) (i + 1) (j - 1) else xs)"
setup {* add_rewrite_rule_cond @{thm rev_swap.simps} [with_filt (size1_filter "i"), with_filt (size1_filter "j")] *}
setup {* register_wellform_data ("rev_swap xs i j", ["j < length xs"]) *}
setup {* add_prfstep_check_req ("rev_swap xs i j", "j < length xs") *}

lemma rev_swap_length:
  "j < length xs \<Longrightarrow> length (rev_swap xs i j) = length xs"
@proof
  @strong_induct j arbitrary i xs
  @case "i < j" @with
    @apply_induct_hyp "j - 1" "i + 1" "list_swap xs i j"
  @end
@qed
setup {* add_forward_prfstep_cond @{thm rev_swap_length} [with_term "rev_swap ?xs ?i ?j"] *}

lemma nat_sub2 [rewrite]: "(k::nat) \<ge> i + 1 \<Longrightarrow> j - 1 - (k - (i + 1)) = j - (k - i)" by simp

lemma rev_swap_eval [rewrite]:
  "j < length xs \<Longrightarrow> (rev_swap xs i j) ! k =
    (if k < i then xs ! k else if k > j then xs ! k else xs ! (j - (k - i)))"
@proof
  @strong_induct j arbitrary i xs
  @case "i < j" @with
    @apply_induct_hyp "j - 1" "i + 1" "list_swap xs i j"
  @end
@qed

lemma rev_swap_is_rev [rewrite]:
  "length xs \<ge> 1 \<Longrightarrow> rev_swap xs 0 (length xs - 1) = rev xs" by auto2

section {* Copy one array to the beginning of another *}
    
fun array_copy :: "'a list \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "array_copy xs i xs' j n =
    (if n = 0 then xs' else array_copy xs (i + 1) (xs' [j := xs ! i]) (j + 1) (n - 1))"
setup {* add_rewrite_rule_cond @{thm array_copy.simps} [with_filt (size1_filter "i"), with_filt (size1_filter "j")] *}
setup {* register_wellform_data ("array_copy xs i xs' j n", ["i + n \<le> length xs", "j + n \<le> length xs'"]) *}
setup {* add_prfstep_check_req ("array_copy xs i xs' j n", "i + n \<le> length xs \<and> j + n \<le> length xs'") *}

lemma array_copy_length:
  "i + n \<le> length xs \<Longrightarrow> j + n \<le> length xs' \<Longrightarrow> length (array_copy xs i xs' j n) = length xs'"
@proof
  @strong_induct n arbitrary i j xs'
  @case "n = 0"
  @apply_induct_hyp "n - 1" "i + 1" "j + 1" "xs' [j := xs ! i]"
@qed
setup {* add_forward_prfstep_cond @{thm array_copy_length} [with_term "array_copy ?xs ?i ?xs' ?j ?n"] *}

lemma nat_sub6 [rewrite]: "(a::nat) + (b + 1) - (c + 1) = a + b - c" by simp

lemma array_copy_eval [rewrite]:
  "i + n \<le> length xs \<Longrightarrow> j + n \<le> length xs' \<Longrightarrow>
   (array_copy xs i xs' j n) ! k = (if k < j then xs' ! k else if k \<ge> j + n then xs' ! k else xs ! (k + i - j))"
@proof
  @strong_induct n arbitrary i j xs'
  @case "n = 0" @then
  @apply_induct_hyp "n - 1" "i + 1" "j + 1" "xs' [j := xs ! i]"
@qed

setup {* del_prfstep_thm @{thm array_copy.simps} *}

lemma array_copy_take [backward]:
  "n \<le> length xs' \<Longrightarrow> n \<le> length xs \<Longrightarrow> take n (array_copy xs 0 xs' 0 n) = take n xs"
@proof
  @have "length (take n (array_copy xs 0 xs' 0 n)) = length (take n xs)"
@qed

section {* Sublist *}

definition sublist :: "nat \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "sublist l r xs = drop l (take r xs)"
setup {* register_wellform_data ("sublist l r xs", ["l \<le> r", "r \<le> length xs"]) *}
setup {* add_prfstep_check_req ("sublist l r xs", "l \<le> r \<and> r \<le> length xs") *}

lemma length_sublist:
  "r \<le> length xs \<Longrightarrow> length (sublist l r xs) = r - l" by auto2
setup {* add_forward_prfstep_cond @{thm length_sublist} [with_term "sublist ?l ?r ?xs"] *}

lemma nth_sublist [rewrite]:
  "r \<le> length xs \<Longrightarrow> xs' = sublist l r xs \<Longrightarrow> i < length xs' \<Longrightarrow> xs' ! i = xs ! (i + l)" by auto2

lemma sublist_nil [rewrite]:
  "r \<le> length xs \<Longrightarrow> r \<le> l \<Longrightarrow> sublist l r xs = []" by auto2

setup {* del_prfstep_thm @{thm sublist_def} *}

lemma sublist_single [rewrite]:
  "l + 1 \<le> length xs \<Longrightarrow> sublist l (l + 1) xs = [xs ! l]"
@proof @have "length [xs ! l] = 1" @qed

lemma nat_sub7 [rewrite]: "b \<le> a \<Longrightarrow> c \<le> b \<Longrightarrow> ((a::nat) - b) + (b - c) = a - c" by simp
lemma nat_sub8 [rewrite]: "b \<ge> c \<Longrightarrow> a \<ge> b - c \<Longrightarrow> (a::nat) - (b - c) + b = a + c" by simp

lemma sublist_append [rewrite]:
  "l \<le> m \<Longrightarrow> m \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow> sublist l m xs @ sublist m r xs = sublist l r xs"
@proof
  @let "xs1 = sublist l r xs" "xs2 = sublist l m xs" "xs3 = sublist m r xs"
  @have "length (xs2 @ xs3) = (r - m) + (m - l)"
  @have "\<forall>i<length xs1. xs1 ! i = (xs2 @ xs3) ! i" @with
    @case "i < length xs2" @then
    @have "i - length xs2 < length xs3"
  @end
@qed

lemma sublist_Cons [rewrite]:
  "r \<le> length xs \<Longrightarrow> l < r \<Longrightarrow> xs ! l # sublist (l + 1) r xs = sublist l r xs"
@proof
  @have "sublist l r xs = sublist l (l + 1) xs @ sublist (l + 1) r xs"
@qed

lemma sorted_triv_sublist [backward]:
  "r + 1 \<le> length xs \<Longrightarrow> l \<ge> r \<Longrightarrow> sorted (sublist l (r + 1) xs)"
@proof @case "l = r" @qed

lemma sorted_pivoted_list [forward]:
  "l \<le> p \<Longrightarrow> p + 1 \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow>
   sorted (sublist (p + 1) r xs) \<Longrightarrow> sorted (sublist l p xs) \<Longrightarrow>
   \<forall>x\<in>set (sublist l p xs). x \<le> xs ! p \<Longrightarrow> \<forall>y\<in>set (sublist (p + 1) r xs). xs ! p \<le> y \<Longrightarrow>
   sorted (sublist l r xs)"
@proof
  @have "sublist p r xs = (xs ! p) # sublist (p + 1) r xs"
  @have "sorted (sublist p r xs)"
  @case "p = 0"
  @have "sublist l r xs = sublist l p xs @ sublist p r xs"
@qed

lemma sublist_equalityI:
  "i \<le> j \<Longrightarrow> j \<le> length xs \<Longrightarrow> length xs = length ys \<Longrightarrow>
   \<forall>k. i \<le> k \<longrightarrow> k < j \<longrightarrow> xs ! k = ys ! k \<Longrightarrow> sublist i j xs = sublist i j ys"
@proof
  @let "xs1 = sublist i j xs" "xs2 = sublist i j ys"
  @have "\<forall>k<j-i. xs1 ! k = xs2 ! k" @with @have "i \<le> i + k" @end
@qed
setup {* add_backward2_prfstep_cond @{thm sublist_equalityI} [with_filt (order_filter "xs" "ys")] *}

lemma set_sublist [resolve]:
  "j \<le> length xs \<Longrightarrow> x \<in> set (sublist i j xs) \<Longrightarrow> \<exists>k. k \<ge> i \<and> k < j \<and> x = xs ! k"
@proof
  @let "xs' = sublist i j xs" @have "length xs' = j - i"
  @obtain l where "l < length xs'" "xs' ! l = x"
  @have "x = xs ! (l + i)"
  @have "i + l \<ge> i"
@qed

lemma list_take_sublist_drop_eq [rewrite]:
  "l \<le> r \<Longrightarrow> r \<le> length xs \<Longrightarrow> take l xs @ sublist l r xs @ drop r xs = xs"
@proof
  @have "take l xs = sublist 0 l xs"
  @have "drop r xs = sublist r (length xs) xs"
@qed

end
