(* Examples on lists. The itrev example comes from Section 2.4 in
   "Programming and Proving in Isabelle/HOL".

   The development of insertion and deletion on lists is essential for
   verifying binary search trees and RBTs (both functional and imperative).
   This idea follows the paper "Automatic Functional Correctness Proofs for
   Functional Search Trees" by Tobias Nipkow.
*)

theory Lists_Ex
imports "../Auto2_Main" Mapping
begin

section {* Backward induction *}
  
theorem list_induct': "P [] \<Longrightarrow> (\<forall>l. l \<noteq> [] \<and> P (tl l) \<longrightarrow> P l) \<Longrightarrow> P l"
  @proof @var_induct l "P l" @qed
setup {* add_prfstep_induction @{thm list_induct'} *}

section {* Induction on two lists. *}

theorem list_double_induct:
  "\<forall>ys. P [] ys \<Longrightarrow> \<forall>xs. P xs [] \<Longrightarrow>
   \<forall>xs ys. xs \<noteq> [] \<and> ys \<noteq> [] \<and> P (tl xs) ys \<and> P xs (tl ys) \<longrightarrow> P xs ys \<Longrightarrow> P xs ys"
@proof
  @var_induct xs "\<forall>ys. P xs ys" @with
    @subgoal "xs = x # xs'"
      @var_induct ys "ys \<noteq> [] \<longrightarrow> P (x # xs') ys"
    @endgoal
  @end
@qed
setup {* add_prfstep_double_induction @{thm list_double_induct} *}

section {* Linear time version of rev *}

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []       ys = ys" |
  "itrev (x # xs) ys = itrev xs (x # ys)"
setup {* fold add_rewrite_rule @{thms itrev.simps} *}

lemma itrev_prop [rewrite]: "itrev x y = rev x @ y"
@proof
  @induct x arbitrary y
  @have "hd x # y = [hd x] @ y"
@qed

lemma itrev_eq_rev: "itrev x [] = rev x" by auto2

section {* sorted function on lists *}

fun strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted [] = True"
| "strict_sorted (x # ys) = ((\<forall>y\<in>set ys. x < y) \<and> strict_sorted ys)"
setup {* fold add_rewrite_rule @{thms strict_sorted.simps} *}

theorem strict_sorted_single [resolve]: "strict_sorted [x]" by auto2
setup {* del_prfstep_thm @{thm strict_sorted.simps(2)} #>
  add_rewrite_rule_cond @{thm strict_sorted.simps(2)} [with_cond "?ys \<noteq> []"] *}

theorem strict_sorted_append [rewrite]:
  "strict_sorted (xs @ ys) =
    ((\<forall>x y. x \<in> set xs \<longrightarrow> y \<in> set ys \<longrightarrow> x < y) \<and> strict_sorted xs \<and> strict_sorted ys)"
@proof @induct xs @qed

theorem strict_sorted_append_one:
  "strict_sorted (xs @ [y]) = ((\<forall>x\<in>set xs. x < y) \<and> strict_sorted xs)" by auto2

theorem strict_sorted_distinct [resolve]: "strict_sorted l \<Longrightarrow> distinct l"
@proof @induct l @qed

theorem strict_sorted_min [rewrite]: "strict_sorted (x # xs) \<Longrightarrow> Min (set (x # xs)) = x" by auto2

theorem strict_sorted_delmin [rewrite]:
  "strict_sorted (x # xs) \<Longrightarrow> set (x # xs) - {x} = set xs"
@proof @have "distinct (x # xs)" @qed

theorem map_of_alist_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> (map_of_alist (xs @ a # ys))\<langle>x\<rangle> =
   (if x < fst a then (map_of_alist xs)\<langle>x\<rangle>
    else if x > fst a then (map_of_alist ys)\<langle>x\<rangle> else Some (snd a))"
@proof
  @induct xs @with @case "x \<notin> set (map fst ys)" @end
@qed

section {* Ordered insert *}

fun ordered_insert :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ordered_insert x [] = [x]"
| "ordered_insert x (y # ys) = (
    if x = y then (y # ys)
    else if x < y then x # (y # ys)
    else y # ordered_insert x ys)"
setup {* fold add_rewrite_rule @{thms ordered_insert.simps} *}

theorem ordered_insert_set [rewrite]:
  "set (ordered_insert x ys) = {x} \<union> set ys"
@proof @induct ys @qed

theorem ordered_insert_sorted [backward]:
  "strict_sorted ys \<Longrightarrow> strict_sorted (ordered_insert x ys)"
@proof @induct ys @qed

theorem ordered_insert_binary [rewrite]:
  "strict_sorted (xs @ a # ys) \<Longrightarrow> ordered_insert x (xs @ a # ys) =
    (if x < a then (ordered_insert x xs) @ a # ys
     else if x > a then xs @ a # ordered_insert x ys
     else xs @ a # ys)"
@proof
  @induct xs
  @case "x < a" @then @have "a > hd xs"
@qed

section {* Ordered insertion into list of pairs *}

fun ordered_insert_pairs :: "'a::ord \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "ordered_insert_pairs x v [] = [(x, v)]"
| "ordered_insert_pairs x v (y # ys) = (
    if x = fst y then ((x, v) # ys)
    else if x < fst y then (x, v) # (y # ys)
    else y # ordered_insert_pairs x v ys)"
setup {* fold add_rewrite_rule @{thms ordered_insert_pairs.simps} *}

theorem ordered_insert_pairs_map [rewrite]:
  "map_of_alist (ordered_insert_pairs x v ys) = update_map (map_of_alist ys) x v"
@proof @induct ys @qed

theorem ordered_insert_pairs_set [rewrite]:
  "set (map fst (ordered_insert_pairs x v ys)) = {x} \<union> set (map fst ys)"
@proof @induct ys @qed

theorem ordered_insert_pairs_sorted [backward]:
  "strict_sorted (map fst ys) \<Longrightarrow> strict_sorted (map fst (ordered_insert_pairs x v ys))"
@proof @induct ys @qed

theorem ordered_insert_pairs_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> ordered_insert_pairs x v (xs @ a # ys) =
    (if x < fst a then (ordered_insert_pairs x v xs) @ a # ys
     else if x > fst a then xs @ a # ordered_insert_pairs x v ys
     else xs @ (x, v) # ys)"
@proof
  @induct xs
  @case "x < fst a" @then @have "fst a > fst (hd xs)"
@qed

section {* Deleting an element *}

fun remove_elt_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_elt_list x [] = []"
| "remove_elt_list x (y # ys) = (if y = x then remove_elt_list x ys else y # remove_elt_list x ys)"
setup {* fold add_rewrite_rule @{thms remove_elt_list.simps} *}

theorem remove_elt_list_set [rewrite]:
  "set (remove_elt_list x ys) = set ys - {x}"
@proof @induct ys @qed

theorem remove_elt_list_sorted [backward]:
  "strict_sorted ys \<Longrightarrow> strict_sorted (remove_elt_list x ys)"
@proof @induct ys @qed

theorem remove_elt_idem [rewrite]:
  "x \<notin> set xs \<Longrightarrow> remove_elt_list x xs = xs"
@proof @induct xs @qed

theorem remove_elt_list_binary [rewrite]:
  "strict_sorted (xs @ a # ys) \<Longrightarrow> remove_elt_list x (xs @ a # ys) =
    (if x < a then (remove_elt_list x xs) @ a # ys
     else if x > a then xs @ a # remove_elt_list x ys else xs @ ys)"
@proof
  @induct xs @with
    @case "x < a" @with @have "x \<notin> set ys" @end
  @end
@qed

section {* Deleting from a list of pairs *}

fun remove_elt_pairs :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "remove_elt_pairs x [] = []"
| "remove_elt_pairs x (y # ys) = (if fst y = x then ys else y # remove_elt_pairs x ys)"
setup {* fold add_rewrite_rule @{thms remove_elt_pairs.simps} *}

theorem remove_elt_pairs_map [rewrite]:
  "strict_sorted (map fst ys) \<Longrightarrow> map_of_alist (remove_elt_pairs x ys) = delete_map x (map_of_alist ys)"
@proof
  @induct ys
  @case "fst (hd ys) = x" @with @have "x \<notin> set (map fst (tl ys))" @end
@qed

theorem remove_elt_pairs_on_set [rewrite]:
  "strict_sorted (map fst ys) \<Longrightarrow> set (map fst (remove_elt_pairs x ys)) = set (map fst ys) - {x}"
@proof @induct ys @qed

theorem remove_elt_pairs_sorted [backward]:
  "strict_sorted (map fst ys) \<Longrightarrow> strict_sorted (map fst (remove_elt_pairs x ys))"
@proof @induct ys @qed

theorem remove_elt_pairs_idem [rewrite]:
  "x \<notin> set (map fst ys) \<Longrightarrow> remove_elt_pairs x ys = ys"
@proof @induct ys @qed

theorem remove_elt_pairs_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> remove_elt_pairs x (xs @ a # ys) =
    (if x < fst a then (remove_elt_pairs x xs) @ a # ys
     else if x > fst a then xs @ a # remove_elt_pairs x ys else xs @ ys)"
@proof
  @induct xs @with
    @case "x < fst a" @with @have "x \<notin> set (map fst ys)" @end
  @end
@qed

section {* Merge sort *}

fun merge_list :: "('a::ord) list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "merge_list xs [] = xs"
| "merge_list [] ys = ys"
| "merge_list (x # xs) (y # ys) = (
    if x \<le> y then x # (merge_list xs (y # ys))
    else y # (merge_list (x # xs) ys))"
setup {* fold add_rewrite_rule @{thms merge_list.simps} *}

theorem merge_list_simp2' [rewrite]: "merge_list [] ys = ys" by auto2
setup {* del_prfstep_thm @{thm merge_list.simps(2)} *}

theorem merge_list_correct [rewrite]: "set (merge_list xs ys) = set xs \<union> set ys"
  @proof @double_induct xs ys @qed

theorem merge_list_sorted [backward2]: "sorted xs \<Longrightarrow> sorted ys \<Longrightarrow> sorted (merge_list xs ys)"
  @proof @double_induct xs ys @qed

end
