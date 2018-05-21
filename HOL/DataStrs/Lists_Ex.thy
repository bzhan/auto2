(* Examples on lists. The itrev example comes from Section 2.4 in
   "Programming and Proving in Isabelle/HOL".

   The development of insertion and deletion on lists is essential for
   verifying functional binary search trees and RBTs. This idea follows
   the paper "Automatic Functional Correctness Proofs for Functional
   Search Trees" by Tobias Nipkow.
*)

theory Lists_Ex
imports "../Auto2_Main" Mapping_Str
begin
  
section {* Linear time version of rev *}

fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev []       ys = ys"
| "itrev (x # xs) ys = itrev xs (x # ys)"
setup {* fold add_rewrite_rule @{thms itrev.simps} *}

lemma itrev_eq_rev: "itrev x [] = rev x"
@proof
  @induct x for "\<forall>y. itrev x y = rev x @ y" arbitrary y
@qed

section {* Strict sorted *}

fun strict_sorted :: "'a::linorder list \<Rightarrow> bool" where
  "strict_sorted [] = True"
| "strict_sorted (x # ys) = ((\<forall>y\<in>set ys. x < y) \<and> strict_sorted ys)"
setup {* fold add_rewrite_rule @{thms strict_sorted.simps} *}

lemma strict_sorted_appendI [backward]:
  "strict_sorted xs \<and> strict_sorted ys \<and> (\<forall>x\<in>set xs. \<forall>y\<in>set ys. x < y) \<Longrightarrow> strict_sorted (xs @ ys)"
@proof @induct xs @qed

lemma strict_sorted_appendE1 [forward]:
  "strict_sorted (xs @ ys) \<Longrightarrow> strict_sorted xs \<and> strict_sorted ys"
@proof @induct xs @qed

lemma strict_sorted_appendE2 [forward]:
  "strict_sorted (xs @ ys) \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<forall>y\<in>set ys. x < y"
@proof @induct xs @qed

lemma strict_sorted_distinct [forward]: "strict_sorted l \<Longrightarrow> distinct l"
@proof @induct l @qed

section {* Ordered insert *}

fun ordered_insert :: "'a::ord \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "ordered_insert x [] = [x]"
| "ordered_insert x (y # ys) = (
    if x = y then (y # ys)
    else if x < y then x # (y # ys)
    else y # ordered_insert x ys)"
setup {* fold add_rewrite_rule @{thms ordered_insert.simps} *}

lemma ordered_insert_set [rewrite]:
  "set (ordered_insert x ys) = {x} \<union> set ys"
@proof @induct ys @qed

lemma ordered_insert_sorted [forward]:
  "strict_sorted ys \<Longrightarrow> strict_sorted (ordered_insert x ys)"
@proof @induct ys @qed

lemma ordered_insert_binary [rewrite]:
  "strict_sorted (xs @ a # ys) \<Longrightarrow> ordered_insert x (xs @ a # ys) =
    (if x < a then ordered_insert x xs @ a # ys
     else if x > a then xs @ a # ordered_insert x ys
     else xs @ a # ys)"
@proof @induct xs @qed

section {* Deleting an element *}

fun remove_elt_list :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_elt_list x [] = []"
| "remove_elt_list x (y # ys) = (if y = x then remove_elt_list x ys else y # remove_elt_list x ys)"
setup {* fold add_rewrite_rule @{thms remove_elt_list.simps} *}

lemma remove_elt_list_set [rewrite]:
  "set (remove_elt_list x ys) = set ys - {x}"
@proof @induct ys @qed

lemma remove_elt_list_sorted [forward]:
  "strict_sorted ys \<Longrightarrow> strict_sorted (remove_elt_list x ys)"
@proof @induct ys @qed

lemma remove_elt_idem [rewrite]:
  "x \<notin> set ys \<Longrightarrow> remove_elt_list x ys = ys"
@proof @induct ys @qed

lemma remove_elt_list_binary [rewrite]:
  "strict_sorted (xs @ a # ys) \<Longrightarrow> remove_elt_list x (xs @ a # ys) =
    (if x < a then remove_elt_list x xs @ a # ys
     else if x > a then xs @ a # remove_elt_list x ys else xs @ ys)"
@proof @induct xs @with
  @subgoal "xs = []"
    @case "x < a" @with @have "x \<notin> set ys" @end
  @endgoal @end
@qed

section {* Ordered insertion into list of pairs *}

fun ordered_insert_pairs :: "'a::ord \<Rightarrow> 'b \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "ordered_insert_pairs x v [] = [(x, v)]"
| "ordered_insert_pairs x v (y # ys) = (
    if x = fst y then ((x, v) # ys)
    else if x < fst y then (x, v) # (y # ys)
    else y # ordered_insert_pairs x v ys)"
setup {* fold add_rewrite_rule @{thms ordered_insert_pairs.simps} *}

lemma ordered_insert_pairs_map [rewrite]:
  "map_of_alist (ordered_insert_pairs x v ys) = update_map (map_of_alist ys) x v"
@proof @induct ys @qed

lemma ordered_insert_pairs_set [rewrite]:
  "set (map fst (ordered_insert_pairs x v ys)) = {x} \<union> set (map fst ys)"
@proof @induct ys @qed

lemma ordered_insert_pairs_sorted [backward]:
  "strict_sorted (map fst ys) \<Longrightarrow> strict_sorted (map fst (ordered_insert_pairs x v ys))"
@proof @induct ys @qed

lemma ordered_insert_pairs_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> ordered_insert_pairs x v (xs @ a # ys) =
    (if x < fst a then ordered_insert_pairs x v xs @ a # ys
     else if x > fst a then xs @ a # ordered_insert_pairs x v ys
     else xs @ (x, v) # ys)"
@proof @induct xs @qed

section {* Deleting from a list of pairs *}

fun remove_elt_pairs :: "'a \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> ('a \<times> 'b) list" where
  "remove_elt_pairs x [] = []"
| "remove_elt_pairs x (y # ys) = (if fst y = x then ys else y # remove_elt_pairs x ys)"
setup {* fold add_rewrite_rule @{thms remove_elt_pairs.simps} *}

lemma remove_elt_pairs_map [rewrite]:
  "strict_sorted (map fst ys) \<Longrightarrow> map_of_alist (remove_elt_pairs x ys) = delete_map x (map_of_alist ys)"
@proof @induct ys @with
  @subgoal "ys = y # ys'"
    @case "fst y = x" @with @have "x \<notin> set (map fst ys')" @end
  @endgoal @end
@qed

lemma remove_elt_pairs_on_set [rewrite]:
  "strict_sorted (map fst ys) \<Longrightarrow> set (map fst (remove_elt_pairs x ys)) = set (map fst ys) - {x}"
@proof @induct ys @qed

lemma remove_elt_pairs_sorted [backward]:
  "strict_sorted (map fst ys) \<Longrightarrow> strict_sorted (map fst (remove_elt_pairs x ys))"
@proof @induct ys @qed

lemma remove_elt_pairs_idem [rewrite]:
  "x \<notin> set (map fst ys) \<Longrightarrow> remove_elt_pairs x ys = ys"
@proof @induct ys @qed

lemma remove_elt_pairs_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> remove_elt_pairs x (xs @ a # ys) =
    (if x < fst a then remove_elt_pairs x xs @ a # ys
     else if x > fst a then xs @ a # remove_elt_pairs x ys else xs @ ys)"
@proof @induct xs @with
  @subgoal "xs = []"
    @case "x < fst a" @with @have "x \<notin> set (map fst ys)" @end
  @endgoal @end
@qed

section {* Search in a list of pairs *}

lemma map_of_alist_binary [rewrite]:
  "strict_sorted (map fst (xs @ a # ys)) \<Longrightarrow> (map_of_alist (xs @ a # ys))\<langle>x\<rangle> =
   (if x < fst a then (map_of_alist xs)\<langle>x\<rangle>
    else if x > fst a then (map_of_alist ys)\<langle>x\<rangle> else Some (snd a))"
@proof @induct xs @with
  @subgoal "xs = []"
    @case "x \<notin> set (map fst ys)"
  @endgoal @end
@qed

end
