theory Mapping
imports "../Logic_More"
begin

datatype ('a, 'b) map = Map "'a \<Rightarrow> 'b option"
fun meval :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b option" ("_\<langle>_\<rangle>" [90]) where
  "(Map f) \<langle>h\<rangle> = f h"
setup {* add_rewrite_rule @{thm meval.simps} *}

theorem meval_ext: "\<forall>x. M\<langle>x\<rangle> = N\<langle>x\<rangle> \<Longrightarrow> M = N"
  apply (cases M) apply (cases N) by auto
setup {* add_backward_prfstep_cond @{thm meval_ext} [with_filt (order_filter "M" "N")] *}

definition empty_map :: "('a, 'b) map" where
  "empty_map = Map (\<lambda>x. None)"
setup {* add_rewrite_rule @{thm empty_map_def} *}

definition update_map ::
  "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a ,'b) map" (" _ { _ \<rightarrow> _ }" [89,90,90] 90) where
  "update_map M k v = Map (\<lambda>x. if x = k then Some v else M\<langle>x\<rangle>)"
setup {* add_rewrite_rule @{thm update_map_def} *}

definition delete_map :: "'a \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "delete_map k M = Map (\<lambda>x. if x = k then None else M\<langle>x\<rangle>)"
setup {* add_rewrite_rule @{thm delete_map_def} *}

section {* map_of_alist *}

definition map_of_alist :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) map" where
  "map_of_alist xs = Map (map_of xs)"
setup {* add_rewrite_rule @{thm map_of_alist_def} *}

theorem map_of_alist_simps [rewrite]:
  "map_of_alist [] = empty_map"
  "map_of_alist (x # xs) = update_map (map_of_alist xs) (fst x) (snd x)" by auto2+
setup {* del_prfstep_thm @{thm map_of_alist_def} *}

theorem map_of_alist_nil [rewrite]:
  "x \<notin> set (map fst ys) \<Longrightarrow> (map_of_alist ys)\<langle>x\<rangle> = None"
@proof @induct ys @qed

end
