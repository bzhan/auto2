theory Mapping
imports "../Auto2"
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

definition binary_map :: "('a::linorder) \<Rightarrow> 'b \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "binary_map k v M1 M2 = Map (\<lambda>x. if x = k then Some v else if x < k then M1\<langle>x\<rangle> else M2\<langle>x\<rangle>)"
setup {* add_rewrite_rule @{thm binary_map_def} *}

lemma binary_map_single [rewrite]:
  "binary_map k v empty_map empty_map = empty_map {k \<rightarrow> v}" by auto2

lemma binary_map_update [rewrite]:
  "(binary_map k v' M1 M2) {k \<rightarrow> v} = binary_map k v M1 M2" by auto2

lemma binary_map_update_left [rewrite]:
  "a < k \<Longrightarrow> binary_map k v (M1 {a \<rightarrow> b}) M2 = (binary_map k v M1 M2) {a \<rightarrow> b}" by auto2

lemma binary_map_update_right [rewrite]:
  "a > k \<Longrightarrow> binary_map k v M1 (M2 {a \<rightarrow> b}) = (binary_map k v M1 M2) {a \<rightarrow> b}" by auto2

end
