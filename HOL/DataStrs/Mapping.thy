theory Mapping
imports "../Auto2_Main"
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

section {* The unique *}

definition THE_unique :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "THE_unique P = (if (\<exists>!x. P x) then Some (THE x. P x) else None)"
setup {* add_rewrite_rule @{thm THE_unique_def} *}

theorem THE_uniqueI: "\<exists>!x. P x \<Longrightarrow> THE_unique P \<noteq> None \<and> P (the (THE_unique P))" by auto2
setup {* add_forward_prfstep_cond @{thm THE_uniqueI} [with_term "THE_unique ?P"] *}

theorem THE_unique_None: "\<not>(\<exists>!x. P x) \<Longrightarrow> THE_unique P = None" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_None} [with_term "THE_unique ?P"] *}

theorem THE_unique_None': "\<not>(\<exists>x. P x) \<Longrightarrow> THE_unique P = None" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_None'} [with_term "THE_unique ?P"] *}

theorem THE_unique_eq: "P a \<Longrightarrow> \<exists>!x. P x \<Longrightarrow> THE_unique P = Some a" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_eq} [with_term "THE_unique ?P"] *}

theorem THE_uniqueD [resolve]: "THE_unique P = Some x \<Longrightarrow> P x"
  by (metis THE_unique_def option.sel option.simps(3) theI')

setup {* del_prfstep_thm @{thm THE_unique_def} *}
    
section {* Unique keys in an alist *}

definition unique_keys :: "(nat \<times> 'a) list \<Rightarrow> bool" where [rewrite]:
  "unique_keys xs = (\<forall>m n. m < length xs \<longrightarrow> n < length xs \<longrightarrow> m \<noteq> n \<longrightarrow> fst (xs ! m) \<noteq> fst (xs ! n))"
setup {* add_property_const @{term unique_keys} *}

lemma unique_keysD:
  "unique_keys xs \<Longrightarrow> m < length xs \<Longrightarrow> n < length xs \<Longrightarrow> m \<noteq> n \<Longrightarrow> fst (xs ! m) \<noteq> fst (xs ! n)" by auto2
setup {* add_forward_prfstep_cond @{thm unique_keysD} [with_term "?xs ! ?m", with_term "?xs ! ?n"] *}
setup {* del_prfstep_thm_eqforward @{thm unique_keys_def} *}

definition has_key :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> bool" where
  "has_key xs k = (\<exists>v'. (k, v') \<in># mset xs)"
setup {* add_rewrite_rule @{thm has_key_def} *}

theorem not_has_key [forward, backward2]:
  "\<not>(has_key xs k) \<Longrightarrow> p \<in># mset xs \<Longrightarrow> k \<noteq> fst p" by auto2

definition map_of_kv_set :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_set S = Map (\<lambda>a. THE_unique (\<lambda>b. (a, b) \<in> S))"
setup {* add_rewrite_rule @{thm map_of_kv_set_def} *}

setup {* add_gen_prfstep ("THE_unique_case",
  [WithTerm @{term_pat "THE_unique (\<lambda>b. (?a, b) \<in> ?S)"},
   CreateCase @{term_pat "\<exists>!b. (?a, b) \<in> ?S"}]) *}

definition unique_keys_set :: "(nat \<times> 'a) set \<Rightarrow> bool" where
  "unique_keys_set S = (\<forall>i x y. (i, x) \<in> S \<longrightarrow> (i, y) \<in> S \<longrightarrow> x = y)"
setup {* add_rewrite_rule @{thm unique_keys_set_def} *}

theorem unique_keys_imp [forward]:
  "unique_keys_set S \<Longrightarrow> (i, x) \<in> S \<Longrightarrow> \<exists>!x. (i, x) \<in> S" by auto2

theorem map_of_kv_set_insert [rewrite]:
  "unique_keys_set T \<Longrightarrow> \<forall>v. (k, v) \<notin> T \<Longrightarrow> map_of_kv_set (T \<union> { (k, v) }) = (map_of_kv_set T) {k \<rightarrow> v}"
@proof
  @let "S = T \<union> { (k, v) }" @then
  @have "T \<subseteq> S" @then @have "unique_keys_set S"
@qed

theorem map_of_kv_set_delete [rewrite]:
  "unique_keys_set T \<Longrightarrow> (k, v) \<in> T \<Longrightarrow> map_of_kv_set (T - { (k, v) }) = delete_map k (map_of_kv_set T)"
@proof
  @let "S = T - { (k, v) }" @then
  @have "S \<subseteq> T" @then @have "unique_keys_set S"
@qed

theorem map_of_kv_set_update [rewrite]:
  "unique_keys_set T \<Longrightarrow> (k, v) \<in> T \<Longrightarrow>
   map_of_kv_set ((T - { (k, v) }) \<union> { (k, v') }) = (map_of_kv_set T) {k \<rightarrow> v'}"
@proof
  @have "unique_keys_set (T - { (k, v) })" @then
  @have "\<forall>x. (k, x) \<notin> T - { (k, v) }"
@qed

definition map_of_kv_list :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) map" where
  "map_of_kv_list xs = map_of_kv_set (set xs)"
setup {* add_rewrite_rule @{thm map_of_kv_list_def} *}

theorem unique_keys_to_set [forward]:
  "unique_keys xs \<Longrightarrow> unique_keys_set (set xs)"
@proof
  @let "S = set xs"
  @have "\<forall>k x y. (k, x) \<in> S \<longrightarrow> (k, y) \<in> S \<longrightarrow> x = y" @with
    @obtain i where "i < length xs" "(k, x) = xs ! i"
    @obtain j where "j < length xs" "(k, y) = xs ! j"
  @end
@qed

theorem unique_key_to_distinct [forward]: "unique_keys xs \<Longrightarrow> distinct xs"
  using distinct_conv_nth unique_keys_def by fastforce

lemma map_of_kv_list_empty [backward]:
  "[] = xs \<Longrightarrow> map_of_kv_list xs = empty_map" by auto2

theorem mset_update' [rewrite]:
  "i < length ls \<Longrightarrow> mset (list_update ls i v) = {#v#} + (mset ls - {# ls ! i #})"
  using mset_update by fastforce

theorem empty_list_to_empty_map [rewrite]:
  "map_of_kv_list ([]::('a \<times> 'b) list) = empty_map" by auto2

theorem has_key_set [rewrite]:
  "has_key xs k \<longleftrightarrow> (\<exists>v. (k, v) \<in> set xs)"
@proof
  @case "has_key xs k" @with
    @obtain v where "(k, v) \<in># mset xs" @then @have "(k, v) \<in> set xs"
  @end
@qed

theorem has_key_to_map_none [rewrite_bidir]:
  "unique_keys xs \<Longrightarrow> has_key xs k \<longleftrightarrow> (map_of_kv_list xs) \<langle>k\<rangle> \<noteq> None" by auto2
setup {* del_prfstep_thm @{thm has_key_set} *}

end
