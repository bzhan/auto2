theory Mapping
imports "../Auto2_Main"
begin

datatype ('a, 'b) map = Map "'a \<Rightarrow> 'b option"

fun meval :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b option" ("_\<langle>_\<rangle>" [90]) where
  "(Map f) \<langle>h\<rangle> = f h"
setup {* add_rewrite_rule @{thm meval.simps} *}

lemma meval_ext: "\<forall>x. M\<langle>x\<rangle> = N\<langle>x\<rangle> \<Longrightarrow> M = N"
  apply (cases M) apply (cases N) by auto
setup {* add_backward_prfstep_cond @{thm meval_ext} [with_filt (order_filter "M" "N")] *}

definition empty_map :: "('a, 'b) map" where
  "empty_map = Map (\<lambda>x. None)"
setup {* add_rewrite_rule @{thm empty_map_def} *}

definition update_map :: "('a, 'b) map \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a ,'b) map" (" _ { _ \<rightarrow> _ }" [89,90,90] 90) where
  "M {k \<rightarrow> v} = Map (\<lambda>x. if x = k then Some v else M\<langle>x\<rangle>)"
setup {* add_rewrite_rule @{thm update_map_def} *}

definition delete_map :: "'a \<Rightarrow> ('a, 'b) map \<Rightarrow> ('a, 'b) map" where
  "delete_map k M = Map (\<lambda>x. if x = k then None else M\<langle>x\<rangle>)"
setup {* add_rewrite_rule @{thm delete_map_def} *}

section {* Map from an AList *}

fun map_of_alist :: "('a \<times> 'b) list \<Rightarrow> ('a, 'b) map" where
  "map_of_alist [] = empty_map"
| "map_of_alist (x # xs) = (map_of_alist xs) {fst x \<rightarrow> snd x}"
setup {* fold add_rewrite_rule @{thms map_of_alist.simps} *}

definition has_key_alist :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> bool" where [rewrite]:
  "has_key_alist xs a \<longleftrightarrow> (\<exists>p\<in>set xs. fst p = a)"

lemma map_of_alist_nil [rewrite_back]:
  "has_key_alist ys x \<longleftrightarrow> (map_of_alist ys)\<langle>x\<rangle> \<noteq> None"
@proof @induct ys @qed
setup {* add_rewrite_rule_cond @{thm map_of_alist_nil} [with_term "(map_of_alist ?ys)\<langle>?x\<rangle>"] *}

lemma map_of_alist_some [forward]:
  "(map_of_alist xs)\<langle>k\<rangle> = Some v \<Longrightarrow> (k, v) \<in> set xs"
@proof @induct xs @qed

lemma map_of_alist_nil':
  "x \<in> set (map fst ys) \<longleftrightarrow> (map_of_alist ys)\<langle>x\<rangle> \<noteq> None"
@proof @induct ys @qed
setup {* add_rewrite_rule_cond @{thm map_of_alist_nil'} [with_term "(map_of_alist ?ys)\<langle>?x\<rangle>"] *}
    
section {* Mapping defined by a set of key-value pairs *}

definition unique_keys_set :: "('a \<times> 'b) set \<Rightarrow> bool" where [rewrite]:
  "unique_keys_set S = (\<forall>i x y. (i, x) \<in> S \<longrightarrow> (i, y) \<in> S \<longrightarrow> x = y)"
setup {* add_property_const @{term unique_keys_set} *}

lemma unique_keys_setD [forward]: "unique_keys_set S \<Longrightarrow> (i, x) \<in> S \<Longrightarrow> (i, y) \<in> S \<Longrightarrow> x = y" by auto2
setup {* del_prfstep_thm_eqforward @{thm unique_keys_set_def} *}

definition map_of_aset :: "('a \<times> 'b) set \<Rightarrow> ('a, 'b) map" where
  "map_of_aset S = Map (\<lambda>a. if \<exists>b. (a, b) \<in> S then Some (THE b. (a, b) \<in> S) else None)"
setup {* add_rewrite_rule @{thm map_of_aset_def} *}
setup {* add_prfstep_check_req ("map_of_aset S", "unique_keys_set S") *}

lemma map_of_asetI1 [rewrite]: "unique_keys_set S \<Longrightarrow> (a, b) \<in> S \<Longrightarrow> (map_of_aset S)\<langle>a\<rangle> = Some b"
@proof @have "\<exists>b. (a, b) \<in> S" @have "\<exists>!b. (a, b) \<in> S" @qed

lemma map_of_asetI2 [rewrite]: "\<forall>b. (a, b) \<notin> S \<Longrightarrow> (map_of_aset S)\<langle>a\<rangle> = None" by auto2

lemma map_of_asetD1 [forward]: "(map_of_aset S)\<langle>a\<rangle> = None \<Longrightarrow> \<forall>b. (a, b) \<notin> S" by auto2

lemma map_of_asetD2 [forward]:
  "unique_keys_set S \<Longrightarrow> (map_of_aset S)\<langle>a\<rangle> = Some b \<Longrightarrow> (a, b) \<in> S" by auto2
setup {* del_prfstep_thm @{thm map_of_aset_def} *}

lemma map_of_aset_insert [rewrite]:
  "unique_keys_set (S \<union> {(k, v)}) \<Longrightarrow> map_of_aset (S \<union> {(k, v)}) = (map_of_aset S) {k \<rightarrow> v}"
@proof
  @let "M = map_of_aset S" "N = map_of_aset (S \<union> {(k, v)})"
  @have (@rule) "\<forall>x. N\<langle>x\<rangle> = (M {k \<rightarrow> v}) \<langle>x\<rangle>" @with @case "M\<langle>x\<rangle> = None" @end
@qed

lemma map_of_alist_to_aset [rewrite]:
  "unique_keys_set (set xs) \<Longrightarrow> map_of_aset (set xs) = map_of_alist xs"
@proof @induct xs @with
  @subgoal "xs = x # xs'"
    @have "set (x # xs') = set xs' \<union> {x}"
  @endgoal @end
@qed

lemma map_of_aset_delete [rewrite]:
  "unique_keys_set S \<Longrightarrow> (k, v) \<in> S \<Longrightarrow> map_of_aset (S - {(k, v)}) = delete_map k (map_of_aset S)"
@proof
  @let "T = S - {(k, v)}" @then
  @let "M = map_of_aset S" "N = map_of_aset T"
  @have (@rule) "\<forall>x. N\<langle>x\<rangle> = (delete_map k M) \<langle>x\<rangle>" @with
    @case "M\<langle>x\<rangle> = None" @case "x = k"
    @obtain y where "M\<langle>x\<rangle> = Some y" @have "(x, y) \<in> T"
  @end
@qed

lemma map_of_aset_update [rewrite]:
  "unique_keys_set S \<Longrightarrow> (k, v) \<in> S \<Longrightarrow>
   map_of_aset (S - {(k, v)} \<union> {(k, v')}) = (map_of_aset S) {k \<rightarrow> v'}" by auto2

lemma map_of_alist_delete [rewrite]:
  "set xs' = set xs - {x} \<Longrightarrow> unique_keys_set (set xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow>
   map_of_alist xs' = delete_map (fst x) (map_of_alist xs)"
@proof @have "map_of_alist xs' = map_of_aset (set xs')" @qed

lemma map_of_alist_insert [rewrite]:
  "set xs' = set xs \<union> {x} \<Longrightarrow> unique_keys_set (set xs') \<Longrightarrow>
   map_of_alist xs' = (map_of_alist xs) {fst x \<rightarrow> snd x}"
@proof @have "map_of_alist xs' = map_of_aset (set xs')" @qed

lemma map_of_alist_update [rewrite]:
  "set xs' = set xs - {(k, v)} \<union> {(k, v')} \<Longrightarrow> unique_keys_set (set xs) \<Longrightarrow> (k, v) \<in> set xs \<Longrightarrow>
   map_of_alist xs' = (map_of_alist xs) {k \<rightarrow> v'}"
@proof @have "map_of_alist xs' = map_of_aset (set xs')" @qed

section {* General update function on a mapping *}

definition map_update_set :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat, 'a) map \<Rightarrow> (nat, 'a) map" where [rewrite]:
  "map_update_set S f m = Map (\<lambda>i. if i \<in> S then Some (f i) else m\<langle>i\<rangle>)"

fun map_update_set_impl :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat, 'a) map \<Rightarrow> nat \<Rightarrow> (nat, 'a) map" where
  "map_update_set_impl S f m 0 = m"
| "map_update_set_impl S f m (Suc k) =
   (let m' = map_update_set_impl S f m k in
      if k \<in> S then m' { k \<rightarrow> f k } else m')"
setup {* fold add_rewrite_rule @{thms map_update_set_impl.simps} *}

lemma map_update_set_impl_ind [rewrite]:
  "map_update_set_impl S f m n =
   Map (\<lambda>i. if i < n then if i \<in> S then Some (f i) else m\<langle>i\<rangle> else m\<langle>i\<rangle>)"
@proof @induct n arbitrary m @qed

lemma map_update_set_impl_correct [rewrite]:
  "\<forall>i\<in>S. i < n \<Longrightarrow> map_update_set_impl S f m n = map_update_set S f m" by auto2

definition map_constr_set :: "nat set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat, 'a) map" where [rewrite]:
  "map_constr_set S f = map_update_set S f empty_map"

end
