theory ArrayMap
imports SepAuto "../DataStrs/Mapping"
begin

text {* Implementation of a map from nats [0,n) to 'a using a fixed-size array. *}

datatype 'a array_map = ArrayMap (alen: nat) (aref: "'a option array")
setup {* add_rewrite_rule_back @{thm array_map.collapse} *}
setup {* add_rewrite_rule @{thm array_map.case} *}
setup {* fold add_rewrite_rule @{thms array_map.sel} *}

definition amap_of_list :: "'a option list \<Rightarrow> (nat, 'a) map" where [rewrite]:
  "amap_of_list xs = Map (\<lambda>i. if i < length xs then xs ! i else None)"

lemma amap_of_listI [backward]:
  "\<forall>i. if i < length xs then m\<langle>i\<rangle> = xs ! i else m\<langle>i\<rangle> = None \<Longrightarrow> m = amap_of_list xs" by auto2

lemma amap_of_listD [rewrite]:
  "(amap_of_list xs)\<langle>i\<rangle> = (if i < length xs then xs ! i else None)" by auto2

lemma amap_of_list_update [rewrite]:
  "i < length xs \<Longrightarrow> amap_of_list (list_update xs i (Some x)) = (amap_of_list xs) {i \<rightarrow> x}" by auto2

lemma amap_of_list_delete [rewrite]:
  "i < length xs \<Longrightarrow> amap_of_list (list_update xs i None) = delete_map i (amap_of_list xs)" by auto2

fun amap :: "(nat, 'a::heap) map \<Rightarrow> 'a array_map \<Rightarrow> assn" where
  "amap m (ArrayMap al a) = (\<exists>\<^sub>Axs. a \<mapsto>\<^sub>a xs * \<up>(al = length xs) * \<up>(m = amap_of_list xs))"
setup {* add_rewrite_ent_rule @{thm amap.simps} *}

definition amap_new :: "nat \<Rightarrow> ('a::heap) array_map Heap" where [sep_proc_defs]:
  "amap_new n = do {
    a \<leftarrow> Array.new n None;
    return (ArrayMap n a)
   }"

lemma amap_new_rule [hoare_triple]:
  "<emp>
   amap_new k
   <\<lambda>r. amap empty_map r * \<up>(alen r = k)>" by auto2

definition amap_lookup :: "('a::heap) array_map \<Rightarrow> nat \<Rightarrow> 'a option Heap" where [sep_proc_defs]:
  "amap_lookup p i = (if i < alen p then Array.nth (aref p) i else return None)"

lemma amap_lookup_rule [hoare_triple]:
  "<amap m p>
   amap_lookup p k
   <\<lambda>r. amap m p * \<up>(r = m\<langle>k\<rangle>)>" by auto2

lemma amap_heap_preserving [heap_presv_thms]:
  "heap_preserving (amap_lookup p i)" by auto2

definition amap_update :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a array_map \<Rightarrow> unit Heap" where [sep_proc_defs]:
  "amap_update i x p =
   (if i < alen p then
      do { Array.upd i (Some x) (aref p); return () }
    else raise ''amap_update'')"

lemma amap_update_rule [hoare_triple]:
  "<amap m p * \<up>(i < alen p)>
   amap_update i x p
   <\<lambda>_. amap (m {i \<rightarrow> x}) p>" by auto2

definition amap_delete :: "nat \<Rightarrow> 'a::heap array_map \<Rightarrow> unit Heap" where [sep_proc_defs]:
  "amap_delete i p =
   (if i < alen p then
      do { Array.upd i None (aref p); return () }
    else raise ''amap_delete'')"

lemma amap_delete_rule [hoare_triple]:
  "<amap m p * \<up>(i < alen p)>
   amap_delete i p
   <\<lambda>_. amap (delete_map i m) p>" by auto2

setup {* del_prfstep_thm @{thm array_map.collapse} *}
setup {* del_prfstep_thm @{thm amap_of_list_def} *}
setup {* del_prfstep_thm @{thm amap.simps} *}

end
