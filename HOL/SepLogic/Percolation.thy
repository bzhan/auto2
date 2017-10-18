theory Percolation
imports Union_Find "../DataStrs/Percolation_Func"
begin

section {* Constructing the connected relation *}

fun connected_rel_imp :: "nat \<Rightarrow> (nat \<times> nat) list \<Rightarrow> nat \<Rightarrow> uf Heap" where
  "connected_rel_imp n es 0 = do { p \<leftarrow> uf_init n; return p }"
| "connected_rel_imp n es (Suc k) = do {
    p \<leftarrow> connected_rel_imp n es k;
    p' \<leftarrow> uf_union p (fst (es ! k)) (snd (es ! k));
    return p' }"
declare connected_rel_imp.simps [sep_proc_defs]

lemma connected_rel_imp_to_fun [hoare_triple]:
  "<\<up>(is_valid_graph n (set es)) * \<up>(k \<le> length es)>
   connected_rel_imp n es k
   <is_uf n (connected_rel_ind n es k)>"
@proof @induct k @qed
declare connected_rel_imp.simps [sep_proc_defs del]

lemma connected_rel_imp_correct [hoare_triple]:
  "<\<up>(is_valid_graph n (set es))>
   connected_rel_imp n es (length es)
   <is_uf n (connected_rel n (set es))>" by auto2

section {* Connectedness tests *}

lemma uf_cmp_correct [hoare_triple]:
  "<is_uf n (connected_rel n S) p>
   uf_cmp p i j
   <\<lambda>r. is_uf n (connected_rel n S) p * \<up>(r \<longleftrightarrow> has_path n S i j)>" by auto2

end
