theory Union_Find_Impl
imports "../DataStrs/Union_Find" SepAuto
begin

type_synonym uf = "nat array \<times> nat array"
  
definition is_uf :: "nat \<Rightarrow> (nat\<times>nat) set \<Rightarrow> uf \<Rightarrow> assn" where
  "is_uf n R u = (\<exists>\<^sub>Al szl. snd u \<mapsto>\<^sub>a l * fst u \<mapsto>\<^sub>a szl *
        \<up>(ufa_invar l \<and> ufa_\<alpha> l = R \<and> length l = n \<and> length szl = n))"
setup {* add_rewrite_ent_rule @{thm is_uf_def} *}

definition uf_init :: "nat \<Rightarrow> uf Heap" where [sep_proc_defs]:
  "uf_init n = do {
     l \<leftarrow> Array.of_list [0..<n];
     szl \<leftarrow> Array.new n (1::nat);
     return (szl, l)
   }"

lemma uf_init_rule [hoare_triple]:
  "<emp> uf_init n <is_uf n (uf_init_rel n)>" by auto2
declare uf_init_def [sep_proc_defs del]
  
partial_function (heap) uf_rep_of :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where
  "uf_rep_of p i = do {
     n \<leftarrow> Array.nth p i;
     if n = i then return i else uf_rep_of p n
   }"
declare uf_rep_of.simps [sep_proc_defs]
  
lemma uf_rep_of_rule [hoare_triple]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow>
   <p \<mapsto>\<^sub>a l>
   uf_rep_of p i
   <\<lambda>r. p \<mapsto>\<^sub>a l * \<up>(r = rep_of l i)>"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed
declare uf_rep_of.simps [sep_proc_defs del]

partial_function (heap) uf_compress :: "nat \<Rightarrow> nat \<Rightarrow> nat array \<Rightarrow> unit Heap" where
  "uf_compress i ci p = (
    if i = ci then return ()
    else do {
      ni \<leftarrow> Array.nth p i;
      uf_compress ni ci p;
      Array.upd i ci p;
      return ()
    })"
declare uf_compress.simps [sep_proc_defs]

lemma uf_compress_rule [hoare_triple]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow>
   <p \<mapsto>\<^sub>a l>
   uf_compress i (rep_of l i) p
   <\<lambda>_. \<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * \<up>(ufa_invar l' \<and> length l' = length l \<and> (\<forall>i<length l. rep_of l' i = rep_of l i))>"
@proof @prop_induct "ufa_invar l \<and> i < length l" @qed
declare uf_compress.simps [sep_proc_defs del]

definition uf_rep_of_c :: "nat array \<Rightarrow> nat \<Rightarrow> nat Heap" where [sep_proc_defs]:
  "uf_rep_of_c p i = do {
    ci \<leftarrow> uf_rep_of p i;
    uf_compress i ci p;
    return ci
  }"

lemma uf_rep_of_c_rule [hoare_triple]:
  "ufa_invar l \<Longrightarrow> i < length l \<Longrightarrow>
   <p \<mapsto>\<^sub>a l>
   uf_rep_of_c p i
   <\<lambda>r. \<exists>\<^sub>Al'. p \<mapsto>\<^sub>a l' * \<up>(r = rep_of l i \<and> ufa_invar l' \<and> length l' = length l \<and>
                          (\<forall>i<length l. rep_of l' i = rep_of l i))>"
  by auto2
declare uf_rep_of_c_def [sep_proc_defs del]

definition uf_cmp :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool Heap" where [sep_proc_defs]:
  "uf_cmp u i j \<equiv> do {
    n \<leftarrow> Array.len (snd u);
    if (i\<ge>n \<or> j\<ge>n) then return False
    else do {
      ci \<leftarrow> uf_rep_of_c (snd u) i;
      cj \<leftarrow> uf_rep_of_c (snd u) j;
      return (ci = cj)
    }
  }"

lemma uf_cmp_rule [hoare_triple]:
  "<is_uf n R u>
   uf_cmp u i j
   <\<lambda>r. is_uf n R u * \<up>(r \<longleftrightarrow> (i,j)\<in>R)>" by auto2
declare uf_cmp_def [sep_proc_defs del]

definition uf_union :: "uf \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> uf Heap" where [sep_proc_defs]:
  "uf_union u i j \<equiv> do {
    ci \<leftarrow> uf_rep_of (snd u) i;
    cj \<leftarrow> uf_rep_of (snd u) j;
    if (ci = cj) then return u
    else do {
      si \<leftarrow> Array.nth (fst u) ci;
      sj \<leftarrow> Array.nth (fst u) cj;
      if si < sj then do {
        Array.upd ci cj (snd u);
        Array.upd cj (si+sj) (fst u);
        return u
      } else do { 
        Array.upd cj ci (snd u);
        Array.upd ci (si+sj) (fst u);
        return u
      }
    }
  }"

lemma uf_union_rule [hoare_triple]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow>
   <is_uf n R u>
   uf_union u i j
   <is_uf n (per_union R i j)>" by auto2
declare uf_union_def [sep_proc_defs del]

end
