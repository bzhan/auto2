theory Hoare_Triple
imports Run
begin

section {* Definition of hoare triple, and the frame rule. *}

text {* Analyze the heap before and after executing a command, to add
  the allocated addresses to the covered address range. *}

definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"
setup {* add_rewrite_rule @{thm new_addrs_def} *}

lemma new_addr_refl [rewrite]: "new_addrs h as h = as" by auto2

definition hoare_triple :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>") where
  "<P> c <Q> \<longleftrightarrow> (\<forall>h as \<sigma> r. (h, as) \<Turnstile> P \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs h as (the \<sigma>)) \<Turnstile> Q r \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>)))"
setup {* add_forward_prfstep (equiv_forward_th @{thm hoare_triple_def}) *}
setup {* add_resolve_prfstep (equiv_backward_th @{thm hoare_triple_def}) *}

text {* For garbage-collected languages, specifications usually allow for some
  arbitrary heap parts in the postcondition. The following abbreviation defines
  a handy shortcut notation for such specifications. *}
abbreviation hoare_triple' :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") where
  "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

lemma frame_rule [backward]:
  "<P> c <Q> \<Longrightarrow> <P * R> c <\<lambda>x. Q x * R>"
@proof
  @have "\<forall>h as \<sigma> r. (h, as) \<Turnstile> P * R \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
                    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs h as (the \<sigma>)) \<Turnstile> Q r * R \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    @obtain as1 as2 where "set_partition as as1 as2" "(h, as1) \<Turnstile> P \<and> (h, as2) \<Turnstile> R" @then
    @have "relH as2 h (the \<sigma>)" @then
    @have "set_partition (new_addrs h as (the \<sigma>)) (new_addrs h as1 (the \<sigma>)) as2" @with
      @have "\<forall>x. x \<in> as2 \<longrightarrow> x \<notin> {a. lim h \<le> a \<and> a < lim (the \<sigma>)}"
    @end
  @end
@qed

(* This is the last use of the definition of separating conjunction. *)
setup {* del_prfstep_thm @{thm mod_star_conv} *}
setup {* del_prfstep_thm_str "@eqbackward@res" @{thm hoare_triple_def} *}

section {* Hoare triples for atomic commands *}

setup {* add_backward_prfstep (equiv_backward_th @{thm hoare_triple_def}) *}

(* First, those that do not modify the heap. *)

(* Avoid variables P and Q since they are pre- and post-condition. *)
lemma comment_rule:
  "<R> comment R <\<lambda>r. R>" by auto2

lemma comment_rule2:
  "<R x> comment (\<exists>\<^sub>Ax. R x) <\<lambda>r. R x>" by auto2

lemma assert_rule:
  "<\<up>(R x)> assert R x <\<lambda>r. \<up>(r = x)>" by auto2

lemma return_rule:
  "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

lemma nth_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>" by auto2

lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>" by auto2

lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2

(* Next, the update rules. *)
setup {* add_rewrite_rule @{thm Ref.lim_set} *}
theorem Array_lim_set [rewrite]: "lim (Array.set p xs h) = lim h" by (simp add: Array.set_def)

setup {* fold add_rewrite_rule [@{thm Ref.get_set_eq}, @{thm Array.get_set_eq}] *}
setup {* add_rewrite_rule @{thm Array.update_def} *}

lemma upd_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a list_update xs i x * \<up>(r = a)>" by auto2

lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>" by auto2

(* Finally, the allocation rules. *)
theorem lim_set_gen [rewrite]: "lim (h\<lparr>lim := l\<rparr>) = l" by simp

theorem Array_alloc_def' [rewrite]: 
  "Array.alloc xs h = (let l = lim h; r = Array l in (r, (Array.set r xs (h\<lparr>lim := l + 1\<rparr>))))"
  by (simp add: Array.alloc_def)

setup {* fold add_rewrite_rule [
  @{thm addr_of_array.simps}, @{thm addr_of_ref.simps}, @{thm Ref.alloc_def}] *}

theorem refs_on_Array_set [rewrite]: "refs (Array.set p xs h) t i = refs h t i"
  by (simp add: Array.set_def)

theorem arrays_on_Ref_set [rewrite]: "arrays (Ref.set p x h) t i = arrays h t i"
  by (simp add: Ref.set_def)

theorem refs_on_Array_alloc [rewrite]: "refs (snd (Array.alloc xs h)) t i = refs h t i"
  by (metis (no_types, lifting) Array.alloc_def refs_on_Array_set select_convs(2) snd_conv surjective update_convs(3))

theorem arrays_on_Ref_alloc [rewrite]: "arrays (snd (Ref.alloc x h)) t i = arrays h t i"
  by (metis (no_types, lifting) Ref.alloc_def arrays_on_Ref_set select_convs(1) sndI surjective update_convs(3))

theorem arrays_on_Array_alloc [rewrite]: "i < lim h \<Longrightarrow> arrays (snd (Array.alloc xs h)) t i = arrays h t i"
  by (smt Array.alloc_def Array.set_def addr_of_array.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less simps(1) snd_conv surjective update_convs(1) update_convs(3))

theorem refs_on_Ref_alloc [rewrite]: "i < lim h \<Longrightarrow> refs (snd (Ref.alloc x h)) t i = refs h t i"
  by (smt Ref.alloc_def Ref.set_def addr_of_ref.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less select_convs(2) simps(6) snd_conv surjective update_convs(3))

lemma new_rule:
  "<emp> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>" by auto2

lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup {* fold del_prfstep_thm [@{thm sngr_assn_rule}, @{thm snga_assn_rule}] *}

section {* Other properties *}

theorem norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2

section {* success_run and its properties. *}

theorem union_case [forward]: "x \<in> A \<union> B \<Longrightarrow> x \<in> A \<or> x \<in> B" by auto2
theorem new_addrs_bind [rewrite]: "lim h \<le> lim h' \<Longrightarrow> lim h' \<le> lim h'' \<Longrightarrow>
  new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''"
@proof @have "\<forall>x. x \<in> new_addrs h' (new_addrs h as h') h'' \<longleftrightarrow> x \<in> new_addrs h as h''" @qed
setup {* del_prfstep_thm @{thm union_case} *}

fun success_run :: "'a Heap \<Rightarrow> pheap \<Rightarrow> pheap \<Rightarrow> 'a \<Rightarrow> bool" where
  "success_run f (h, as) (h', as') r \<longleftrightarrow>
    as' = new_addrs h as h' \<and> run f (Some h) (Some h') r \<and> relH {a. a < lim h \<and> a \<notin> as} h h' \<and> lim h \<le> lim h'"
setup {* add_rewrite_rule @{thm success_run.simps} *}

theorem success_run_bind:
  "success_run f h h' r \<Longrightarrow> success_run (g r) h' h'' r' \<Longrightarrow> success_run (f \<bind> g) h h'' r'" by auto2

theorem success_run_next: "success_run f h h'' r' \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (fst h') \<and> success_run (f \<bind> g) h h' r \<longrightarrow> \<not> h' \<Turnstile> Q \<Longrightarrow>
  \<forall>h'. \<sigma> = Some (fst h') \<and> success_run (g r') h'' h' r \<longrightarrow> \<not> h' \<Turnstile> Q" by auto2

theorem hoare_triple_def' [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h \<sigma> r. h \<Turnstile> P \<longrightarrow> run c (Some (fst h)) \<sigma> r \<longrightarrow>
    (\<sigma> \<noteq> None \<and> (the \<sigma>, new_addrs (fst h) (snd h) (the \<sigma>)) \<Turnstile> Q r \<and> relH {a . a < lim (fst h) \<and> a \<notin> (snd h)} (fst h) (the \<sigma>) \<and>
     lim (fst h) \<le> lim (the \<sigma>)))" using hoare_triple_def by fastforce

theorem hoare_tripleE': "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run c (Some (fst h)) \<sigma> r \<Longrightarrow>
  \<exists>h'. h' \<Turnstile> Q r * Ru \<and> \<sigma> = Some (fst h') \<and> success_run c h h' r"
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

theorem hoare_tripleI: "\<not><P> c <Q> \<Longrightarrow> \<exists>h \<sigma> r. h \<Turnstile> P \<and> run c (Some (fst h)) \<sigma> r \<and>
  (\<forall>h'. \<sigma> = Some (fst h') \<and> success_run c h h' r \<longrightarrow> \<not>h' \<Turnstile> Q r)" by auto2

theorem hoare_triple_mp: "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> success_run c h h' r \<Longrightarrow> h' \<Turnstile> (Q r) * Ru"
@proof @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @qed

theorem hoare_tripleE'': "<P> c <Q> \<Longrightarrow> h \<Turnstile> P * Ru \<Longrightarrow> run (c \<bind> g) (Some (fst h)) \<sigma> r \<Longrightarrow>
  \<exists>r' h'. run (g r') (Some (fst h')) \<sigma> r \<and> h' \<Turnstile> Q r' * Ru \<and> success_run c h h' r'"
@proof
  @have "<P * Ru> c <\<lambda>r. Q r * Ru>" @then
  @obtain \<sigma>' r' where "run c (Some (fst h)) \<sigma>' r'"
@qed

definition heap_preserving :: "'a Heap \<Rightarrow> bool" where
  "heap_preserving c = (\<forall>h h' r. effect c h h' r \<longrightarrow> h = h')"
setup {* add_rewrite_rule @{thm heap_preserving_def} *}

setup {* add_forward_prfstep @{thm effectI} *}

theorem heap_preservingD [forward]:
  "heap_preserving c \<Longrightarrow> success_run c h h' r \<Longrightarrow> h = h'" by auto2

theorem heap_preserving_effectD:
  "heap_preserving c \<Longrightarrow> effect c h h' r \<Longrightarrow> h = h'" by auto2

theorem effect_bind [forward]: "effect (f \<bind> g) h h'' r' \<Longrightarrow> \<exists>h' r. effect f h h' r \<and> effect (g r) h' h'' r'"
  by (elim effect_elims) auto

theorem hoare_tripleE'_preserve: "heap_preserving c \<Longrightarrow>
  \<exists>h'. h' \<Turnstile> Q \<and> \<sigma> = Some (fst h') \<and> success_run c h h' r \<Longrightarrow>
  h \<Turnstile> Q \<and> \<sigma> = Some (fst h) \<and> success_run c h h r" by auto2

theorem hoare_tripleE''_preserve: "heap_preserving c \<Longrightarrow>
  \<exists>r' h'. run (g r') (Some (fst h')) \<sigma> r \<and> h' \<Turnstile> Q r' * Ru \<and> success_run c h h' r' \<Longrightarrow>
  \<exists>r'. run (g r') (Some (fst h)) \<sigma> r \<and> h \<Turnstile> Q r' * Ru \<and> success_run c h h r'" by auto2

setup {* del_prfstep_thm @{thm effectI} *}
setup {* del_prfstep_thm @{thm hoare_triple_def} *}
setup {* del_prfstep_thm @{thm hoare_triple_def'} *}
setup {* del_prfstep_thm @{thm success_run.simps} *}

end
