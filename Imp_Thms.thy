theory Imp_Thms
imports Auto2 Lists_Thms "~~/src/HOL/Imperative_HOL/Imperative_HOL"
  "~~/src/HOL/Imperative_HOL/ex/Subarray"
begin

(* Basic *)
setup {* fold add_forward_prfstep @{thms effect_deterministic} *}

definition present_on_set :: "heap \<Rightarrow> ('a::heap) ref set \<Rightarrow> bool" where
  "present_on_set h rs \<longleftrightarrow> (\<forall>ref \<in> rs. Ref.present h ref)"
setup {* add_rewrite_rule @{thm present_on_set_def} *}
theorem present_on_set_single: "present_on_set h {r} \<Longrightarrow> Ref.present h r" by auto2
theorem present_on_set_mp: "present_on_set h rs \<Longrightarrow> r \<in> rs \<Longrightarrow> Ref.present h r" by auto2
theorem present_on_set_mp': "present_on_set h rs \<Longrightarrow> \<not>Ref.present h r \<Longrightarrow> r \<notin> rs" by auto2
setup {* del_prfstep_thm @{thm present_on_set_def} #> add_backward_prfstep (equiv_backward_th @{thm present_on_set_def}) *}
setup {* fold add_forward_prfstep [@{thm present_on_set_single}, @{thm present_on_set_mp}, @{thm present_on_set_mp'}] *}

definition eq_on_set :: "heap \<Rightarrow> heap \<Rightarrow> ('a::heap) ref set \<Rightarrow> bool" where
  "eq_on_set h h' rs \<longleftrightarrow> (present_on_set h rs \<and> present_on_set h' rs) \<and> (\<forall>ref \<in> rs. Ref.get h ref = Ref.get h' ref)"
setup {* add_rewrite_rule @{thm eq_on_set_def} *}
theorem eq_on_set_single: "eq_on_set h h' {r} \<Longrightarrow> Ref.get h r = Ref.get h' r" by auto2
theorem eq_on_set_mp: "eq_on_set h h' rs \<Longrightarrow> r \<in> rs \<Longrightarrow> Ref.get h r = Ref.get h' r" by auto2
theorem eq_on_set_mp': "eq_on_set h h' rs \<Longrightarrow> Ref.get h r \<noteq> Ref.get h' r \<Longrightarrow> r \<notin> rs" by auto2
setup {* del_prfstep_thm @{thm eq_on_set_def} #> add_backward_prfstep (equiv_backward_th @{thm eq_on_set_def}) *}
setup {* add_forward_prfstep (conj_left_th (equiv_forward_th @{thm eq_on_set_def})) *}
setup {* fold add_forward_prfstep [@{thm eq_on_set_single}, @{thm eq_on_set_mp}, @{thm eq_on_set_mp'}] *}

definition not_present_on_set :: "heap \<Rightarrow> ('a::heap) ref set \<Rightarrow> bool" where
  "not_present_on_set h rs = (\<forall>ref \<in> rs. \<not>Ref.present h ref)"
setup {* add_rewrite_rule_bidir @{thm not_present_on_set_def} *}

theorem neq_from_present: "Ref.present h p \<Longrightarrow> \<not>Ref.present h q \<Longrightarrow> p \<noteq> q" by auto2
setup {* add_forward_prfstep @{thm neq_from_present} *}
theorem not_in_from_present: "Ref.present h p \<Longrightarrow> not_present_on_set h qs \<Longrightarrow> p \<notin> qs" by auto2
theorem not_in_from_present': "\<not>Ref.present h p \<Longrightarrow> present_on_set h qs \<Longrightarrow> p \<notin> qs" by auto2
setup {* fold add_forward_prfstep [@{thm not_in_from_present}, @{thm not_in_from_present'}] *}
theorem disjoint_from_present: "present_on_set h rs \<Longrightarrow> not_present_on_set h rs' \<Longrightarrow> rs \<inter> rs' = {}"
  by (tactic {* auto2s_tac @{context} (OBTAIN "\<forall>r. r \<in> rs \<longrightarrow> r \<notin> rs'") *})
setup {* add_forward_prfstep @{thm disjoint_from_present} *}

theorem success_to_effect: "success f h \<Longrightarrow> \<exists>h' r. effect f h h' r" using success_effectE by blast
theorem success_to_effect_unit: "success (f::unit Heap) h \<Longrightarrow> \<exists>h'. effect f h h' ()" using success_to_effect by fastforce
theorem success_to_effect_same:
  "(\<forall>h' r. effect f h h' r \<longrightarrow> h = h') \<Longrightarrow> success f h \<Longrightarrow> \<exists>r. effect f h h r" using success_to_effect by blast
theorem success_to_effect_same_unit:
  "(\<forall>h' r. effect f h h' r \<longrightarrow> h = h') \<Longrightarrow> success (f::unit Heap) h \<Longrightarrow> effect f h h ()" using success_to_effect_unit by blast

setup {* add_gen_prfstep ("effect_to_success_goal_intro",
  [WithGoal @{term_pat "effect ?f ?h ?h' ?r"},
   CreateCase ([], [@{term_pat "success ?f ?h"}])]) *}

setup {* add_prfstep_thm_fn ("use_success_to_effect",
  [WithFact @{term_pat "success ?f ?h"},
   WithGoal @{term_pat "effect ?f ?h ?h' ?r"}],
  [Update.ADD_ITEMS],
  (fn _ => fn ((_, inst), ths) => (hd ths) RS @{thm success_to_effect})) *}

(* present extension *)
definition present_extension :: "heap \<Rightarrow> heap \<Rightarrow> bool" where
  "present_extension h h' \<longleftrightarrow> lim h' \<ge> lim h"
theorem present_extension_ref: "present_extension h h' \<Longrightarrow> Ref.present h q \<Longrightarrow> Ref.present h' q"
  by (simp add: Ref.present_def present_extension_def)
theorem present_extension_refs: "present_extension h h' \<Longrightarrow> present_on_set h rs \<Longrightarrow> present_on_set h' rs"
  by (simp add: present_extension_ref present_on_set_def)
theorem present_extension_trans: "present_extension h h' \<Longrightarrow> present_extension h' h'' \<Longrightarrow> present_extension h h''"
  using le_trans present_extension_def by blast
theorem present_extension_refl: "present_extension h h"
  by (simp add: present_extension_def)
setup {* fold add_forward_prfstep [@{thm present_extension_ref}, @{thm present_extension_refs}] *}
setup {* add_backward2_prfstep @{thm present_extension_trans} *}
setup {* add_resolve_prfstep @{thm present_extension_refl} *}

(* Unchanged outer *)
definition unchanged_outer :: "heap \<Rightarrow> heap \<Rightarrow> ('a::heap) ref set \<Rightarrow> bool" where
  "unchanged_outer h h' rs \<longleftrightarrow> present_extension h h' \<and> (\<forall>r. r \<notin> rs \<longrightarrow> Ref.present h r \<longrightarrow> Ref.get h r = Ref.get h' r)"
setup {* add_rewrite_rule @{thm unchanged_outer_def} *}
theorem unchanged_outer_ref: "unchanged_outer h h' rs \<Longrightarrow> r \<notin> rs \<Longrightarrow> Ref.present h r \<Longrightarrow> Ref.get h r = Ref.get h' r" by auto2
theorem unchanged_outer_refs: "unchanged_outer h h' rs \<Longrightarrow> rs' \<inter> rs = {} \<Longrightarrow> present_on_set h rs' \<Longrightarrow> eq_on_set h h' rs'" by auto2
setup {* del_prfstep_thm @{thm unchanged_outer_def}
  #> add_forward_prfstep (conj_left_th (equiv_forward_th @{thm unchanged_outer_def}))
  #> add_backward_prfstep (equiv_backward_th @{thm unchanged_outer_def})
  #> fold add_forward_prfstep [@{thm unchanged_outer_ref}, @{thm unchanged_outer_refs}] *}

(* refs_of_extension *)
definition refs_of_extension :: "heap \<Rightarrow> 'a::heap ref set \<Rightarrow> 'a::heap ref set \<Rightarrow> bool" where
  "refs_of_extension h ps ps' = (\<forall>r \<in> ps'. \<not> Ref.present h r \<or> r \<in> ps)"
setup {* add_rewrite_rule @{thm refs_of_extension_def} *}

theorem not_in_extension: "refs_of_extension h ps ps' \<Longrightarrow> q \<notin> ps \<Longrightarrow> Ref.present h q \<Longrightarrow> q \<notin> ps'" by auto2
theorem disjoint_extension:
  "refs_of_extension h ps ps' \<Longrightarrow> qs \<inter> ps = {} \<Longrightarrow> present_on_set h qs \<Longrightarrow> qs \<inter> ps' = {}"
  by (tactic {* auto2s_tac @{context} (OBTAIN "\<forall>q\<in>qs. q \<notin> ps'") *})
setup {* fold add_forward_prfstep [@{thm not_in_extension}, @{thm disjoint_extension}] *}
setup {* del_prfstep_thm @{thm refs_of_extension_def}
  #> add_backward_prfstep (equiv_backward_th @{thm refs_of_extension_def}) *}

(* Comments *)
definition comment :: "(heap \<Rightarrow> bool) \<Rightarrow> unit Heap" where
  "comment P = Heap_Monad.Heap (\<lambda>h. if P h then Some ((), h) else None)"
theorem success_comment: "P h \<Longrightarrow> success (comment P) h" by (simp add: comment_def successI)
setup {* add_backward_prfstep @{thm success_comment} *}
theorem effect_comment: "effect (comment P) h h' r \<Longrightarrow> h = h' \<and> P h" by (smt comment_def effectE effect_def execute.simps option.distinct(2))
setup {* add_forward_prfstep @{thm effect_comment} *}

(* Assert *)
setup {* add_backward_prfstep @{thm success_assertI} *}
theorem effect_assert: "effect (assert P x) h h' r \<Longrightarrow> h = h' \<and> P x \<and> r = x" using effect_assertE by fastforce
setup {* add_forward_prfstep @{thm effect_assert} *}

(* Raise *)
theorem effect_raise: "\<not>effect (raise x) h h' r" by (meson effect_raiseE)
setup {* add_resolve_prfstep @{thm effect_raise} *}

(* Bind *)
setup {* add_gen_prfstep ("success_bind_first",
  [WithGoal @{term_pat "success ((?f::?'a Heap) \<guillemotright>= ?g) ?h"},
   CreateCase ([], [@{term_pat "success (?f::?'a Heap) ?h"}])])
*}

setup {* add_backward2_prfstep @{thm success_bind_effectI} *}

theorem effect_bind: "effect (f \<guillemotright>= g) h h'' r' \<Longrightarrow> \<exists>h' r. effect f h h' r \<and> effect (g r) h' h'' r'"
  by (elim effect_elims) auto

theorem effect_bind_unit: "effect ((f::unit Heap) \<guillemotright>= g) h h'' r' \<Longrightarrow> \<exists>h'. effect f h h' () \<and> effect (g ()) h' h'' r'"
  by (elim effect_elims) auto

theorem effect_bind_same:
  "(\<forall>h' r. effect f h h' r \<longrightarrow> h = h') \<Longrightarrow> effect (f \<guillemotright>= g) h h'' r' \<Longrightarrow> \<exists>r. effect f h h r \<and> effect (g r) h h'' r'"
  using effect_bind by force

theorem effect_bind_same_unit:
  "(\<forall>h' r. effect f h h' r \<longrightarrow> h = h') \<Longrightarrow> effect ((f::unit Heap) \<guillemotright>= g) h h'' r' \<Longrightarrow> effect f h h () \<and> effect (g ()) h h'' r'"
  using effect_bind_unit by force

setup {* add_backward2_prfstep @{thm effect_bindI} *}

(* ref (allocation of memory) *)
lemma effect_ref: "effect (ref v) h h' x \<Longrightarrow> Ref.get h' x = v \<and> \<not> Ref.present h x \<and> Ref.present h' x"
  using effect_refE by blast
lemma effect_ref_get: "effect (ref v) h h' x \<Longrightarrow> Ref.present h y \<Longrightarrow> Ref.get h y = Ref.get h' y \<and> Ref.present h' y"
  by (metis Ref.present_alloc effect_heapE effect_refE get_alloc_neq noteq_I ref_def)
lemma effect_ref_present_extension: "effect (ref v) h h' x \<Longrightarrow> present_extension h h'"
  by (meson Ref.present_def effect_ref linorder_not_le order_less_trans present_extension_def)
setup {* fold add_forward_prfstep [@{thm effect_ref}, @{thm effect_ref_get}, @{thm effect_ref_present_extension}] #>
  add_backward2_prfstep (conj_right_th @{thm effect_ref_get}) *}

theorem effect_ref_present_inv: "effect (ref v) h h' x \<Longrightarrow> present_on_set h rs \<Longrightarrow> present_on_set h' rs" by auto2
theorem effect_ref_eq_inv: "effect (ref v) h h' x \<Longrightarrow> present_on_set h rs \<Longrightarrow> eq_on_set h h' rs" by auto2
theorem effect_ref_not_present_inv: "effect (ref v) h h' x \<Longrightarrow> not_present_on_set h' rs \<Longrightarrow> not_present_on_set h rs" by auto2
setup {* fold add_forward_prfstep
  [@{thm effect_ref_present_inv}, @{thm effect_ref_eq_inv}, @{thm effect_ref_not_present_inv}] *}

setup {* add_resolve_prfstep @{thm success_refI} *}

(* return *)
setup {* add_resolve_prfstep @{thm success_returnI} *}
theorem effect_return: "effect (return x) h h' x' \<Longrightarrow> h = h' \<and> x = x'"
  by (elim effect_elims) auto
setup {* add_forward_prfstep @{thm effect_return} *}
theorem effect_returnI': "effect (return x) h h x" by (intro effect_intros) auto
setup {* add_resolve_prfstep @{thm effect_returnI'} *}

(* lookup *)
theorem effect_lookup: "effect (!v) h h' r \<Longrightarrow> h = h' \<and> r = Ref.get h v"
  by (elim effect_elims) auto
setup {* add_forward_prfstep @{thm effect_lookup} *}

setup {* add_resolve_prfstep @{thm success_lookupI} *}

(* update *)
setup {* add_forward_prfstep_cond @{thm Ref.get_set_eq} [with_term "Ref.set ?r ?x ?h"] *}
theorem Ref_get_set_neq': "r \<noteq> s \<Longrightarrow> Ref.get (Ref.set s x h) r = Ref.get h r" by simp
setup {* add_forward_prfstep_cond @{thm Ref_get_set_neq'} [with_term "Ref.set ?s ?x ?h"] *}
setup {* add_backward_prfstep @{thm Ref_get_set_neq'} *}

lemma effect_update: "effect (p := v) h h' r \<Longrightarrow> h' = Ref.set p v h" by (auto elim: effect_elims)
lemma effect_update_present_extension: "h' = Ref.set p v h \<Longrightarrow> present_extension h h'"
  by (metis lim_set order_refl present_extension_def)
setup {* fold add_forward_prfstep [@{thm effect_update}, @{thm effect_update_present_extension}] *}

lemma effect_update_eq_set:
  "effect (p := v) h h' r \<Longrightarrow> p \<notin> rs \<Longrightarrow> present_on_set h rs \<Longrightarrow> eq_on_set h h' rs" by auto2
setup {* add_forward_prfstep @{thm effect_update_eq_set} *}

setup {* add_resolve_prfstep @{thm success_updateI} *}

(* Outer remains on arrays. *)
definition outer_remains :: "heap \<Rightarrow> heap \<Rightarrow> ('a::heap) array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "outer_remains h h' a l r = (Array.length h a = Array.length h' a \<and>
  (\<forall>i. i < l \<or> r < i \<longrightarrow> Array.get h a ! i = Array.get h' a ! i))"
setup {* add_rewrite_rule @{thm outer_remains_def} *}

theorem outer_remains_mp_left: "outer_remains h h' a l r \<Longrightarrow> i < l \<Longrightarrow> Array.get h a ! i = Array.get h' a ! i" by auto2
theorem outer_remains_mp_right: "outer_remains h h' a l r \<Longrightarrow> r < i \<Longrightarrow> Array.get h a ! i = Array.get h' a ! i" by auto2
setup {* fold add_forward_prfstep [@{thm outer_remains_mp_left}, @{thm outer_remains_mp_right}] *}
setup {* fold add_backward2_prfstep [@{thm outer_remains_mp_left}, @{thm outer_remains_mp_right}] *}
setup {* del_prfstep_thm @{thm outer_remains_def} #> add_backward_prfstep (equiv_backward_th @{thm outer_remains_def})
  #> add_forward_prfstep (conj_left_th (equiv_forward_th @{thm outer_remains_def})) *}

(* Other commands. *)
setup {* add_backward_prfstep @{thm success_nthI} *}
theorem effect_nth: "effect (Array.nth a i) h h' r \<Longrightarrow> h = h' \<and> i < Array.length h a \<and> r = Array.get h a ! i"
  by (elim effect_elims) auto
setup {* add_forward_prfstep @{thm effect_nth} *}

setup {* add_backward_prfstep @{thm success_updI} *}
theorem effect_upd: "effect (Array.upd i v a) h h' r \<Longrightarrow> r = a \<and> h' = Array.update a i v h \<and> i < Array.length h a"
  by (elim effect_elims) auto
setup {* add_forward_prfstep @{thm effect_upd} *}

setup {* add_rewrite_rule @{thm get_update_eq} *}

theorem Array_get_update:
  "j < Array.length h a \<Longrightarrow> Array.get (Array.update a j v h) a ! i = (if i = j then v else Array.get h a ! i)"
by (simp add: length_def)
setup {* add_rewrite_rule @{thm Array_get_update} *}

theorem Array_length_update:
  "Array.length (Array.update b i v h) a = Array.length h a" by simp
setup {* add_rewrite_rule @{thm Array_length_update} *}

setup {* add_rewrite_rule_bidir @{thm Array.length_def} *}

(* Subarray and sublists. *)
setup {* add_backward2_prfstep (equiv_backward_th @{thm subarray_eq_samelength_iff}) *}
setup {* add_rewrite_rule (to_obj_eq_th @{thm subarray_def}) *}
setup {* add_rewrite_rule @{thm length_sublist'} *}
setup {* add_rewrite_rule @{thm nth_sublist'} *}
theorem nth_rev_sublist'_use: "k < j - i \<Longrightarrow> j \<le> length xs \<Longrightarrow> sublist' i j xs ! (length (sublist' i j xs) - 1 - k) = xs ! (j - 1 - k)"
  by (simp add: length_sublist' nth_sublist')
setup {* add_rewrite_rule @{thm nth_rev_sublist'_use} *}

theorem sublist_as_Cons: "l < r \<and> r \<le> length xs \<Longrightarrow> sublist' l r xs = xs ! l # sublist' (l + 1) r xs"
  by (metis One_nat_def add.right_neutral add_Suc_right order_less_trans sublist'_front le_neq_implies_less)
theorem sublist_as_append: "l \<le> m \<and> m \<le> r \<Longrightarrow> sublist' l r xs = sublist' l m xs @ sublist' m r xs"
  by (simp add: sublist'_append)
setup {* add_backward_prfstep @{thm sublist_as_Cons} *}
setup {* add_backward_prfstep @{thm sublist_as_append} *}

(* An result about sortedness of trivial sublists. *)
theorem sublist'_single': "n < length xs \<Longrightarrow> sublist' n (n + 1) xs = [xs ! n]" using sublist'_single by simp
setup {* fold add_rewrite_rule [@{thm sublist'_Nil'}, @{thm sublist'_single'}, @{thm sublist'_Nil2}] *}
theorem sorted_triv_list: "l \<ge> r \<Longrightarrow> sorted (sublist' l (1 + r) xs)"
  by (tactic {* auto2s_tac @{context} (CASE "l \<ge> length xs" THEN CASE "l = r" THEN OBTAIN "l > r") *})
setup {* add_known_fact @{thm sorted_triv_list} *}
(* Some results about sets and multisets of sublists. *)
setup {* add_rewrite_rule @{thm set_sublist'} *}

theorem multiset_of_sublist':
  "r \<le> List.length xs \<and> (\<forall>i. i < l \<longrightarrow> xs ! i = ys ! i) \<and> (\<forall>i. i \<ge> r \<longrightarrow> xs ! i = ys ! i) \<Longrightarrow>
   multiset_of xs = multiset_of ys \<Longrightarrow> multiset_of (sublist' l r xs) = multiset_of (sublist' l r ys)"
by (smt le_less_trans multiset_of_eq_length multiset_of_sublist nat_less_le sublist'_eq_samelength_iff)
setup {* add_backward1_prfstep @{thm multiset_of_sublist'} *}

ML_file "imp_steps.ML"

end
