theory Set_Thms
imports Auto2_Base "~~/src/HOL/Library/Multiset"
begin

(* Set *)
thm Set.mem_Collect_eq
setup {* add_prfstep_conv ("collect_eq",
  [WithTerm @{term_pat "?a \<in> {x. ?P}"}],
  (rewr_obj_eq @{thm Set.mem_Collect_eq})) *}

theorem Max_ge': "finite A \<Longrightarrow> x > Max A \<Longrightarrow> \<not>(x \<in> A)" using Max_ge leD by auto
setup {* add_forward_prfstep @{thm Max_ge'} *}

setup {* add_rewrite_rule @{thm Ball_def} *}
setup {* add_forward_prfstep @{thm Set.singletonD} *}
setup {* add_forward_prfstep (equiv_forward_th @{thm Set.empty_iff}) *}
setup {* add_rewrite_rule @{thm Un_iff} *}

(* Multiset *)

(* set_of *)
setup {* add_rewrite_rule @{thm set_of_empty} *}
setup {* add_rewrite_rule @{thm set_of_single} *}
setup {* add_rewrite_rule @{thm set_of_union} *}

(* image_mset *)
setup {* add_rewrite_rule @{thm image_mset_empty} *}
setup {* add_rewrite_rule @{thm image_mset_single} *}
setup {* add_rewrite_rule @{thm image_mset_union} *}

(* mset_prod *)
setup {* add_rewrite_rule @{thm msetprod_empty} *}
setup {* add_rewrite_rule @{thm msetprod_singleton} *}
setup {* add_rewrite_rule @{thm msetprod_Un} *}

(* Case checking. *)
setup {* add_resolve_prfstep @{thm multi_nonempty_split} *}

(* Membership and ordering. *)
theorem multiset_antisym: "M \<subseteq># N \<Longrightarrow> N \<subseteq># M \<Longrightarrow> M = N" by simp
setup {* add_backward2_prfstep @{thm multiset_antisym} *}
setup {* add_resolve_prfstep @{thm Multiset.empty_le} *}
setup {* add_forward_prfstep @{thm mset_lessD} *}
setup {* add_backward_prfstep @{thm Multiset.multi_member_split} *}
setup {* add_forward_prfstep_cond @{thm multi_psub_of_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_contain_add_self: "x \<in># A + {#x#}" by simp
setup {* add_forward_prfstep_cond @{thm multi_contain_add_self} [with_term "?A + {#?x#}"] *}
theorem multi_add_right: "M \<subseteq># N \<Longrightarrow> M + {#x#} \<subseteq># N + {#x#}" by simp
setup {* add_resolve_prfstep @{thm multi_add_right} *}
theorem multi_Ball_mono': "M \<subset># N \<Longrightarrow> \<forall>x\<in>set_of N. P x \<Longrightarrow> \<forall>x\<in>set_of M. P x" by (meson mem_set_of_iff mset_lessD)
setup {* add_prfstep_thm ("multi_Ball_mono'",
  [WithFact @{term_pat "?M \<subset># ?N"},
   WithFact @{term_pat "\<forall>x\<in>set_of ?N. ?P"}],
  @{thm multi_Ball_mono'}) *}
setup {* add_prfstep_conv ("ball_set_of_iff", [WithTerm @{term_pat "\<forall>x\<in>set_of ?M. ?P"}],
  (rewr_obj_eq @{thm Multiset.ball_set_of_iff})) *}

(* Induction. *)
setup {* add_prfstep_strong_induction @{thm full_multiset_induct} *}

end
