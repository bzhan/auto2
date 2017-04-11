theory Partial_Object
imports Prelim_Thms Feval
begin

(* Use only in this theory *)
setup {* add_rewrite_rule @{thm inj_on_def} *}
setup {* add_rewrite_rule @{thm feval_def} *}
setup {* add_backward_prfstep @{thm set_ext} *}

subsection \<open>Partial objects\<close>

record 'a partial_object =
  carrier :: "'a set"

definition struct_subset :: "_ \<Rightarrow> 'a set \<Rightarrow> bool"  ("subset\<index> _" [81] 80) where
  "subset\<^bsub>G\<^esub> H \<longleftrightarrow> (\<forall>x\<in>H. x \<in> carrier G)"
setup {* add_backward_prfstep (equiv_backward_th @{thm struct_subset_def}) *}

theorem struct_subsetE [forward]: "subset\<^bsub>G\<^esub> H \<Longrightarrow> x \<in> H \<Longrightarrow> x \<in> carrier G"
  by (simp add: struct_subset_def)

definition struct_compose :: "_ \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'c" (infixr "\<circ>\<index>" 55) where
  "i \<circ>\<^bsub>G\<^esub> h = compose (carrier G) i h"
setup {* add_rewrite_rule @{thm struct_compose_def} *}

theorem struct_compose_eq [rewrite]: "x \<in> carrier G \<Longrightarrow> (g \<circ>\<^bsub>G\<^esub> f)\<langle>x\<rangle> = g\<langle>f\<langle>x\<rangle>\<rangle>" by auto2

definition struct_is_inj :: "_ \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool"  ("is'_inj\<index> _" [81] 80) where
  "is_inj\<^bsub>G\<^esub> h \<longleftrightarrow> inj_on h (carrier G)"
setup {* add_rewrite_rule_bidir @{thm struct_is_inj_def} *}

definition struct_is_surj :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" ("is'_surj\<index> _ _" [81, 80] 80) where
  "is_surj\<^bsub>G\<^esub> H h \<longleftrightarrow> h ` carrier G = carrier H"
setup {* add_rewrite_rule_bidir @{thm struct_is_surj_def} *}

theorem struct_is_inj_def': "is_inj\<^bsub>G\<^esub> h \<longleftrightarrow> (\<forall>x y. x \<in> carrier G \<longrightarrow> y \<in> carrier G \<longrightarrow> h\<langle>x\<rangle> = h\<langle>y\<rangle> \<longrightarrow> x = y)" by auto2
setup {* add_forward_prfstep (equiv_backward_th @{thm struct_is_inj_def'}) *}

definition struct_image :: "_ \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set"  ("image\<index> _" [81] 80) where
  "image\<^bsub>G\<^esub> h = {y. \<exists>x. x \<in> carrier G \<and> h\<langle>x\<rangle> = y}"
setup {* add_rewrite_rule @{thm struct_image_def} *}

theorem struct_is_surj_image_def: fixes G (structure) shows
  "is_surj H h \<longleftrightarrow> (\<forall>x. x \<in> carrier G \<longrightarrow> h\<langle>x\<rangle> \<in> carrier H) \<and> image h = carrier H" by auto2
setup {* add_backward_prfstep (equiv_backward_th @{thm struct_is_surj_image_def}) *}
setup {* add_forward_prfstep (conj_right_th (equiv_forward_th @{thm struct_is_surj_image_def})) *}

theorem mem_imageI: "h\<langle>x\<rangle> = y \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> image\<^bsub>G\<^esub> h" by auto2
setup {* add_forward_prfstep_cond @{thm mem_imageI} [with_term "image\<^bsub>?G\<^esub> ?h"] *}

theorem mem_imageD [forward]: "y \<in> image\<^bsub>G\<^esub> h \<Longrightarrow> \<exists>x. x \<in> carrier G \<and> h\<langle>x\<rangle> = y" by auto2

definition struct_is_bij :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "struct_is_bij G H h \<longleftrightarrow> is_inj\<^bsub>G\<^esub> h \<and> is_surj\<^bsub>G\<^esub> H h"
setup {* add_rewrite_rule @{thm struct_is_bij_def} *}

theorem struct_is_bij_def' [rewrite_bidir]:
  "struct_is_bij G H h \<longleftrightarrow> bij_betw h (carrier G) (carrier H)" by auto2

theorem struct_is_bijI [backward2]:
  "is_inj\<^bsub>G\<^esub> h \<Longrightarrow> is_surj\<^bsub>G\<^esub> H h \<Longrightarrow> struct_is_bij G H h" by auto2

theorem struct_is_bij_identity [resolve]: "struct_is_bij G G (\<lambda>x. x)" by auto2

theorem struct_is_bij_transitive [backward2]:
  "struct_is_bij G H f \<Longrightarrow> struct_is_bij H I g \<Longrightarrow> struct_is_bij G I (g \<circ>\<^bsub>G\<^esub> f)" by auto2

definition struct_inv_into :: "_ \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" ("inv'_fun\<index> _" [81] 80) where
  "inv_fun\<^bsub>G\<^esub> f = inv_into (carrier G) f"
setup {* add_rewrite_rule @{thm struct_inv_into_def} *}

theorem struct_inv_into_eval:
  "f\<langle>x\<rangle> = y \<Longrightarrow> is_inj\<^bsub>G\<^esub> f \<Longrightarrow> x \<in> carrier G \<Longrightarrow> (inv_fun\<^bsub>G\<^esub> f)\<langle>y\<rangle> = x" by auto2
setup {* add_forward_prfstep_cond @{thm struct_inv_into_eval} [with_term "(inv_fun\<^bsub>?G\<^esub> ?f)\<langle>?y\<rangle>"] *}

theorem struct_inv_into_mem:
  "is_surj\<^bsub>G\<^esub> H f \<Longrightarrow> x \<in> carrier H \<Longrightarrow> (inv_fun\<^bsub>G\<^esub> f)\<langle>x\<rangle> \<in> carrier G" by auto2
setup {* add_forward_prfstep_cond @{thm struct_inv_into_mem} [with_term "(inv_fun\<^bsub>?G\<^esub> ?f)\<langle>?x\<rangle>"] *}

theorem struct_bij_betw_inv_into_right' [rewrite]:
  "struct_is_bij G H f \<Longrightarrow> y \<in> carrier H \<Longrightarrow> f \<langle>(inv_fun\<^bsub>G\<^esub> f) \<langle>y\<rangle>\<rangle> = y" by auto2

theorem struct_bij_inv_fun [backward]:
  "struct_is_bij G H f \<Longrightarrow> struct_is_bij H G (inv_fun\<^bsub>G\<^esub> f)" by auto2

(* Remove proof steps added for this theory. *)
setup {* del_prfstep_thm_str "@eqforward" @{thm inj_on_def} *}
setup {* del_prfstep_thm_str "" @{thm feval_def} *}
setup {* del_prfstep_thm_str "@back" @{thm set_ext} *}

(* Remove part of definition of struct_elt and strict_is_bij. *)
setup {* del_prfstep_thm_str "@invbackward" @{thm struct_is_bij_def} *}

(* Remove all uses of definition of several other theorems. *)
setup {* fold del_prfstep_thm [
  @{thm struct_compose_def},
  @{thm struct_is_inj_def}, @{thm struct_is_surj_def},
  @{thm struct_is_bij_def'}, @{thm struct_inv_into_def}]
*}

end
