theory Run
imports Assertions "~~/src/HOL/Imperative_HOL/Imperative_HOL"
begin

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> bool" where
  "run c None None r " |
  "execute c h = None \<Longrightarrow> run c (Some h) None r" |
  "execute c h = Some (r, h') \<Longrightarrow> run c (Some h) (Some h') r"
setup {* add_case_induct_rule @{thm run.cases} *}
setup {* fold add_resolve_prfstep @{thms run.intros(1,2)} *}
setup {* add_forward_prfstep @{thm run.intros(3)} *}

theorem run_preserve_None [forward]:
  "run c None \<sigma>' r \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c None \<sigma>' r" @qed

theorem run_execute_fail [forward]:
  "execute c h = None \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = None"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

theorem run_execute_succeed [forward]:
  "execute c h = Some (r', h') \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = Some h' \<and> r = r'"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r. run c \<sigma> \<sigma>' (r::'a)"
@proof
  @obtain "r::'a" where "r = r"
  @case "\<sigma> = None" @with @have "run c None None r" @end
  @case "execute c (the \<sigma>) = None" @with @have "run c \<sigma> None r" @end
@qed

theorem run_to_execute [forward]:
  "run c (Some h) \<sigma>' r \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>')"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

setup {* add_backward_prfstep @{thm run.intros(3)} *}

setup {* add_rewrite_rule @{thm execute_bind(1)} *}
lemma runE [forward]:
  "run f (Some h) (Some h') r' \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r \<Longrightarrow> run (g r') (Some h') \<sigma> r"
@proof @case "\<sigma> = None" @qed

setup {* add_rewrite_rule @{thm Array.get_alloc} *}
setup {* add_rewrite_rule @{thm Ref.get_alloc} *}
setup {* add_rewrite_rule_bidir @{thm Array.length_def} *}

setup {* add_rewrite_rule @{thm execute_assert(1)} *}
lemma execute_return': "execute (return x) h = Some (x, h)" by (metis comp_eq_dest_lhs execute_return)
setup {* add_rewrite_rule @{thm execute_return'} *}
setup {* add_rewrite_rule @{thm execute_len} *}
setup {* add_rewrite_rule @{thm execute_new} *}
setup {* add_rewrite_rule @{thm execute_upd(1)} *}
setup {* add_rewrite_rule @{thm execute_ref} *}
setup {* add_rewrite_rule @{thm execute_lookup} *}
setup {* add_rewrite_rule @{thm execute_nth(1)} *}
setup {* add_rewrite_rule @{thm execute_update} *}

definition comment :: "assn \<Rightarrow> unit Heap" where
  "comment P = Heap_Monad.Heap (\<lambda>h. Some ((), h))"

theorem execute_comment [rewrite]:
  "execute (comment P) h = Some ((), h)" by (simp add: comment_def)

end
