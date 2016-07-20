theory Run
imports Assertions "~~/src/HOL/Imperative_HOL/Imperative_HOL"
begin

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> bool" where
  "run c None None r " |
  "execute c h = None \<Longrightarrow> run c (Some h) None r" |
  "execute c h = Some (r, h') \<Longrightarrow> run c (Some h) (Some h') r"
setup {* add_prfstep_prop_induction @{thm run.induct} *}
setup {* fold add_resolve_prfstep @{thms run.intros(1,2)} *}
setup {* add_forward_prfstep @{thm run.intros(3)} *}

theorem run_preserve_None [forward]:
  "run c None \<sigma>' r \<Longrightarrow> \<sigma>' = None"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("run c None \<sigma>' r", [])) *})

theorem run_execute_fail [forward]:
  "execute c h = None \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = None"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("run c (Some h) \<sigma>' r", [])) *})

theorem run_execute_succeed [forward]:
  "execute c h = Some (r', h') \<Longrightarrow> run c (Some h) \<sigma>' r \<Longrightarrow> \<sigma>' = Some h' \<and> r = r'"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("run c (Some h) \<sigma>' r", [])) *})

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r. run c \<sigma> \<sigma>' (r::'a)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "r::'a, ArbVar r" THEN
     CASE "\<sigma> = None" WITH OBTAIN "run c None None r" THEN
     CASE "execute c (the \<sigma>) = None" WITH OBTAIN "run c \<sigma> None r") *})

theorem run_execute_none [forward]: "run c (Some h) None r \<Longrightarrow> execute c h = None"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("run c (Some h) None r", [])) *})

theorem run_execute_some [forward]: "run c (Some h) (Some h') r \<Longrightarrow> execute c h = Some (r, h')"
  by (tactic {* auto2s_tac @{context} (PROP_INDUCT ("run c (Some h) (Some h') r", [])) *})
setup {* add_backward_prfstep @{thm run.intros(3)} *}

setup {* add_rewrite_rule @{thm execute_bind(1)} *}
lemma runE [forward]:
  "run f (Some h) (Some h') r' \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r \<Longrightarrow> run (g r') (Some h') \<sigma> r"
  by (tactic {* auto2s_tac @{context} (CASE "\<sigma> = None") *})

setup {* add_rewrite_rule @{thm Array.get_alloc} *}
setup {* add_rewrite_rule @{thm Ref.get_alloc} *}
setup {* add_rewrite_rule_bidir @{thm Array.length_def} *}

lemma execute_return': "execute (return x) h = Some (x, h)" by (metis comp_eq_dest_lhs execute_return)
setup {* add_forward_prfstep_cond @{thm execute_return'} [with_term "run (return ?x) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_len} [with_term "run (Array.len ?a) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_new} [with_term "run (Array.new ?n ?x) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_upd(1)} [with_term "run (Array.upd ?i ?x ?a) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_ref} [with_term "run (ref ?v) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_lookup} [with_term "run (!?r) (Some ?h) ?\<sigma>' ?r'"] *}
setup {* add_forward_prfstep_cond @{thm execute_nth(1)} [with_term "run (Array.nth ?a ?i) (Some ?h) ?\<sigma>' ?r"] *}
setup {* add_forward_prfstep_cond @{thm execute_update} [with_term "run (?r := ?v) (Some ?h) ?\<sigma>' ?r'"] *}

end
