theory Logic_More
imports Auto2
begin

definition THE_unique :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option" where
  "THE_unique P = (if (\<exists>!x. P x) then Some (THE x. P x) else None)"
setup {* add_rewrite_rule @{thm THE_unique_def} *}

theorem THE_uniqueI: "\<exists>!x. P x \<Longrightarrow> THE_unique P \<noteq> None \<and> P (the (THE_unique P))" by auto2
setup {* add_forward_prfstep_cond @{thm THE_uniqueI} [with_term "THE_unique ?P"] *}

theorem THE_unique_None: "\<not>(\<exists>!x. P x) \<Longrightarrow> THE_unique P = None" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_None} [with_term "THE_unique ?P"] *}

theorem THE_unique_None': "\<not>(\<exists>x. P x) \<Longrightarrow> THE_unique P = None" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_None'} [with_term "THE_unique ?P"] *}

theorem THE_unique_eq: "P a \<Longrightarrow> \<exists>!x. P x \<Longrightarrow> THE_unique P = Some a" by auto2
setup {* add_forward_prfstep_cond @{thm THE_unique_eq} [with_term "THE_unique ?P"] *}

theorem THE_uniqueD [resolve]: "THE_unique P = Some x \<Longrightarrow> P x"
  by (metis THE_unique_def option.sel option.simps(3) theI')

setup {* del_prfstep_thm @{thm THE_unique_def} *}

end
