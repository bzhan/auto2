(* Monoids and Groups, following HOL/Algebra/Group. *)

theory Group
imports Partial_Object
begin

subsection \<open>Monoids\<close>

record 'a monoid = "'a partial_object" +
  mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>\<index>" 70)
  one :: 'a ("\<one>\<index>")

definition monoid :: "('a, 'b) monoid_scheme \<Rightarrow> bool" where
  "monoid G \<longleftrightarrow>
    \<one>\<^bsub>G\<^esub> \<in> carrier G \<and>
    (\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. x \<otimes>\<^bsub>G\<^esub> y \<in> carrier G) \<and>
    (\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<forall>z\<in>carrier G. (x \<otimes>\<^bsub>G\<^esub> y) \<otimes>\<^bsub>G\<^esub> z = x \<otimes>\<^bsub>G\<^esub> (y \<otimes>\<^bsub>G\<^esub> z)) \<and>
    (\<forall>x\<in>carrier G. \<one>\<^bsub>G\<^esub> \<otimes>\<^bsub>G\<^esub> x = x) \<and>
    (\<forall>x\<in>carrier G. x \<otimes>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub> = x)"
setup {* add_property_const @{term "monoid"} *}
setup {* register_wellform_data ("x \<otimes>\<^bsub>G\<^esub> y", ["monoid G", "x \<in> carrier G", "y \<in> carrier G"]) *}

lemma monoid_props: fixes G (structure) shows
  "monoid G \<Longrightarrow> \<one> \<in> carrier G"
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y \<in> carrier G"
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow>
    (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z) \<and> y \<otimes> z \<in> carrier G"
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow>
    x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z \<and> x \<otimes> y \<in> carrier G"
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> \<one> \<otimes> x = x"
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> x \<otimes> \<one> = x" by (simp add: Group.monoid_def)+
setup {* add_forward_prfstep @{thm monoid_props(1)} *}
setup {* add_forward_prfstep_cond @{thm monoid_props(2)} [with_term "?x \<otimes>\<^bsub>?G\<^esub> ?y"] *}
setup {* fold add_rewrite_rule @{thms monoid_props(5-6)} *}

setup {* WfACUtil.add_wf_ac_data ("group_assoc", WfACUtil.constr_ac_info
  {assoc_l_th = @{thm monoid_props(4)}, assoc_r_th = @{thm monoid_props(3)}})
*}

lemma monoidI: fixes G (structure) shows
  "\<one> \<in> carrier G \<Longrightarrow>
   \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. x \<otimes> y \<in> carrier G \<Longrightarrow>
   \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. \<forall>z\<in>carrier G. (x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z) \<Longrightarrow>
   \<forall>x\<in>carrier G. \<one> \<otimes> x = x \<Longrightarrow>
   \<forall>x\<in>carrier G. x \<otimes> \<one> = x \<Longrightarrow>
   monoid(G)" by (simp add: monoid_def)
setup {* add_horn_clause @{thm monoidI} *}

definition Units :: "_ \<Rightarrow> 'a set" -- \<open>The set of invertible elements\<close>
  where "Units G = {x. x \<in> carrier G \<and> (\<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<and> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>)}"
setup {* add_rewrite_rule @{thm Units_def} *}

lemma Unit_closed [forward]: "x \<in> Units G \<Longrightarrow> x \<in> carrier G" by auto2

lemma Unit_exists_inv [resolve]:
  "x \<in> Units G \<Longrightarrow> \<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<and> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>" by auto2

lemma Units_exists_invl [resolve]: "x \<in> Units G \<Longrightarrow> \<exists>y\<in>carrier G. y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub>" by auto2

lemma Units_exists_invr [resolve]: "x \<in> Units G \<Longrightarrow> \<exists>y\<in>carrier G. x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>" by auto2

lemma Unit_intro [backward1, backward2]:
  "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<Longrightarrow> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub> \<Longrightarrow> x \<in> Units G" by auto2

lemma Units_one_closed: fixes G (structure) shows
  "monoid G \<Longrightarrow> \<one> \<in> Units G"
  by (tactic {* auto2s_tac @{context} (HAVE "\<one> \<otimes> \<one> = \<one>") *})

setup {* del_prfstep_thm @{thm Units_def} *}

lemma Units_m_closed: fixes G (structure) shows
  "monoid G \<Longrightarrow> x \<in> Units G \<Longrightarrow> y \<in> Units G \<Longrightarrow> x \<otimes> y \<in> Units G"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "x', x' \<in> carrier G \<and> x' \<otimes> x = \<one> \<and> x \<otimes> x' = \<one>" THEN
     CHOOSE "y', y' \<in> carrier G \<and> y' \<otimes> y = \<one> \<and> y \<otimes> y' = \<one>" THEN
     HAVE "(y' \<otimes> x') \<otimes> (x \<otimes> y) = y' \<otimes> (x' \<otimes> x) \<otimes> y" THEN
     HAVE "(x \<otimes> y) \<otimes> (y' \<otimes> x') = x \<otimes> (y \<otimes> y') \<otimes> x'") *})

definition m_inv :: "('a, 'b) monoid_scheme \<Rightarrow> 'a \<Rightarrow> 'a" ("inv\<index> _" [81] 80)
  where "inv\<^bsub>G\<^esub> x = (THE y. y \<in> carrier G \<and> y \<otimes>\<^bsub>G\<^esub> x = \<one>\<^bsub>G\<^esub> \<and> x \<otimes>\<^bsub>G\<^esub> y = \<one>\<^bsub>G\<^esub>)"
setup {* add_rewrite_rule @{thm m_inv_def} *}
setup {* register_wellform_data ("inv\<^bsub>G\<^esub> x", ["x \<in> carrier G"]) *}

lemma inv_unique [forward]: fixes G (structure) shows
  "monoid G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> y' \<in> carrier G \<Longrightarrow> y \<otimes> x = \<one> \<Longrightarrow> x \<otimes> y' = \<one> \<Longrightarrow> y = y'"
  by (tactic {* auto2s_tac @{context} (HAVE "(y \<otimes> x) \<otimes> y' = y \<otimes> (x \<otimes> y')") *})

theorem monoid_inv_prop: fixes G (structure) shows
  "monoid G \<Longrightarrow> x \<in> Units G \<Longrightarrow> inv x \<in> carrier G \<and> inv x \<otimes> x = \<one> \<and> x \<otimes> inv x = \<one>"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<exists>!y. y \<in> carrier G \<and> y \<otimes> x = \<one> \<and> x \<otimes> y = \<one>") *})
setup {* add_forward_prfstep_cond @{thm monoid_inv_prop} [with_term "inv\<^bsub>?G\<^esub> ?x"] *}
setup {* del_prfstep_thm @{thm m_inv_def} *}

theorem Units_inv_Units: "monoid G \<Longrightarrow> x \<in> Units G \<Longrightarrow> inv\<^bsub>G\<^esub> x \<in> Units G" by auto2
setup {* add_forward_prfstep_cond @{thm Units_inv_Units} [with_term "inv\<^bsub>?G\<^esub> ?x"] *}

lemma Units_l_cancel [forward]: fixes G (structure) shows
  "monoid G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> x \<in> Units G \<Longrightarrow> y = z"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(inv x \<otimes> x) \<otimes> y = inv x \<otimes> (x \<otimes> y)" THEN
    HAVE "(inv x \<otimes> x) \<otimes> z = inv x \<otimes> (x \<otimes> z)") *})

lemma Units_r_cancel [forward]: fixes G (structure) shows
  "monoid G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> y \<otimes> x = z \<otimes> x \<Longrightarrow> x \<in> Units G \<Longrightarrow> y = z"
  by (tactic {* auto2s_tac @{context} (
    HAVE "y \<otimes> (x \<otimes> inv x) = (y \<otimes> x) \<otimes> inv x" THEN
    HAVE "z \<otimes> (x \<otimes> inv x) = (z \<otimes> x) \<otimes> inv x") *})

lemma Units_inv_inv [rewrite]: fixes G (structure) shows
  "monoid G \<Longrightarrow> x \<in> Units G \<Longrightarrow> inv (inv x) = x" by auto2

lemma inv_inj_on_Units: "monoid G \<Longrightarrow> inj_on (m_inv G) (Units G)" by auto2

lemma Units_inv_comm [backward2]: fixes G (structure) shows
  "monoid G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<otimes> y = \<one> \<Longrightarrow> x \<in> Units G \<Longrightarrow> y \<otimes> x = \<one>"
  by (tactic {* auto2s_tac @{context} (
    HAVE "x \<otimes> y \<otimes> x = x \<otimes> (y \<otimes> x)" THEN
    HAVE "x \<otimes> (y \<otimes> x) = x \<otimes> \<one>") *})

lemma monoid_set_not_empty: fixes G (structure) shows
  "monoid G \<Longrightarrow> \<exists>x. x \<in> carrier G" by auto2

definition order :: "('a, 'b) monoid_scheme \<Rightarrow> nat" where
  "order S = card (carrier S)"
setup {* add_rewrite_rule @{thm order_def} *}

subsection \<open>Groups\<close>

definition group :: "('a, 'b) monoid_scheme \<Rightarrow> bool" where
  "group G \<longleftrightarrow> monoid G \<and> (\<forall>x\<in>carrier G. x \<in> Units G)"
setup {* add_property_const @{term "group"} *}

setup {* add_backward_prfstep (equiv_backward_th @{thm group_def}) *}

theorem groupI [backward]: fixes G (structure) shows
  "monoid G \<Longrightarrow> \<forall>x\<in>carrier G. (\<exists>y\<in>carrier G. y \<otimes> x = \<one>) \<Longrightarrow> group G" by auto2
setup {* del_prfstep_thm @{thm group_def} #>
  add_forward_prfstep_cond (equiv_forward_th @{thm group_def}) [with_term "?G"] *}

theorem group_to_monoid [forward]: "group G \<Longrightarrow> monoid G" by auto2
theorem group_elt_is_unit: "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> x \<in> Units G" by auto2
setup {* add_forward_prfstep_cond @{thm group_elt_is_unit} [with_term "?x", with_term "?G"] *}

(* Since every element is a unit, can streamline proofs here *)
theorem group_inv_prop: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> inv x \<in> carrier G"
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> inv x \<otimes> x = \<one>"
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> x \<otimes> inv x = \<one>" by auto2+
setup {* add_forward_prfstep_cond @{thm group_inv_prop(1)} [with_term "inv\<^bsub>?G\<^esub> ?x"] *}
setup {* fold add_rewrite_rule @{thms group_inv_prop(2-3)} *}

theorem group_l_cancel [forward]: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> x \<otimes> y = x \<otimes> z \<Longrightarrow> y = z" by auto2

theorem group_r_cancel [forward]: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> y \<otimes> x = z \<otimes> x \<Longrightarrow> y = z" by auto2

lemma group_inv_inv [rewrite]: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> inv (inv x) = x" by auto2

setup {* fold del_prfstep_thm [@{thm group_def}, @{thm group_elt_is_unit}] *}

theorem inv_equality [backward]: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> y \<otimes> x = \<one> \<Longrightarrow> inv x = y"
  by (tactic {* auto2s_tac @{context} (HAVE "inv x \<otimes> x = \<one>") *})

lemma inv_mult_group: fixes G (structure) shows
  "group G \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> inv (x \<otimes> y) = inv y \<otimes> inv x"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(inv y \<otimes> inv x) \<otimes> (x \<otimes> y) = inv y \<otimes> (inv x \<otimes> x) \<otimes> y") *})
setup {* add_rewrite_rule_cond @{thm inv_mult_group} (with_conds ["?x \<noteq> \<one>\<^bsub>?G\<^esub>", "?y \<noteq> \<one>\<^bsub>?G\<^esub>"]) *}

theorem move_inv_r: fixes G (structure) shows
  "group G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> c \<in> carrier G \<Longrightarrow> a \<otimes> inv b = c \<longleftrightarrow> a = c \<otimes> b"
  by (tactic {* auto2s_tac @{context} (
    HAVE "c \<otimes> b \<otimes> inv b = c \<otimes> (b \<otimes> inv b)") *})
setup {* add_rewrite_rule_cond @{thm move_inv_r} [with_cond "?b \<noteq> \<one>\<^bsub>?G\<^esub>"] *}

theorem move_inv_l: fixes G (structure) shows
  "group G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> c \<in> carrier G \<Longrightarrow> inv a \<otimes> b = c \<longleftrightarrow> b = a \<otimes> c"
  by (tactic {* auto2s_tac @{context} (
    HAVE "a \<otimes> c \<otimes> inv c = a \<otimes> (c \<otimes> inv c)") *})
setup {* add_rewrite_rule_cond @{thm move_inv_l} [with_cond "?a \<noteq> \<one>\<^bsub>?G\<^esub>"] *}

subsection \<open>Subgroups\<close>

definition is_subgroup :: "'a set \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> bool" where
  "is_subgroup H G \<longleftrightarrow>
    group G \<and> subset\<^bsub>G\<^esub> H \<and> (\<forall>x\<in>H. \<forall>y\<in>H. x \<otimes>\<^bsub>G\<^esub> y \<in> H) \<and> (\<one>\<^bsub>G\<^esub> \<in> H) \<and> (\<forall>x\<in>H. inv\<^bsub>G\<^esub> x \<in> H)"

definition subgroup :: "'a set \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> ('a, 'b) monoid_scheme" where
  "subgroup H G = G \<lparr>carrier := H\<rparr>"

lemma subgroup_sel [rewrite]:
  "is_subgroup H G \<Longrightarrow> carrier (subgroup H G) = H"
  "x \<otimes>\<^bsub>subgroup H G\<^esub> y = x \<otimes>\<^bsub>G\<^esub> y"
  "\<one>\<^bsub>subgroup H G\<^esub> = \<one>\<^bsub>G\<^esub>" by (simp add: subgroup_def)+

setup {* add_rewrite_rule @{thm is_subgroup_def} *}
lemma is_subgroupI [horn_clause]: fixes G (structure) shows
  "group G \<Longrightarrow> subset\<^bsub>G\<^esub> H \<Longrightarrow> \<forall>x\<in>H. \<forall>y\<in>H. x \<otimes> y \<in> H \<Longrightarrow> \<one> \<in> H \<Longrightarrow> \<forall>x\<in>H. inv x \<in> H \<Longrightarrow>
   is_subgroup H G" by auto2
setup {* del_prfstep_thm @{thm is_subgroup_def} *}

lemma is_subgroupD:
  "is_subgroup H G \<Longrightarrow> group G"
  "is_subgroup H G \<Longrightarrow> subset\<^bsub>G\<^esub> H"
  "is_subgroup H G \<Longrightarrow> x \<in> H \<Longrightarrow> y \<in> H \<Longrightarrow> x \<otimes>\<^bsub>G\<^esub> y \<in> H"
  "is_subgroup H G \<Longrightarrow> \<one>\<^bsub>G\<^esub> \<in> H"
  "is_subgroup H G \<Longrightarrow> x \<in> H \<Longrightarrow> inv\<^bsub>G\<^esub> x \<in> H" by (simp add: subgroup_def is_subgroup_def)+
setup {* fold add_forward_prfstep @{thms is_subgroupD(1-2)} *}
setup {* add_forward_prfstep_cond @{thm is_subgroupD(3)} [with_term "?x \<otimes>\<^bsub>?G\<^esub> ?y"] *}
setup {* add_forward_prfstep_cond @{thm is_subgroupD(4)} [with_term "\<one>\<^bsub>?G\<^esub>"] *}
setup {* add_forward_prfstep_cond @{thm is_subgroupD(5)} [with_term "inv\<^bsub>?G\<^esub> ?x"] *}

lemma subgroup_is_group: "is_subgroup H G \<Longrightarrow> \<H> = subgroup H G \<Longrightarrow> group \<H>"
  by (tactic {* auto2s_tac @{context}
    (HAVE "monoid \<H>" WITH (
      HAVE "\<forall>x\<in>carrier \<H>. \<forall>y\<in>carrier \<H>. \<forall>z\<in>carrier \<H>. (x \<otimes>\<^bsub>\<H>\<^esub> y) \<otimes>\<^bsub>\<H>\<^esub> z = x \<otimes>\<^bsub>\<H>\<^esub> (y \<otimes>\<^bsub>\<H>\<^esub> z)" WITH (
        HAVE "(x \<otimes>\<^bsub>G\<^esub> y) \<otimes>\<^bsub>G\<^esub> z = x \<otimes>\<^bsub>G\<^esub> (y \<otimes>\<^bsub>G\<^esub> z)")) THEN
     HAVE "\<forall>x\<in>carrier \<H>. \<exists>y\<in>carrier \<H>. y \<otimes>\<^bsub>\<H>\<^esub> x = \<one>\<^bsub>\<H>\<^esub>" WITH
      (HAVE "inv\<^bsub>G\<^esub> x \<otimes>\<^bsub>\<H>\<^esub> x = \<one>\<^bsub>\<H>\<^esub>")) *})

theorem subgroup_non_empty [resolve]: "is_subgroup H G \<Longrightarrow> H \<noteq> {}"
  by (tactic {* auto2s_tac @{context} (HAVE "\<one>\<^bsub>G\<^esub> \<in> H") *})

subsection \<open>Direct Products\<close>

definition DirProd :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<times> 'b) monoid" (infixr "\<times>\<times>" 80) where
  "G \<times>\<times> H =
    \<lparr>carrier = carrier G \<times> carrier H,
     mult = (\<lambda>(g, h) (g', h'). (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')),
     one = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)\<rparr>"

lemma Dir_Prod_sel [rewrite]:
  "(g, h) \<in> carrier (G \<times>\<times> H) \<longleftrightarrow> g \<in> carrier G \<and> h \<in> carrier H"
  "\<one>\<^bsub>G \<times>\<times> H\<^esub> = (\<one>\<^bsub>G\<^esub>, \<one>\<^bsub>H\<^esub>)"
  "(g, h) \<otimes>\<^bsub>(G \<times>\<times> H)\<^esub> (g', h') = (g \<otimes>\<^bsub>G\<^esub> g', h \<otimes>\<^bsub>H\<^esub> h')" by (simp add: DirProd_def)+

theorem elt_prod: "x \<in> carrier G \<Longrightarrow> y \<in> carrier H \<Longrightarrow> (x, y) \<in> carrier (G \<times>\<times> H)"
  by (simp add: Dir_Prod_sel(1))
setup {* add_forward_prfstep_cond @{thm elt_prod} [with_term "(?x, ?y)", with_term "?G \<times>\<times> ?H"] *}
theorem Prod_eq [backward]: "x = x' \<Longrightarrow> y = y' \<Longrightarrow> (x, y) = (x', y')" by auto
theorem mem_DirProd: "x \<in> carrier (G \<times>\<times> H) \<Longrightarrow> x = (fst x, snd x) \<and> fst x \<in> carrier G \<and> snd x \<in> carrier H"
  by (metis Dir_Prod_sel(1) prod.collapse)
setup {* add_forward_prfstep_cond @{thm mem_DirProd}
  (with_term "?x" :: with_term "?G \<times>\<times> ?H" :: with_conds ["?x \<noteq> (?x1, ?x2)", "?x \<noteq> \<one>\<^bsub>?G \<times>\<times> ?H\<^esub>"]) *}

lemma DirProd_monoid: "monoid G \<Longrightarrow> monoid H \<Longrightarrow> monoid (G \<times>\<times> H)" by auto2
setup {* add_forward_prfstep_cond @{thm DirProd_monoid} [with_term "?G \<times>\<times> ?H"] *}

lemma DirProd_group: "group G \<Longrightarrow> group H \<Longrightarrow> group (G \<times>\<times> H)"
  by (tactic {* auto2s_tac @{context}
    (LET "A = G \<times>\<times> H" THEN
     HAVE "monoid A" THEN
     HAVE "\<forall>x\<in>carrier A. (\<exists>y\<in>carrier A. y \<otimes>\<^bsub>A\<^esub> x = \<one>\<^bsub>A\<^esub>)" WITH
       HAVE "(inv\<^bsub>G\<^esub> (fst x), inv\<^bsub>H\<^esub> (snd x)) \<otimes>\<^bsub>A\<^esub> x = \<one>\<^bsub>A\<^esub>") *})
setup {* add_forward_prfstep_cond @{thm DirProd_group} [with_term "?G \<times>\<times> ?H"] *}

lemma inv_DirProd [rewrite]: "group G \<Longrightarrow> group H \<Longrightarrow> (g, h) \<in> carrier (G \<times>\<times> H) \<Longrightarrow>
  inv\<^bsub>G \<times>\<times> H\<^esub> (g, h) = (inv\<^bsub>G\<^esub> g, inv\<^bsub>H\<^esub> h)" by auto2

subsection \<open>Homomorphisms and Isomorphisms\<close>

definition hom :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b) set" where
  "hom G H =
    {h. h \<in> carrier G \<rightarrow> carrier H \<and>
      (\<forall>x\<in>carrier G. \<forall>y\<in>carrier G. h \<langle>x \<otimes>\<^bsub>G\<^esub> y\<rangle> = h\<langle>x\<rangle> \<otimes>\<^bsub>H\<^esub> h\<langle>y\<rangle>)}"

theorem is_homD1: "h \<in> hom G H \<Longrightarrow> x \<in> carrier G \<Longrightarrow> h\<langle>x\<rangle> \<in> carrier H"
  by (metis (no_types, lifting) Pi_mem feval_def hom_def mem_Collect_eq)
setup {* add_forward_prfstep_cond @{thm is_homD1} [with_term "?h\<langle>?x\<rangle>"] *}

theorem is_homD2 [rewrite]:
  "x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> h \<in> hom G H \<Longrightarrow> h \<langle>x \<otimes>\<^bsub>G\<^esub> y\<rangle> = h\<langle>x\<rangle> \<otimes>\<^bsub>H\<^esub> h\<langle>y\<rangle>"
  by (simp add: hom_def)

theorem is_homI [backward]:
  "\<forall>x\<in>carrier G. h\<langle>x\<rangle> \<in> carrier H \<Longrightarrow> \<forall>x\<in>carrier G. \<forall>y\<in>carrier G. h \<langle>x \<otimes>\<^bsub>G\<^esub> y\<rangle> = h\<langle>x\<rangle> \<otimes>\<^bsub>H\<^esub> h\<langle>y\<rangle> \<Longrightarrow>
   h \<in> hom G H" by (simp add: hom_def)

lemma hom_compose [backward1]:
  "group G \<Longrightarrow> h \<in> hom G H \<Longrightarrow> i \<in> hom H I \<Longrightarrow> i \<circ>\<^bsub>G\<^esub> h \<in> hom G I" by auto2

lemma hom_one_closed [rewrite]: fixes G (structure) shows
  "group G \<Longrightarrow> group H \<Longrightarrow> h \<in> hom G H \<Longrightarrow> h\<langle>\<one>\<rangle> = \<one>\<^bsub>H\<^esub>"
  by (tactic {* auto2s_tac @{context} (HAVE "h\<langle>\<one> \<otimes> \<one>\<rangle> = h\<langle>\<one>\<rangle> \<otimes>\<^bsub>H\<^esub> \<one>\<^bsub>H\<^esub>") *})

lemma hom_inv_closed [rewrite]: fixes G (structure) shows
  "group G \<Longrightarrow> group H \<Longrightarrow> x \<in> carrier G \<Longrightarrow> h \<in> hom G H \<Longrightarrow> h\<langle>inv x\<rangle> = inv\<^bsub>H\<^esub> h\<langle>x\<rangle>"
  by (tactic {* auto2s_tac @{context} (HAVE "h\<langle>inv x \<otimes> x\<rangle> = \<one>\<^bsub>H\<^esub>") *})

definition iso :: "_ \<Rightarrow> _ \<Rightarrow> ('a \<Rightarrow> 'b) set" (infixr "\<cong>" 60) where
  "G \<cong> H = {h. h \<in> hom G H \<and> struct_is_bij G H h}"
setup {* add_rewrite_rule @{thm iso_def} *}

lemma iso_refl: "(\<lambda>x. x) \<in> G \<cong> G" by auto2

lemma iso_trans: "group G \<Longrightarrow> h \<in> G \<cong> H \<Longrightarrow> i \<in> H \<cong> I \<Longrightarrow> (i \<circ>\<^bsub>G\<^esub> h) \<in> G \<cong> I" by auto2

lemma iso_sym: "group G \<Longrightarrow> group H \<Longrightarrow> h \<in> G \<cong> H \<Longrightarrow> h' = inv_fun\<^bsub>G\<^esub> h \<Longrightarrow> h' \<in> H \<cong> G"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>x\<in>carrier H. \<forall>y\<in>carrier H. h' \<langle>x \<otimes>\<^bsub>H\<^esub> y\<rangle> = (h'\<langle>x\<rangle>) \<otimes>\<^bsub>G\<^esub> (h'\<langle>y\<rangle>)" WITH
      (HAVE "h \<langle>h' \<langle>x \<otimes>\<^bsub>H\<^esub> y\<rangle>\<rangle> = x \<otimes>\<^bsub>H\<^esub> y" THEN
       HAVE "h \<langle>h'\<langle>x\<rangle> \<otimes>\<^bsub>G\<^esub> h'\<langle>y\<rangle>\<rangle> = x \<otimes>\<^bsub>H\<^esub> y")) *})

end
