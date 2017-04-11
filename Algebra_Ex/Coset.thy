(* Normal subgroup, quotient group, following HOL/Algebra/Coset. *)

theory Coset
imports Group
begin

subsection \<open>Cosets\<close>

definition r_coset :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> 'a set" (infixl "#>\<index>" 60) where
  "H #>\<^bsub>G\<^esub> a = (\<Union>h\<in>H. {h \<otimes>\<^bsub>G\<^esub> a})"
setup {* add_rewrite_rule @{thm r_coset_def} *}

definition RCOSETS  :: "_ \<Rightarrow> 'a set \<Rightarrow> ('a set) set" ("rcosets\<index> _" [81] 80) where
  "rcosets\<^bsub>G\<^esub> H = (\<Union>a\<in>carrier G. {H #>\<^bsub>G\<^esub> a})"
setup {* add_rewrite_rule @{thm RCOSETS_def} *}

theorem is_rcoset: fixes G (structure) shows
  "s \<in> rcosets H \<Longrightarrow> \<exists>a\<in>carrier G. s = H #> a" by auto2
setup {* add_forward_prfstep_cond @{thm is_rcoset} [with_cond "?s \<noteq> \<one>\<^bsub>?G'\<^esub>"] *}

theorem r_coset_bij [rewrite_back]: fixes G (structure) shows
  "group G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> subset H \<Longrightarrow> card H = card (H #> a)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "f, \<forall>h. f h = h \<otimes> a" THEN
     HAVE "bij_betw f H (H #> a)" WITH
     (HAVE "inj_on f H" THEN
      HAVE "\<forall>y\<in>(H #> a). \<exists>x\<in>H. f x = y" WITH CHOOSE "x\<in>H, y = x \<otimes> a")) *})

theorem r_coset_eqI [backward1]: fixes G (structure) shows
  "is_subgroup H G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> a \<otimes> inv b \<in> H \<Longrightarrow> H #> a = H #> b"
  by (tactic {* auto2s_tac @{context}
    (HAVE "b \<otimes> inv a \<in> H" WITH HAVE "inv (a \<otimes> inv b) = b \<otimes> inv a" THEN
     HAVE "\<forall>x. x \<in> (H #> a) \<longleftrightarrow> x \<in> H #> b" WITH
      (CASE "x \<in> H #> a" WITH
        (CHOOSE "h \<in> H, x = h \<otimes> a" THEN
         HAVE "(h \<otimes> a) \<otimes> (inv b \<otimes> b) = (h \<otimes> (a \<otimes> inv b)) \<otimes> b") THEN
       CASE "x \<in> H #> b" WITH
        (CHOOSE "h \<in> H, x = h \<otimes> b" THEN
         HAVE "(h \<otimes> b) \<otimes> (inv a \<otimes> a) = (h \<otimes> (b \<otimes> inv a)) \<otimes> a"))) *})

theorem r_coset_disjoint [backward1]: fixes G (structure) shows
  "a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> is_subgroup H G \<Longrightarrow> H #> a \<noteq> H #> b \<Longrightarrow> set_disjoint (H #> a) (H #> b)"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "x, x \<in> (H #> a) \<inter> (H #> b)" THEN
     CHOOSES ["ha\<in>H, x = ha \<otimes> a", "hb\<in>H, x = hb \<otimes> b"] THEN
     HAVE "a \<otimes> (inv x \<otimes> x) \<otimes> inv b = (a \<otimes> inv x) \<otimes> (x \<otimes> inv b)") *})

theorem r_cosets_union_G [rewrite]: fixes G (structure) shows
  "is_subgroup H G \<Longrightarrow> \<Union>(rcosets H) = carrier G"
  by (tactic {* auto2s_tac @{context}
    (HAVE "carrier G \<subseteq> \<Union>(rcosets H)" WITH
      (HAVE "\<forall>a\<in>carrier G. a \<in> H #> a" WITH HAVE "a = \<one> \<otimes> a")) *})

theorem lagrange: fixes G (structure) shows
  "finite (carrier G) \<Longrightarrow> is_subgroup H G \<Longrightarrow> card (rcosets H) * card H = order G"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>S\<in>rcosets H. \<forall>T\<in>rcosets H. S \<noteq> T \<longrightarrow> S \<inter> T = {}" THEN
     HAVE "carrier G = \<Union>(rcosets H)") *})

definition set_mult :: "_ \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "<#>\<index>" 60) where
  "H <#>\<^bsub>G\<^esub> K = (\<Union>h\<in>H. \<Union>k\<in>K. {h \<otimes> \<^bsub>G\<^esub> k})"
setup {* add_rewrite_rule @{thm set_mult_def} *}
theorem set_multI [backward]: "h \<in> H \<Longrightarrow> k \<in> K \<Longrightarrow> h \<otimes>\<^bsub>G\<^esub> k \<in> H <#>\<^bsub>G\<^esub> K" by auto2

definition is_normal_subgroup :: "'a set \<Rightarrow> ('a, 'b) monoid_scheme \<Rightarrow> bool" where
  "is_normal_subgroup H G \<longleftrightarrow>
    is_subgroup H G \<and>
    (\<forall>a\<in>carrier G. \<forall>h\<in>H. a \<otimes>\<^bsub>G\<^esub> h \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> a \<in> H)"
setup {* add_backward_prfstep (equiv_backward_th @{thm is_normal_subgroup_def}) *}

lemma is_normal_subgroupD: fixes G (structure) shows
  "is_normal_subgroup H G \<Longrightarrow> is_subgroup H G"
  "is_normal_subgroup H G \<Longrightarrow> a \<in> carrier G \<Longrightarrow> h \<in> H \<Longrightarrow> a \<otimes> h \<otimes> inv a \<in> H"
  by (simp add: is_normal_subgroup_def)+
setup {* add_forward_prfstep @{thm is_normal_subgroupD(1)} *}
setup {* add_backward2_prfstep @{thm is_normal_subgroupD(2)} *}

lemma is_normal_subgroupD' [backward2]: fixes G (structure) shows
  "a \<in> carrier G \<Longrightarrow> is_normal_subgroup H G \<Longrightarrow> h \<in> H \<Longrightarrow> inv a \<otimes> h \<otimes> a \<in> H"
  by (tactic {* auto2s_tac @{context} (HAVE "a = inv (inv a)") *})

theorem set_mult_normal_cosets [rewrite]: fixes G (structure) shows
  "a \<in> carrier G \<Longrightarrow> b \<in> carrier G \<Longrightarrow> is_normal_subgroup H G \<Longrightarrow> (H #> a) <#> (H #> b) = H #> (a \<otimes> b)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>x. x \<in> (H #> a) <#> (H #> b) \<longleftrightarrow> x \<in> H #> (a \<otimes> b)" WITH
      (CASE "x \<in> (H #> a) <#> (H #> b)" WITH
        (CHOOSE "x1 \<in> H #> a, x2 \<in> H #> b, x = x1 \<otimes> x2" THEN
         CHOOSE "h1 \<in> H, x1 = h1 \<otimes> a" THEN CHOOSE "h2 \<in> H, x2 = h2 \<otimes> b" THEN
         HAVE "x = (h1 \<otimes> a) \<otimes> (h2 \<otimes> inv a \<otimes> a \<otimes> b)" THEN
         HAVE "a \<otimes> h2 \<otimes> inv a \<in> H" THEN
         HAVE "(h1 \<otimes> a) \<otimes> (h2 \<otimes> inv a \<otimes> a \<otimes> b) = (h1 \<otimes> (a \<otimes> h2 \<otimes> inv a)) \<otimes> (a \<otimes> b)") THEN
       CASE "x \<in> H #> (a \<otimes> b)" WITH
        (CHOOSE "h \<in> H, x = h \<otimes> (a \<otimes> b)" THEN
         HAVE "h \<otimes> (a \<otimes> (\<one> \<otimes> b)) = (h \<otimes> a) \<otimes> (\<one> \<otimes> b)"))) *})

definition FactGroup :: "_ \<Rightarrow> 'a set \<Rightarrow> ('a set) monoid" (infixl "Mod" 65) where
  "FactGroup G H = \<lparr>carrier = rcosets\<^bsub>G\<^esub> H, mult = set_mult G, one = H #>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>\<rparr>"

lemma FactGroup_sel [rewrite]:
  "carrier (G Mod H) = rcosets\<^bsub>G\<^esub>H"
  "\<one>\<^bsub>(G Mod H)\<^esub> = H #>\<^bsub>G\<^esub> \<one>\<^bsub>G\<^esub>"
  "S \<otimes>\<^bsub>(G Mod H)\<^esub> T = S <#>\<^bsub>G\<^esub> T" by (simp add: FactGroup_def)+

lemma r_coset_id_disjoint [backward]: fixes G (structure) shows
  "a = b \<Longrightarrow> H #> a = H #> b" by simp

theorem FactGroup_is_group: fixes G (structure) shows
  "is_normal_subgroup H G \<Longrightarrow> group (G Mod H)"
  by (tactic {* auto2s_tac @{context}
    (HAVE "monoid (G Mod H)" THEN
     HAVE "\<forall>S\<in>carrier (G Mod H). (\<exists>T\<in>carrier (G Mod H). T \<otimes>\<^bsub>G Mod H\<^esub> S = \<one>\<^bsub>G Mod H\<^esub>)" WITH
      (CHOOSE "x, x \<in> carrier G \<and> S = H #> x" THEN
       HAVE "(H #> inv x) \<otimes>\<^bsub>G Mod H\<^esub> (H #> x) = \<one>\<^bsub>G Mod H\<^esub>")) *})

definition kernel :: "('a, 'm) monoid_scheme \<Rightarrow> ('b, 'n) monoid_scheme \<Rightarrow>  ('a \<Rightarrow> 'b) \<Rightarrow> 'a set" where
  "kernel G H h = {x. x \<in> carrier G \<and> h\<langle>x\<rangle> = \<one>\<^bsub>H\<^esub>}"
setup {* add_rewrite_rule @{thm kernel_def} *}

theorem in_kernel [backward]: "x \<in> carrier G \<Longrightarrow> h\<langle>x\<rangle> = \<one>\<^bsub>H\<^esub> \<Longrightarrow> x \<in> kernel G H h" by auto2

(* Earlier verified assumptions (such as \<forall>x\<in>H. inv x \<in> H) generate useless derivations. *)
lemma kernel_is_subgroup [backward]:
  "group G \<Longrightarrow> group H \<Longrightarrow> h \<in> hom G H \<Longrightarrow> is_subgroup (kernel G H h) G" by auto2

lemma kernel_is_normal_subgroup:
  "group G \<Longrightarrow> group H \<Longrightarrow> h \<in> hom G H \<Longrightarrow> is_normal_subgroup (kernel G H h) G" by auto2
setup {* add_forward_prfstep_cond @{thm kernel_is_normal_subgroup} [with_term "kernel ?G ?H ?h"] *}

theorem coset_non_empty [backward]: "H \<noteq> {} \<Longrightarrow> H #>\<^bsub>G\<^esub> a \<noteq> {}"
  by (tactic {* auto2s_tac @{context}
    (CHOOSE "h, h \<in> H" THEN HAVE "h \<otimes>\<^bsub>G\<^esub> a \<in> H #>\<^bsub>G\<^esub> a") *})

definition set_hom ::
  "('a, 'm) monoid_scheme \<Rightarrow> ('b, 'n) monoid_scheme \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a set \<Rightarrow> 'b)" where
  "set_hom G H h S = the_elem (h ` S)"

theorem set_hom_eval [rewrite]: "(set_hom G H h)\<langle>S\<rangle> = the_elem (h ` S)" by (simp add: set_hom_def)

theorem set_hom_on_coset [rewrite]: fixes G (structure) shows
  "group G \<Longrightarrow> group H \<Longrightarrow> a \<in> carrier G \<Longrightarrow> h \<in> hom G H \<Longrightarrow> (set_hom G H h)\<langle>(kernel G H h) #> a\<rangle> = h\<langle>a\<rangle>"
  by (tactic {* auto2s_tac @{context}
    (HAVE "\<forall>y\<in>(kernel G H h) #> a. h\<langle>y\<rangle> = h\<langle>a\<rangle>" WITH CHOOSE "x\<in>kernel G H h, y = x \<otimes> a") *})

theorem set_hom_is_iso: fixes G (structure) shows
  "group G \<Longrightarrow> group H \<Longrightarrow> h \<in> hom G H \<Longrightarrow> is_surj H h \<Longrightarrow> K = kernel G H h \<Longrightarrow>
   h' = set_hom G H h \<Longrightarrow> h' \<in> (G Mod K) \<cong> H"
   by (tactic {* auto2s_tac @{context}
     (HAVE "h' \<in> hom (G Mod K) H" THEN
      HAVE "\<forall>S\<in>carrier (G Mod K). \<forall>T\<in>carrier (G Mod K). h'\<langle>S\<rangle> = h'\<langle>T\<rangle> \<longrightarrow> S = T" WITH
       (CHOOSE "a, a \<in> carrier G \<and> S = K #> a" THEN
        CHOOSE "b, b \<in> carrier G \<and> T = K #> b" THEN
        HAVE "a \<otimes> inv b \<in> K") THEN
      HAVE "\<forall>x. x \<in> image\<^bsub>G Mod K\<^esub> h' \<longleftrightarrow> x \<in> image h" WITH
        CASE "x \<in> image h" WITH
         (CHOOSE "y, y \<in> carrier G \<and> h\<langle>y\<rangle> = x" THEN
          HAVE "x = (set_hom G H h)\<langle>(kernel G H h) #> y\<rangle>")) *})

end
