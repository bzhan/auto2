(* Based on AFP/Separation_Logic/Imperative_HOL/Assertions.thy *)

theory Assertions
imports "../Auto2_Main" "~~/src/HOL/Imperative_HOL/Imperative_HOL"
begin 

subsection {* Partial Heaps *}
text {*
  A partial heap is modeled by a heap and a set of valid addresses, with the
  side condition that the valid addresses have to be within the limit of the
  heap. This modeling is somewhat strange for separation logic, however, it 
  allows us to solve some technical problems related to definition of 
  Hoare triples, that will be detailed later.
*}
type_synonym pheap = "heap \<times> addr set"

text {* Predicate that expresses that the address set of a partial heap is 
  within the heap's limit.
*}
fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" where
  "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup {* add_rewrite_rule @{thm in_range.simps} *}

text {* Relation that holds if two heaps are identical on a given 
  address range. *}
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where
  "relH as h h' = (in_range (h, as) \<and> in_range (h', as) \<and>
     (\<forall>t. \<forall>a \<in> as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a))"
setup {* add_rewrite_rule @{thm relH_def} *}

lemma relH_dist_union [forward]: "relH (as \<union> as') h h' \<Longrightarrow> relH as h h' \<and> relH as' h h'" by auto2

lemma relH_ref [rewrite]: "relH as h h' \<Longrightarrow> addr_of_ref r \<in> as \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (simp add: Ref.get_def relH_def)

lemma relH_array [rewrite]: "relH  as h h' \<Longrightarrow> addr_of_array r \<in> as \<Longrightarrow> Array.get h r = Array.get h' r"
  by (simp add: Array.get_def relH_def)

lemma relH_set_ref [resolve]: "relH {a. a < lim h \<and> a \<notin> {addr_of_ref r}} h (Ref.set r x h)"
  by (simp add: Ref.set_def relH_def)

lemma relH_set_array [resolve]: "relH {a. a < lim h \<and> a \<notin> {addr_of_array r}} h (Array.set r x h)"
  by (simp add: Array.set_def relH_def)

subsection {* Assertions *}
text {*
  Assertions are predicates on partial heaps, that fulfill a well-formedness 
  condition called properness: They only depend on the part of the heap
  by the address set, and must be false for partial heaps that are not in range.
*}
datatype assn_raw = Assn (assn_fn: "pheap \<Rightarrow> bool")
setup {* add_forward_prfstep @{thm assn_raw.expand} *}

fun aseval :: "assn_raw \<Rightarrow> pheap \<Rightarrow> bool" where
  "aseval (Assn f) h = f h"
setup {* add_rewrite_rule @{thm aseval.simps} *}

definition proper :: "assn_raw \<Rightarrow> bool" where
  "proper P = (
    (\<forall>h as. aseval P (h,as) \<longrightarrow> in_range (h,as)) \<and>
    (\<forall>h h' as. aseval P (h,as) \<longrightarrow> relH as h h' \<longrightarrow> in_range (h',as) \<longrightarrow> aseval P (h',as)))"
setup {* add_rewrite_rule @{thm proper_def} *}

typedef assn = "Collect proper"
@proof @have "Assn in_range \<in> Collect proper" @qed

setup {* add_resolve_prfstep (equiv_forward_th @{thm Rep_assn_inject}) *}

theorem Abs_assn_inverse' [rewrite]: "proper y \<Longrightarrow> Rep_assn (Abs_assn y) = y"
  by (simp add: Abs_assn_inverse)

theorem proper_Rep_assn: "proper (Rep_assn P)" using Rep_assn by auto
setup {* add_forward_prfstep_cond @{thm proper_Rep_assn} [with_term "Rep_assn ?P"] *}

definition models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) where
  "h \<Turnstile> P = aseval (Rep_assn P) h"
setup {* add_rewrite_rule_bidir @{thm models_def} *}

lemma models_in_range [resolve]: "h \<Turnstile> P \<Longrightarrow> in_range h" by auto2

lemma mod_relH [forward]:
  "relH as h h' \<Longrightarrow> (h, as) \<Turnstile> P \<Longrightarrow> (h', as) \<Turnstile> P" by auto2

setup {* add_gen_prfstep ("proper_assn_case",
  [WithTerm @{term_pat "?h \<Turnstile> Abs_assn ?P"},
   CreateCase @{term_pat "proper ?P"}]) *}

instantiation assn :: one begin
  definition one_assn :: assn where "1 \<equiv> Abs_assn (Assn (\<lambda>h. snd h = {}))"
instance .. end

abbreviation one_assn :: assn ("emp") where "one_assn \<equiv> 1"

setup {* add_rewrite_rule (to_obj_eq_th @{thm one_assn_def}) *}
theorem one_assn_rule [rewrite]: "h \<Turnstile> emp \<longleftrightarrow> snd h = {}" by auto2
setup {* del_prfstep_thm @{thm one_assn_def} *}

definition set_partition :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "set_partition S T1 T2 = (S = T1 \<union> T2 \<and> T1 \<inter> T2 = {})"
setup {* add_rewrite_rule @{thm set_partition_def} *}

instantiation assn :: times begin
  definition times_assn where
    "P * Q = Abs_assn (Assn (
      \<lambda>h. (\<exists>as1 as2. set_partition (snd h) as1 as2 \<and>
                     aseval (Rep_assn P) (fst h, as1) \<and> aseval (Rep_assn Q) (fst h, as2))))"
instance .. end

setup {* add_rewrite_rule @{thm times_assn_def} *}
lemma mod_star_conv [rewrite]:
  "h \<Turnstile> A * B \<longleftrightarrow>
    (\<exists>as1 as2. set_partition (snd h) as1 as2 \<and> (fst h, as1) \<Turnstile> A \<and> (fst h, as2) \<Turnstile> B)" by auto2
setup {* del_prfstep_thm @{thm times_assn_def} *}

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10) where
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> Q)"
setup {* add_backward_prfstep (equiv_backward_th @{thm entails_def}) *}

lemma entailsD [forward]:
  "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P \<Longrightarrow> h \<Turnstile> Q" using entails_def by blast

theorem aseval_ext [backward]: "\<forall>h. aseval P h = aseval P' h \<Longrightarrow> P = P'"
  apply (cases P) apply (cases P') by auto

lemma ent_iffI: "(A \<Longrightarrow>\<^sub>A B) \<and> (B \<Longrightarrow>\<^sub>A A) \<Longrightarrow> A = B"
@proof @have "Rep_assn A = Rep_assn B" @qed
setup {* add_backward_prfstep_cond @{thm ent_iffI} [with_filt (order_filter "A" "B")] *}
setup {* del_prfstep_thm @{thm aseval_ext} *}

theorem assn_one_left: "1 * P = (P::assn)"
@proof
  @have "\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> 1 * P" @with @have "set_partition (snd h) {} (snd h)" @end
@qed

theorem set_partition_comm [forward]: "set_partition S T1 T2 \<Longrightarrow> set_partition S T2 T1" by auto2

theorem assn_times_comm: "P * Q = Q * (P::assn)" by auto2

theorem set_partition_assoc [forward]:
  "set_partition S T1 T2 \<Longrightarrow> set_partition T1 T11 T12 \<Longrightarrow>
   set_partition S T11 (T12 \<union> T2) \<and> set_partition (T12 \<union> T2) T12 T2" by auto2

setup {* del_prfstep_thm @{thm models_def} *}
theorem assn_times_assoc: "(P * Q) * R = P * (Q * (R::assn))" by auto2
setup {* del_prfstep_thm @{thm set_partition_comm} *}
setup {* del_prfstep_thm @{thm set_partition_assoc} *}

instantiation assn :: comm_monoid_mult begin
  instance apply standard
  apply (rule assn_times_assoc) apply (rule assn_times_comm) by (rule assn_one_left)
end

subsubsection {* Existential Quantification *}

definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11) where
  "(\<exists>\<^sub>Ax. P x) = Abs_assn (Assn (\<lambda>h. \<exists>x. h \<Turnstile> P x))"
setup {* add_rewrite_rule @{thm ex_assn_def} *}

setup {* add_rewrite_rule_bidir @{thm models_def} *}
lemma mod_ex_dist [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x)) \<longleftrightarrow> (\<exists>x. h \<Turnstile> P x)" by auto2
setup {* del_prfstep_thm @{thm models_def} *}

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
@proof
  @have "\<forall>h. h \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q \<longrightarrow> h \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
    @obtain as1 as2 where "set_partition (snd h) as1 as2" "(fst h, as1) \<Turnstile> (\<exists>\<^sub>Ax. P x) \<and> (fst h, as2) \<Turnstile> Q"
    @obtain x where "(fst h, as1) \<Turnstile> P x"
    @have "h \<Turnstile> P x * Q"
  @end
@qed

subsubsection {* Pointers *}

text {* In Imperative HOL, we have to distinguish between pointers to single
  values and pointers to arrays. For both, we define assertions that 
  describe the part of the heap that a pointer points to. *}

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) where
  "r \<mapsto>\<^sub>r x = Abs_assn (Assn (
    \<lambda>h. Ref.get (fst h) r = x \<and> snd h = {addr_of_ref r} \<and> addr_of_ref r < lim (fst h)))"

setup {* add_rewrite_rule_bidir @{thm models_def} *}
setup {* add_rewrite_rule @{thm sngr_assn_def} *}
lemma sngr_assn_rule [rewrite]:
  "(h, as) \<Turnstile> r \<mapsto>\<^sub>r x \<longleftrightarrow> (Ref.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h)" by auto2
setup {* del_prfstep_thm @{thm sngr_assn_def} *}

definition snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82) where
  "r \<mapsto>\<^sub>a x = Abs_assn (Assn (
    \<lambda>h. Array.get (fst h) r = x \<and> snd h = {addr_of_array r} \<and> addr_of_array r < lim (fst h)))"

setup {* add_rewrite_rule @{thm snga_assn_def} *}
lemma snga_assn_rule [rewrite]:
  "(h, as) \<Turnstile> r \<mapsto>\<^sub>a x \<longleftrightarrow> (Array.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" by auto2
setup {* del_prfstep_thm @{thm snga_assn_def} *}

subsubsection {* Pure Assertions *}

text {* Pure assertions do not depend on any heap content. *}

definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where
  "\<up>b = Abs_assn (Assn (\<lambda>h. snd h = {} \<and> b))"

setup {* add_rewrite_rule @{thm pure_assn_def} *}
lemma pure_assn_rule [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (snd h = {} \<and> b)" by auto2
setup {* del_prfstep_thm @{thm pure_assn_def} *}

definition top_assn :: assn ("true") where
  "top_assn = Abs_assn (Assn in_range)"

setup {* add_rewrite_rule @{thm top_assn_def} *}
theorem top_assn_rule [rewrite]: "h \<Turnstile> true \<longleftrightarrow> in_range h" by auto2
setup {* del_prfstep_thm @{thm top_assn_def} *}
setup {* del_prfstep_thm @{thm models_def} *}

abbreviation bot_assn :: assn ("false") where "bot_assn \<equiv> \<up>False"

lemma star_false_left [rewrite]: "false * P = false" by auto2

lemma mod_star_trueI: "h \<Turnstile> P \<Longrightarrow> h \<Turnstile> P * true"
@proof @have "set_partition (snd h) (snd h) {}" @qed

theorem sngr_same_false [resolve]: "\<not>h \<Turnstile> p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y * Qu" by auto2
theorem snga_same_false [resolve]: "\<not>h \<Turnstile> p \<mapsto>\<^sub>r x * p \<mapsto>\<^sub>r y * Qu" by auto2

lemma mod_pure_star_dist [rewrite]: "h \<Turnstile> P * \<up>b \<longleftrightarrow> (h \<Turnstile> P \<and> b)"
@proof @case "h \<Turnstile> P \<and> b" @with @have "set_partition (snd h) (snd h) {}" @end @qed

lemma mod_pure' [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (h \<Turnstile> emp \<and> b)" by auto2

theorem ref_prec:
  "h \<Turnstile> p \<mapsto>\<^sub>r x * Qu \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>r y * Ru \<Longrightarrow> x = y" by auto2
setup {* add_forward_prfstep_cond @{thm ref_prec} [with_cond "?x \<noteq> ?y"] *}

theorem array_ref_prec:
  "h \<Turnstile> p \<mapsto>\<^sub>a x * Qu \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a y * Ru \<Longrightarrow> x = y" by auto2
setup {* add_forward_prfstep_cond @{thm array_ref_prec} [with_cond "?x \<noteq> ?y"] *}

theorem entailsD' [forward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P * R \<Longrightarrow> h \<Turnstile> Q * R" by auto2

end
