theory SepAuto
imports "../Auto2_Main" "~~/src/HOL/Imperative_HOL/Imperative_HOL"
keywords "@hoare_induct" :: prf_decl % "proof"
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

section {* Definition of the run predicate *}

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
setup {* add_rewrite_rule @{thm execute_of_list} *}
setup {* add_rewrite_rule @{thm execute_upd(1)} *}
setup {* add_rewrite_rule @{thm execute_ref} *}
setup {* add_rewrite_rule @{thm execute_lookup} *}
setup {* add_rewrite_rule @{thm execute_nth(1)} *}
setup {* add_rewrite_rule @{thm execute_update} *}

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
    @have "set_partition (new_addrs h as (the \<sigma>)) (new_addrs h as1 (the \<sigma>)) as2"
  @end
@qed

(* This is the last use of the definition of separating conjunction. *)
setup {* del_prfstep_thm @{thm mod_star_conv} *}
setup {* del_prfstep_thm_str "@eqbackward@res" @{thm hoare_triple_def} *}

section {* Hoare triples for atomic commands *}

setup {* add_backward_prfstep (equiv_backward_th @{thm hoare_triple_def}) *}

(* First, those that do not modify the heap. *)

(* Avoid variables P and Q since they are pre- and post-condition. *)

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

lemma of_list_rule:
  "<emp> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>" by auto2

lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup {* fold del_prfstep_thm [@{thm sngr_assn_rule}, @{thm snga_assn_rule}] *}

section {* Other properties *}

theorem norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2

section {* success_run and its properties. *}

lemma new_addrs_bind [rewrite]:
  "lim h \<le> lim h' \<Longrightarrow> lim h' \<le> lim h'' \<Longrightarrow> new_addrs h' (new_addrs h as h') h'' = new_addrs h as h''" by auto2

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

subsection {* Assertions *}

lemma pure_conj:  "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2
lemma mod_false' [resolve]: "\<not> (h \<Turnstile> false * Ru)" by auto2

subsection {* Entailment *}

lemma entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
lemma entail_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
lemma entail_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
lemma entailsD_back: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>h \<Turnstile> Q * R \<Longrightarrow> \<not>h \<Turnstile> P * R" by auto2
lemma entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
lemma entail_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C"
  by (simp add: assn_times_comm entailsD' entails_def)
lemma entail_trans2': "D * B \<Longrightarrow>\<^sub>A A \<Longrightarrow> C \<Longrightarrow>\<^sub>A B \<Longrightarrow> D * C \<Longrightarrow>\<^sub>A A"
  by (simp add: assn_times_comm entailsD' entails_def)
lemma entails_invD: "A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not>(h \<Turnstile> B) \<Longrightarrow> \<not>(h \<Turnstile> A)"
  using entailsD by blast

lemma mod_array_eq [backward1]: "xs = xs' \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs \<Longrightarrow> h \<Turnstile> p \<mapsto>\<^sub>a xs'" by simp

subsection {* Clear unused proofsteps *}

setup {* fold del_prfstep_thm [
  @{thm mod_ex_dist}, @{thm ex_assn_def}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm star_false_left}, @{thm entailsD'}, @{thm mod_pure_star_dist}, @{thm mod_pure'}] *}

subsection {* Definition of procedures *}

named_theorems sep_proc_defs "Seplogic: definitions of procedures"
named_theorems sep_prec_thms "Seplogic: precision theorems"
(* Note adding to sep_heap_presv_thms is taken care of by heap_presv_thms attribute. *)
named_theorems sep_heap_presv_thms "Seplogic: heap preservation theorems"

declare ref_prec [sep_prec_thms]
declare array_ref_prec [sep_prec_thms]

(* ASCII abbreviations for ML files. *)
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "sep_util.ML"
ML_file "assn_matcher.ML"
ML_file "sep_steps.ML"
ML_file "sep_steps_test.ML"
ML_file "sep_induct.ML"

attribute_setup heap_presv_thms = {* setup_attrib add_heap_preserving_thm *}
attribute_setup forward_ent = {* setup_attrib add_forward_ent_prfstep *}
attribute_setup forward_ent_shadow = {* setup_attrib add_forward_ent_shadowing_prfstep *}
attribute_setup rewrite_ent = {* setup_attrib add_rewrite_ent_rule *}
attribute_setup hoare_create_case = {* setup_attrib add_match_hoare_create_case *}
attribute_setup hoare_triple = {* setup_attrib add_hoare_triple_prfstep *}
attribute_setup hoare_triple_direct = {* setup_attrib add_hoare_triple_direct_prfstep *}

lemma heap_preserving_lookup [heap_presv_thms]: "heap_preserving (!p)"
  using effect_lookupE heap_preserving_def by fastforce

lemma heap_preserving_return [heap_presv_thms]: "heap_preserving (return x)"
  using effect_returnE heap_preserving_def by fastforce

lemma heap_preserving_nth [heap_presv_thms]: "heap_preserving (Array.nth a i)"
  using effect_nthE heap_preserving_def by fastforce

lemma heap_preserving_len [heap_presv_thms]: "heap_preserving (Array.len a)"
  using effect_lengthE heap_preserving_def by fastforce

lemma heap_preserve_assert [heap_presv_thms]: "heap_preserving (assert P x)"
  using effect_assertE heap_preserving_def by fastforce

setup {* fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_match_hoare_create_case [
  @{thm assert_rule}, @{thm nth_rule}, @{thm upd_rule}] *}

setup {* fold add_hoare_triple_direct_prfstep [
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm of_list_rule}, @{thm length_rule}] *}

(* Some simple tests *)

theorem "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
