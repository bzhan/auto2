theory Sequence
imports Abs Finite
begin

section {* Definition of sequences as morphisms from Nat *}

definition is_sequence :: "i \<Rightarrow> o" where [rewrite]:
  "is_sequence(X) \<longleftrightarrow> (mor_form(X) \<and> source_str(X) = \<nat>)"
setup {* add_property_const @{term is_sequence} *}

definition seqs :: "i \<Rightarrow> i" where [rewrite]:
  "seqs(R) = (\<nat> \<rightharpoonup> R)"
  
lemma seqsD [forward]:
  "f \<in> seqs(R) \<Longrightarrow> is_sequence(f) \<and> source(f) = nat \<and> target_str(f) = R \<and> target(f) = carrier(R)"
  by auto2

lemma seqsI [typing]:
  "is_sequence(f) \<Longrightarrow> f \<in> seqs(target_str(f))" by auto2
    
(* Constructor for sequences *)
definition Seq :: "i \<Rightarrow> (i \<Rightarrow> i) \<Rightarrow> i" where [rewrite]:
  "Seq(R,f) = Mor(\<nat>,R,f)"

lemma Seq_is_sequence [backward]:
  "\<forall>x\<in>nat. f(x)\<in>.R \<Longrightarrow> Seq(R,f) \<in> seqs(R)" by auto2
setup {* add_prfstep_check_req ("Seq(R,f)", "Seq(R,f) \<in> seqs(R)") *}

lemma seq_beta [rewrite]:
  "F = Seq(R,f) \<Longrightarrow> is_sequence(F) \<Longrightarrow> x \<in> source(F) \<Longrightarrow> F`x = f(x)" by auto2

lemma seq_eval_in_range [typing]:
  "is_sequence(f) \<Longrightarrow> x \<in> source(f) \<Longrightarrow> f`x \<in> target(f)" by auto2

lemma seq_eq [backward]:
  "is_sequence(f) \<Longrightarrow> is_sequence(g) \<Longrightarrow> target_str(f) = target_str(g) \<Longrightarrow>
   \<forall>x\<in>nat. f`x = g`x \<Longrightarrow> f = g" by auto2

setup {* fold del_prfstep_thm [@{thm is_sequence_def}, @{thm seqs_def}, @{thm Seq_def}] *}
  
definition ord_ring_seq :: "i \<Rightarrow> o" where [rewrite]:
  "ord_ring_seq(X) \<longleftrightarrow> (is_sequence(X) \<and> is_ord_ring(target_str(X)))"
setup {* add_property_const @{term ord_ring_seq} *}

lemma ord_ring_seq_iff [forward]:
  "ord_ring_seq(X) \<Longrightarrow> is_sequence(X)"
  "ord_ring_seq(X) \<Longrightarrow> is_ord_ring(target_str(X))"
  "is_sequence(X) \<Longrightarrow> is_ord_ring(target_str(X)) \<Longrightarrow> ord_ring_seq(X)" by auto2+
setup {* del_prfstep_thm @{thm ord_ring_seq_def} *}

definition ord_field_seq :: "i \<Rightarrow> o" where [rewrite]:
  "ord_field_seq(X) \<longleftrightarrow> (is_sequence(X) \<and> is_ord_field(target_str(X)))"
setup {* add_property_const @{term ord_field_seq} *}
  
lemma ord_field_seq_iff [forward]:
  "ord_field_seq(X) \<Longrightarrow> is_sequence(X)"
  "ord_field_seq(X) \<Longrightarrow> is_ord_field(target_str(X))"
  "is_sequence(X) \<Longrightarrow> is_ord_field(target_str(X)) \<Longrightarrow> ord_field_seq(X)" by auto2+
setup {* del_prfstep_thm @{thm ord_field_seq_def} *}

section {* Negation on sequences *}

definition seq_neg :: "i \<Rightarrow> i" where [rewrite]:
  "seq_neg(X) = (let R = target_str(X) in Seq(R, \<lambda>n. -\<^sub>R X`n))"

lemma seq_neg_type [typing]:
  "is_sequence(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> is_comm_ring(R) \<Longrightarrow> seq_neg(X) \<in> seqs(target_str(X))" by auto2
    
lemma eval_seq_neg [rewrite]:
  "is_sequence(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<in> source(seq_neg(X)) \<Longrightarrow> is_comm_ring(R) \<Longrightarrow>
   seq_neg(X)`n = -\<^sub>R X`n" by auto2
setup {* del_prfstep_thm @{thm seq_neg_def} *}

lemma seq_neg_neg [rewrite]:
  "is_sequence(X) \<Longrightarrow> is_ord_ring(target_str(X)) \<Longrightarrow> seq_neg(seq_neg(X)) = X" by auto2

section {* Upper and lower bounds *}
  
definition upper_bounded :: "i \<Rightarrow> o" where [rewrite]:
  "upper_bounded(X) \<longleftrightarrow> (let R = target_str(X) in \<exists>r\<in>.R. \<forall>n\<in>.\<nat>. X`n \<le>\<^sub>R r)"
setup {* add_property_const @{term upper_bounded} *}
  
lemma upper_boundedD [resolve]:
  "upper_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r\<in>.R. \<forall>n\<in>.\<nat>. X`n \<le>\<^sub>R r" by auto2

lemma upper_boundedI [forward]:
  "is_sequence(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> order(R) \<Longrightarrow> \<forall>n\<in>.\<nat>. X`n \<le>\<^sub>R r \<Longrightarrow> upper_bounded(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "X`0 \<le>\<^sub>R r") *})
setup {* del_prfstep_thm @{thm upper_bounded_def} *}

definition lower_bounded :: "i \<Rightarrow> o" where [rewrite]:
  "lower_bounded(X) \<longleftrightarrow> (let R = target_str(X) in \<exists>r\<in>.R. \<forall>n\<in>.\<nat>. X`n \<ge>\<^sub>R r)"
setup {* add_property_const @{term lower_bounded} *}
  
lemma lower_boundedD [resolve]:
  "lower_bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r\<in>.R. \<forall>n\<in>.\<nat>. X`n \<ge>\<^sub>R r" by auto2
    
lemma lower_boundedI [forward]:
  "is_sequence(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> order(R) \<Longrightarrow> \<forall>n\<in>.\<nat>. X`n \<ge>\<^sub>R r \<Longrightarrow> lower_bounded(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "X`0 \<ge>\<^sub>R r") *})
setup {* del_prfstep_thm @{thm lower_bounded_def} *}
  
lemma lower_bounded_is_neg_upper [rewrite]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> upper_bounded(seq_neg(X)) \<longleftrightarrow> lower_bounded(X)"
  by (tactic {* auto2s_tac @{context} (
    CASE "lower_bounded(X)" WITH (
      CHOOSE "r\<in>.R, \<forall>n\<in>.\<nat>. r \<le>\<^sub>R X`n" THEN HAVE "\<forall>n\<in>.\<nat>. -\<^sub>R r \<ge>\<^sub>R (seq_neg(X))`n") THEN
    CASE "upper_bounded(seq_neg(X))" WITH (
      CHOOSE "r\<in>.R, \<forall>n\<in>.\<nat>. r \<ge>\<^sub>R seq_neg(X)`n" THEN HAVE "\<forall>n\<in>.\<nat>. -\<^sub>R r \<le>\<^sub>R X`n")) *})

section {* Boundedness on sequences *}

definition bounded :: "i \<Rightarrow> o" where bounded_def [rewrite]:
  "bounded(X) \<longleftrightarrow> (let R = target_str(X) in \<exists>r>\<^sub>R\<zero>\<^sub>R. \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r)"
setup {* add_property_const @{term bounded} *}
  
lemma boundedI [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r \<Longrightarrow> bounded(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R max(R,r,1\<^sub>R)" THEN HAVE "1\<^sub>R >\<^sub>R \<zero>\<^sub>R") *})

lemma boundedD [resolve]:
  "bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r" by auto2
setup {* del_prfstep_thm @{thm bounded_def} *}
  
lemma boundedI_less [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> bounded(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r") *})
    
lemma boundedD_less [resolve]:
  "ord_ring_seq(X) \<Longrightarrow> bounded(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r" THEN HAVE "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r +\<^sub>R \<one>\<^sub>R") *})
      
lemma bounded_on_tail [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r \<Longrightarrow> bounded(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "r \<in>. R" WITH HAVE "\<bar>X`k\<bar>\<^sub>R \<le>\<^sub>R r" THEN
    CASE "k = 0" WITH HAVE "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r" THEN
    CHOOSE "S \<noteq> \<emptyset>, S = nat_less_range(k)" THEN
    CHOOSE "f \<in> nat \<rightarrow> carrier(R), f = (\<lambda>i\<in>nat. \<bar>X`i\<bar>\<^sub>R \<in> carrier(R))" THEN
    LET "m = max(R,r,greatest(R,f `` S))" THEN
    HAVE "has_greatest(R,f``S)" THEN
    HAVE "\<forall>n\<in>.\<nat>. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R m" WITH HAVE "\<bar>X`n\<bar>\<^sub>R = f`n") *})

lemma bounded_less_on_tail [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> k \<in>. \<nat> \<Longrightarrow> \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> bounded(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R r") *})

section {* Vanishes condition on sequences *}
  
definition vanishes :: "i \<Rightarrow> o" where [rewrite]:
  "vanishes(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r)"
setup {* add_property_const @{term vanishes} *}

lemma vanishesI [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> vanishes(X)" by auto2

lemma vanishesE [backward]:
  "ord_ring_seq(X) \<Longrightarrow> vanishes(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" by auto2
setup {* del_prfstep_thm @{thm vanishes_def} *}
  
lemma vanishesE_nat_ge [backward1]:
  "ord_ring_seq(X) \<Longrightarrow> vanishes(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow>
   \<exists>k\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r" THEN HAVE "\<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>X`n\<bar>\<^sub>R <\<^sub>R r") *})

lemma not_vanishesD [backward]:
  "ord_ring_seq(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. r \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R r)") *})

section {* Cauchy condition on sequences *}

definition cauchy :: "i \<Rightarrow> o" where [rewrite]:
  "cauchy(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r)"
setup {* add_property_const @{term cauchy} *}

lemma cauchyE [backward]:
  "ord_ring_seq(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> 
   \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r" by auto2
  
lemma cauchyI [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow>
   \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> cauchy(X)" by auto2

lemma cauchyE2 [backward]:
  "ord_ring_seq(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R r" by auto2

lemma cauchyE_le [backward]:
  "ord_ring_seq(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow>
   \<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R \<le>\<^sub>R r" by auto2
setup {* del_prfstep_thm @{thm cauchy_def} *}

lemma cauchyI2 [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> cauchy(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R s" THEN
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R s" THEN
    HAVE "\<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r") *})

lemma cauchyE_nat_ge [backward1]:
  "ord_ring_seq(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow>
   \<exists>k\<ge>\<^sub>\<nat>i. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "j\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r" THEN
    HAVE "\<forall>m \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<forall>n \<ge>\<^sub>\<nat> max(\<nat>,i,j). \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r") *})

lemma cauchyE_le_nat_ge [backward1]:
  "ord_ring_seq(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow>
   \<exists>k\<ge>\<^sub>\<nat>i. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R \<le>\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "j\<ge>\<^sub>\<nat>i, \<forall>m\<ge>\<^sub>\<nat>j. \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r") *})

lemma not_cauchyD [backward]:
  "ord_field_seq(X) \<Longrightarrow> \<not>cauchy(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> \<exists>r>\<^sub>R\<zero>\<^sub>R. \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R \<ge>\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R r)") *})

lemma cauchy_from_vanishes [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> vanishes(X) \<Longrightarrow> cauchy(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>m\<ge>\<^sub>\<nat>k. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R s" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n\<bar>\<^sub>R <\<^sub>R s" THEN
    HAVE "\<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R r" WITH (
      HAVE "X`m -\<^sub>R X`n = X`m +\<^sub>R (-\<^sub>R X`n)")) *})

lemma cauchy_imp_bounded [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> bounded(X)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R 1\<^sub>R" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n\<bar>\<^sub>R <\<^sub>R \<bar>X`k\<bar>\<^sub>R +\<^sub>R 1\<^sub>R") *})

lemma abs_bound_one_side1 [forward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow>
   \<bar>a -\<^sub>R b\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> b \<ge>\<^sub>R r +\<^sub>R s \<Longrightarrow> a >\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a -\<^sub>R b) +\<^sub>R b >\<^sub>R -\<^sub>R s +\<^sub>R (r +\<^sub>R s)") *})

lemma abs_bound_one_side2 [forward]:
  "is_ord_ring(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> r \<in>. R \<Longrightarrow> s \<in>. R \<Longrightarrow>
   \<bar>a -\<^sub>R b\<bar>\<^sub>R <\<^sub>R s \<Longrightarrow> b \<le>\<^sub>R -\<^sub>R (r +\<^sub>R s) \<Longrightarrow> r <\<^sub>R -\<^sub>R a"
  by (tactic {* auto2s_tac @{context} (
    HAVE "(a -\<^sub>R b) +\<^sub>R b <\<^sub>R s +\<^sub>R -\<^sub>R (r +\<^sub>R s)") *})

lemma cauchy_not_vanishes_cases [backward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   \<exists>b>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n) \<or> (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R X`n)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<forall>k\<in>.\<nat>. \<exists>n\<ge>\<^sub>\<nat>k. r \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R s" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>m\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`m -\<^sub>R X`n\<bar>\<^sub>R <\<^sub>R s" THEN
    CHOOSE "k\<ge>\<^sub>\<nat>i, r \<le>\<^sub>R \<bar>X`k\<bar>\<^sub>R" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R X`k\<bar>\<^sub>R <\<^sub>R s" THEN
    CASE "X`k \<le>\<^sub>R -\<^sub>R r" WITH HAVE "\<forall>n\<ge>\<^sub>\<nat>k. s <\<^sub>R -\<^sub>R X`n" THEN
    CASE "X`k \<ge>\<^sub>R r" WITH HAVE "\<forall>n\<ge>\<^sub>\<nat>k. s <\<^sub>R X`n") *})
  
lemma cauchy_not_vanishes [backward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> cauchy(X) \<Longrightarrow> \<not>vanishes(X) \<Longrightarrow>
   \<exists>b>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "b >\<^sub>R \<zero>\<^sub>R, k\<in>.\<nat>, (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R -\<^sub>R X`n) \<or> (\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R X`n)" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. b <\<^sub>R \<bar>X`n\<bar>\<^sub>R") *})

section {* Convergence of sequences, limits *}
  
definition converges_to :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "converges_to(X,s) \<longleftrightarrow> (let R = target_str(X) in s \<in>. R \<and> (\<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r))"
setup {* register_wellform_data ("converges_to(X,s)", ["s \<in>. target_str(X)"]) *}

lemma converges_toE1 [forward]: "converges_to(X,s) \<Longrightarrow> s \<in>. target_str(X)" by auto2

lemma converges_toE2 [backward2]:
  "converges_to(X,s) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r" by auto2

lemma converges_toI [resolve]:
  "R = target_str(X) \<Longrightarrow> s \<in>. R \<Longrightarrow> \<forall>r>\<^sub>R\<zero>\<^sub>R. \<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r \<Longrightarrow> converges_to(X,s)" by auto2
setup {* del_prfstep_thm @{thm converges_to_def} *}

lemma converges_toE_nat_ge [backward2]:
  "converges_to(X,s) \<Longrightarrow> R = target_str(X) \<Longrightarrow> r >\<^sub>R \<zero>\<^sub>R \<Longrightarrow> i \<in>. \<nat> \<Longrightarrow>
   \<exists>k\<ge>\<^sub>\<nat>i. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "j\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r" THEN HAVE "max(\<nat>,i,j) \<ge>\<^sub>\<nat> i") *})

lemma converges_to_neg [backward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges_to(X,s) \<Longrightarrow> converges_to(seq_neg(X), -\<^sub>R s)"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "r >\<^sub>R \<zero>\<^sub>R, \<not>(\<exists>k\<in>.\<nat>. \<forall>n\<ge>\<^sub>\<nat>k. \<bar>seq_neg(X)`n -\<^sub>R (-\<^sub>R s)\<bar>\<^sub>R <\<^sub>R r)" THEN
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R s\<bar>\<^sub>R <\<^sub>R r" THEN
    HAVE "\<forall>n\<ge>\<^sub>\<nat>k. \<bar>seq_neg(X)`n -\<^sub>R (-\<^sub>R s)\<bar>\<^sub>R <\<^sub>R r" WITH
      HAVE "-\<^sub>R (X`n) -\<^sub>R (-\<^sub>R s) = -\<^sub>R (X`n -\<^sub>R s)") *})

lemma converges_to_neg' [resolve]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges_to(seq_neg(X),s) \<Longrightarrow> converges_to(X, -\<^sub>R s)"
  by (tactic {* auto2s_tac @{context} (HAVE "seq_neg(seq_neg(X)) = X") *})

lemma lt_limit [backward2]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges_to(X,x) \<Longrightarrow> y <\<^sub>R x \<Longrightarrow> \<exists>n\<in>.\<nat>. y <\<^sub>R X`n"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R x -\<^sub>R y" THEN
    HAVE "\<bar>X`k -\<^sub>R x\<bar>\<^sub>R <\<^sub>R x -\<^sub>R y" THEN HAVE "x -\<^sub>R X`k <\<^sub>R x -\<^sub>R y") *})

lemma gt_limit [backward2]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges_to(X,x) \<Longrightarrow> y >\<^sub>R x \<Longrightarrow> \<exists>n\<in>.\<nat>. y >\<^sub>R X`n"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "k\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>k. \<bar>X`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R y -\<^sub>R x" THEN
    HAVE "\<bar>X`k -\<^sub>R x\<bar>\<^sub>R <\<^sub>R y -\<^sub>R x" THEN HAVE "X`k -\<^sub>R x <\<^sub>R y -\<^sub>R x") *})

lemma limit_unique [forward]:
  "ord_field_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges_to(X,x) \<Longrightarrow> converges_to(X,y) \<Longrightarrow> x = y"
  by (tactic {* auto2s_tac @{context} (
    LET "r = \<bar>x -\<^sub>R y\<bar>\<^sub>R" THEN
    CHOOSE "s >\<^sub>R \<zero>\<^sub>R, t >\<^sub>R \<zero>\<^sub>R, r = s +\<^sub>R t" THEN
    CHOOSE "i\<in>.\<nat>, \<forall>n\<ge>\<^sub>\<nat>i. \<bar>X`n -\<^sub>R x\<bar>\<^sub>R <\<^sub>R s" THEN
    CHOOSE "j\<ge>\<^sub>\<nat>i, \<forall>n\<ge>\<^sub>\<nat>j. \<bar>X`n -\<^sub>R y\<bar>\<^sub>R <\<^sub>R t" THEN
    HAVE "\<bar>x -\<^sub>R y\<bar>\<^sub>R <\<^sub>R r") *})
      
definition converges :: "i \<Rightarrow> o" where [rewrite]:
  "converges(X) \<longleftrightarrow> (\<exists>s. converges_to(X,s))"
setup {* add_property_const @{term converges} *}

lemma convergesI [forward]:
  "converges_to(X,x) \<Longrightarrow> converges(X)" by auto2

lemma convergesE [resolve]:
  "converges(X) \<Longrightarrow> \<exists>s. converges_to(X,s)" by auto2
setup {* del_prfstep_thm @{thm converges_def} *}
  
lemma converges_neg [forward]:
  "ord_ring_seq(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> converges(X) \<Longrightarrow> converges(seq_neg(X))"
  by (tactic {* auto2s_tac @{context} (
    CHOOSE "s, converges_to(X,s)" THEN
    HAVE "converges_to(seq_neg(X), -\<^sub>R s)") *})

lemma converges_neg' [forward]:
  "is_sequence(X) \<Longrightarrow> is_ord_ring(target_str(X)) \<Longrightarrow> converges(seq_neg(X)) \<Longrightarrow> converges(X)"
  by (tactic {* auto2s_tac @{context} (HAVE "seq_neg(seq_neg(X)) = X") *})
  
section {* Constant sequences *}
  
definition seq_const :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "seq_const(R,x) = Seq(R,\<lambda>_. x)"
setup {* register_wellform_data ("seq_const(R,x)", ["x \<in>. R"]) *}

abbreviation seq_const_notation :: "i \<Rightarrow> i \<Rightarrow> i" ("{_}\<^sub>_" [10,91] 90) where
  "{x}\<^sub>R \<equiv> seq_const(R,x)"

lemma seq_const_type [typing]:
  "is_ord_ring(R) \<Longrightarrow> x \<in>. R \<Longrightarrow> {x}\<^sub>R \<in> seqs(R)" by auto2
    
lemma seq_const_eval [rewrite]:
  "is_ord_ring(R) \<Longrightarrow> n \<in> source({x}\<^sub>R) \<Longrightarrow> x \<in>. R \<Longrightarrow> {x}\<^sub>R`n = x" by auto2
setup {* del_prfstep_thm @{thm seq_const_def} *}

section {* Increasing and decreasing sequences *}
  
definition seq_incr :: "i \<Rightarrow> o" where [rewrite]:
  "seq_incr(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`n \<ge>\<^sub>R X`m)"
setup {* add_property_const @{term seq_incr} *}

lemma seq_incrE [backward]:
  "seq_incr(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<ge>\<^sub>\<nat> m \<Longrightarrow> X`n \<ge>\<^sub>R X`m" by auto2

lemma seq_incrI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`n \<ge>\<^sub>R X`m \<Longrightarrow> seq_incr(X)" by auto2

definition seq_decr :: "i \<Rightarrow> o" where [rewrite]:
  "seq_decr(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`n \<le>\<^sub>R X`m)"
setup {* add_property_const @{term seq_decr} *}

lemma seq_decrE [backward]:
  "seq_decr(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<ge>\<^sub>\<nat> m \<Longrightarrow> X`n \<le>\<^sub>R X`m" by auto2
    
lemma seq_decrI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`m \<ge>\<^sub>R X`n \<Longrightarrow> seq_decr(X)" by auto2

lemma seq_incr_on_neg_is_seq_decr [rewrite]:
  "is_sequence(X) \<Longrightarrow> is_ord_ring(target_str(X)) \<Longrightarrow> seq_incr(seq_neg(X)) \<longleftrightarrow> seq_decr(X)" by auto2

lemma seq_decr_on_neg_is_seq_incr [rewrite]:
  "is_sequence(X) \<Longrightarrow> is_ord_ring(target_str(X)) \<Longrightarrow> seq_decr(seq_neg(X)) \<longleftrightarrow> seq_incr(X)" by auto2

setup {* fold del_prfstep_thm [@{thm seq_incr_def}, @{thm seq_decr_def}] *}
  
lemma seq_incrI' [forward]:
  "R = target_str(X) \<Longrightarrow> order(R) \<Longrightarrow> \<forall>n\<in>.\<nat>. X`(n +\<^sub>\<nat> 1) \<ge>\<^sub>R X`n \<Longrightarrow> seq_incr(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`n \<ge>\<^sub>R X`m" WITH INDUCT_ON "n \<ge>\<^sub>\<nat> m" "X`n \<ge>\<^sub>R X`m") *})

lemma seq_decrI' [forward]:
  "R = target_str(X) \<Longrightarrow> order(R) \<Longrightarrow> \<forall>n\<in>.\<nat>. X`(n +\<^sub>\<nat> 1) \<le>\<^sub>R X`n \<Longrightarrow> seq_decr(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> X`n \<le>\<^sub>R X`m" WITH INDUCT_ON "n \<ge>\<^sub>\<nat> m" "X`n \<le>\<^sub>R X`m") *})

definition seq_abs_decr :: "i \<Rightarrow> o" where [rewrite]:
  "seq_abs_decr(X) \<longleftrightarrow> (let R = target_str(X) in \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`m\<bar>\<^sub>R)"
setup {* add_property_const @{term seq_abs_decr} *}
  
lemma seq_abs_decrE [backward]:
  "seq_abs_decr(X) \<Longrightarrow> R = target_str(X) \<Longrightarrow> n \<ge>\<^sub>\<nat> m \<Longrightarrow> \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`m\<bar>\<^sub>R" by auto2
    
lemma seq_abs_decrI [forward]:
  "R = target_str(X) \<Longrightarrow> \<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`m\<bar>\<^sub>R \<Longrightarrow> seq_abs_decr(X)" by auto2
setup {* del_prfstep_thm @{thm seq_abs_decr_def} *}
  
lemma seq_abs_decrI' [forward]:
  "R = target_str(X) \<Longrightarrow> order(R) \<Longrightarrow> \<forall>n\<in>.\<nat>. \<bar>X`(n +\<^sub>\<nat> 1)\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`n\<bar>\<^sub>R \<Longrightarrow> seq_abs_decr(X)"
  by (tactic {* auto2s_tac @{context} (
    HAVE "\<forall>m n. n \<ge>\<^sub>\<nat> m \<longrightarrow> \<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`m\<bar>\<^sub>R" WITH INDUCT_ON "n \<ge>\<^sub>\<nat> m" "\<bar>X`n\<bar>\<^sub>R \<le>\<^sub>R \<bar>X`m\<bar>\<^sub>R") *})

section {* Inductive definition of sequences *}

definition rec_type_cond :: "[i, i, [i, i] \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "rec_type_cond(S,a,b) \<longleftrightarrow> (a \<in> S \<and> (\<forall>m\<in>nat. \<forall>p\<in>S. b(m,p)\<in>S))"
  
lemma rec_type_cond [typing]:
  "rec_type_cond(S,a,b) \<Longrightarrow> a \<in> S"
  "rec_type_cond(S,a,b) \<Longrightarrow> m \<in> nat \<Longrightarrow> p \<in> S \<Longrightarrow> b(m,p) \<in> S" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm rec_type_cond_def} *}

definition Seq_rec :: "[i, i, [i, i] \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Seq_rec(R,a,b) = Seq(R, \<lambda>n. nat_rec(a,b,n))"
setup {* register_wellform_data ("Seq_rec(R,a,b)", ["rec_type_cond(carrier(R),a,b)"]) *}
setup {* add_prfstep_check_req ("Seq_rec(R,a,b)", "rec_type_cond(carrier(R),a,b)") *}

lemma Seq_rec_is_seq [typing]:
  "rec_type_cond(carrier(R),a,b) \<Longrightarrow> Seq_rec(R,a,b) \<in> seqs(R)" by auto2

lemma Seq_rec_eval [rewrite]:
  "rec_type_cond(carrier(R),a,b) \<Longrightarrow> Seq_rec(R,a,b)`0 = a"
  "rec_type_cond(carrier(R),a,b) \<Longrightarrow> m \<in>. \<nat> \<Longrightarrow> Seq_rec(R,a,b)`(m +\<^sub>\<nat> 1) = b(m,Seq_rec(R,a,b)`m)" by auto2+
setup {* del_prfstep_thm @{thm Seq_rec_def} *}
  
(* a and b are initial values. ai is the function taking m, a_m, and b_m giving a_{m+1},
   bi is the function taking m, a_m, and b_m giving b_{m+1}. Result is a sequence
   from k to \<langle>a_k,b_k\<rangle>. *)
definition nat_rec2 :: "[i, [i, i, i] \<Rightarrow> i, i, [i, i, i] \<Rightarrow> i, i] \<Rightarrow> i" where [rewrite]:
  "nat_rec2(a,ai,b,bi,k) =
    nat_rec(\<langle>a,b\<rangle>, \<lambda>m p. \<langle>ai(m,fst(p),snd(p)),bi(m,fst(p),snd(p))\<rangle>, k)"
setup {* register_wellform_data ("nat_rec2(a,ai,b,bi,k)", ["k \<in> nat"]) *}

lemma nat_rec2_0 [rewrite]: "nat_rec2(a,ai,b,bi,0) = \<langle>a,b\<rangle>" by auto2
  
lemma nat_rec2_Suc [rewrite]:
  "m \<in> nat \<Longrightarrow> nat_rec2(a,ai,b,bi,m +\<^sub>\<nat> 1) =
    (let \<langle>p,q\<rangle> = nat_rec2(a,ai,b,bi,m) in \<langle>ai(m,p,q),bi(m,p,q)\<rangle>)" by auto2
setup {* del_prfstep_thm @{thm nat_rec2_def} *}

definition rec2_type_cond :: "[i, i, i, [i, i, i] \<Rightarrow> i, i, [i, i, i] \<Rightarrow> i] \<Rightarrow> o" where [rewrite]:
  "rec2_type_cond(S,T,a,ai,b,bi) \<longleftrightarrow> (a \<in> S \<and> b \<in> T \<and>
     (\<forall>m\<in>nat. \<forall>p\<in>S. \<forall>q\<in>T. ai(m,p,q)\<in>S \<and> bi(m,p,q)\<in>T))"

lemma rec2_type_condD [typing]:
  "rec2_type_cond(S,T,a,ai,b,bi) \<Longrightarrow> a \<in> S"
  "rec2_type_cond(S,T,a,ai,b,bi) \<Longrightarrow> b \<in> T"
  "rec2_type_cond(S,T,a,ai,b,bi) \<Longrightarrow> m \<in> nat \<Longrightarrow> p \<in> S \<Longrightarrow> q \<in> T \<Longrightarrow> ai(m,p,q)\<in>S"
  "rec2_type_cond(S,T,a,ai,b,bi) \<Longrightarrow> m \<in> nat \<Longrightarrow> p \<in> S \<Longrightarrow> q \<in> T \<Longrightarrow> bi(m,p,q)\<in>T" by auto2+
setup {* del_prfstep_thm_str "@eqforward" @{thm rec2_type_cond_def} *}

lemma nat_rec2_type [backward,typing]:
  "k \<in> nat \<Longrightarrow> rec2_type_cond(S,T,a,ai,b,bi) \<Longrightarrow> nat_rec2(a,ai,b,bi,k) \<in> S \<times> T"
  by (tactic {* auto2s_tac @{context} (
    INDUCT_ON "k \<in> nat" "nat_rec2(a,ai,b,bi,k) \<in> S \<times> T") *})
setup {* fold del_prfstep_thm @{thms rec2_type_condD} *}

definition Seq_rec2 :: "[i, i, [i, i, i] \<Rightarrow> i, i, [i, i, i] \<Rightarrow> i] \<Rightarrow> i" where [rewrite]:
  "Seq_rec2(R,a,ai,b,bi) = \<langle>Seq(R, \<lambda>n. fst(nat_rec2(a,ai,b,bi,n))),
                              Seq(R, \<lambda>n. snd(nat_rec2(a,ai,b,bi,n)))\<rangle>"
setup {* register_wellform_data ("Seq_rec2(R,a,ai,b,bi)",
                                ["rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi)"]) *}
setup {* add_prfstep_check_req ("Seq_rec2(R,a,ai,b,bi)",
                                "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi)") *}

lemma Seq_rec2_is_seq [typing]:
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> fst(Seq_rec2(R,a,ai,b,bi)) \<in> seqs(R)"
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> snd(Seq_rec2(R,a,ai,b,bi)) \<in> seqs(R)" by auto2+

lemma Seq_rec2_eval [rewrite]:
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> fst(Seq_rec2(R,a,ai,b,bi))`0 = a"
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> snd(Seq_rec2(R,a,ai,b,bi))`0 = b"
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> m \<in>. \<nat> \<Longrightarrow>
   S = Seq_rec2(R,a,ai,b,bi) \<Longrightarrow> fst(S)`(m +\<^sub>\<nat> 1) = ai(m,fst(S)`m,snd(S)`m)"
  "rec2_type_cond(carrier(R),carrier(R),a,ai,b,bi) \<Longrightarrow> m \<in>. \<nat> \<Longrightarrow>
   S = Seq_rec2(R,a,ai,b,bi) \<Longrightarrow> snd(S)`(m +\<^sub>\<nat> 1) = bi(m,fst(S)`m,snd(S)`m)" by auto2+
setup {* del_prfstep_thm @{thm Seq_rec2_def} *}

end
