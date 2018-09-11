(*
  File: ArrowImpossibility.thy
  Author: Bohua Zhan

  Arrow impossibility theorem. Based on ArrowImpossibility/GS/Arrow_Order
  in the AFP.
*)

theory ArrowImpossibility
  imports WellOrder Finite
begin

section {* Sets with at least three elements *}
  
definition distinct3 :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "distinct3(X,a,b,c) \<longleftrightarrow> (a \<in> X \<and> b \<in> X \<and> c \<in> X \<and> a \<noteq> b \<and> a \<noteq> c \<and> b \<noteq> c)"
  
lemma distinct3_perms [resolve]:
  "distinct3(X,a,b,c) \<Longrightarrow> distinct3(X,a,c,b)"
  "distinct3(X,a,b,c) \<Longrightarrow> distinct3(X,b,a,c)"
  "distinct3(X,a,b,c) \<Longrightarrow> distinct3(X,b,c,a)"
  "distinct3(X,a,b,c) \<Longrightarrow> distinct3(X,c,a,b)"
  "distinct3(X,a,b,c) \<Longrightarrow> distinct3(X,c,b,a)" by auto2+
  
definition card_ge3 :: "i \<Rightarrow> o" where [rewrite]:
  "card_ge3(X) \<longleftrightarrow> (\<exists>a b c. distinct3(X,a,b,c))"

lemma card_ge3I [resolve]: "distinct3(X,a,b,c) \<Longrightarrow> card_ge3(X)" by auto2
lemma card_ge3_D1 [resolve]: "card_ge3(X) \<Longrightarrow> \<exists>a b c. distinct3(X,a,b,c)" by auto2
lemma card_ge3_D2 [backward]:
  "card_ge3(X) \<Longrightarrow> a \<in> X \<Longrightarrow> b \<in> X \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<exists>c\<in>X. distinct3(X,a,b,c)" by auto2
lemma card_ge3_choose2 [resolve]:
  "card_ge3(X) \<Longrightarrow> \<exists>a\<in>X. \<exists>b\<in>X. a \<noteq> b" by auto2
setup {* del_prfstep_thm @{thm card_ge3_def} *}
  
notation less ("prefer")
abbreviation "eq_prefer(R,a,b,S,a',b') \<equiv> (prefer(R,a,b) \<longleftrightarrow> prefer(S,a',b'))"
abbreviation "prefer3(R,a,b,c) \<equiv> a <\<^sub>R b \<and> b <\<^sub>R c"

section {* Linear ordering *}
  
definition linorder_space :: "i \<Rightarrow> i" where [rewrite]:
  "linorder_space(S) = {R \<in> raworder_space(S). linorder(R)}"
  
lemma linorder_spaceD [forward]:
  "R \<in> linorder_space(S) \<Longrightarrow> R \<in> raworder_space(S) \<and> linorder(R)" by auto2

lemma linorder_spaceI [backward1]:
  "linorder(R) \<Longrightarrow> R \<in> raworder_space(S) \<Longrightarrow> R \<in> linorder_space(S)" by auto2
setup {* del_prfstep_thm @{thm linorder_space_def} *}
  
lemma exists_linorder [resolve]: "\<exists>R. R \<in> linorder_space(S)"
@proof
  @obtain "R\<in>raworder_space(S)" where "well_order(R)"
  @have "R \<in> linorder_space(S)"
@qed
      
definition mk_top :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "mk_top(R,a) = Order(carrier(R), \<lambda>x y. y = a \<or> (x \<noteq> a \<and> x \<le>\<^sub>R y))"
setup {* register_wellform_data ("mk_top(R,a)", ["a \<in>. R"]) *}

lemma mk_top_eval:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S = mk_top(R,a) \<Longrightarrow> x \<in>. S \<Longrightarrow> y \<in>. S \<Longrightarrow>
   x \<le>\<^sub>S y \<longleftrightarrow> (y = a \<or> (x \<noteq> a \<and> x \<le>\<^sub>R y))" by auto2
setup {* add_rewrite_rule_cond @{thm mk_top_eval} [with_cond "?x \<noteq> ?a", with_cond "?y \<noteq> ?a"] *}
  
lemma mk_top_eval2 [resolve]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S = mk_top(R,a) \<Longrightarrow> x \<in>. S \<Longrightarrow> x \<le>\<^sub>S a" by auto2

lemma mk_top_type [typing]:
  "linorder(R) \<Longrightarrow> mk_top(R,a) \<in> linorder_space(carrier(R))" by auto2

lemma mk_top_eq_prefer [backward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b \<noteq> a \<Longrightarrow> c \<noteq> a \<Longrightarrow>
   S = mk_top(R,a) \<Longrightarrow> b <\<^sub>R c \<longleftrightarrow> b <\<^sub>S c" by auto2

setup {* del_prfstep_thm @{thm mk_top_def} *}
  
definition mk_bot :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "mk_bot(R,a) = Order(carrier(R), \<lambda>x y. x = a \<or> (y \<noteq> a \<and> x \<le>\<^sub>R y))"
setup {* register_wellform_data ("mk_bot(R,a)", ["a \<in>. R"]) *}

lemma mk_bot_eval:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S = mk_bot(R,a) \<Longrightarrow> x \<in>. S \<Longrightarrow> y \<in>. S \<Longrightarrow>
   x \<le>\<^sub>S y \<longleftrightarrow> (x = a \<or> (y \<noteq> a \<and> x \<le>\<^sub>R y))" by auto2
setup {* add_rewrite_rule_cond @{thm mk_bot_eval} [with_cond "?x \<noteq> ?a", with_cond "?y \<noteq> ?a"] *}
  
lemma mk_bot_eval2 [resolve]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> S = mk_bot(R,a) \<Longrightarrow> x \<in>. S \<Longrightarrow> a \<le>\<^sub>S x" by auto2
  
lemma mk_bot_type [typing]:
  "linorder(R) \<Longrightarrow> mk_bot(R,a) \<in> linorder_space(carrier(R))" by auto2

lemma mk_bot_eq_prefer [backward]:
  "linorder(R) \<Longrightarrow> a \<in>. R \<Longrightarrow> b \<in>. R \<Longrightarrow> c \<in>. R \<Longrightarrow> b \<noteq> a \<Longrightarrow> c \<noteq> a \<Longrightarrow>
   S = mk_bot(R,a) \<Longrightarrow> b <\<^sub>R c \<longleftrightarrow> b <\<^sub>S c" by auto2

setup {* del_prfstep_thm @{thm mk_bot_def} *}
  
lemma complete_Lin [backward]:
  "a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<noteq> b \<Longrightarrow> \<exists>R\<in>linorder_space(S). prefer(R,a,b)"
@proof
  @obtain "R \<in> linorder_space(S)" @let "R' = mk_top(R,b)"
@qed
      
lemma complete_Lin3 [backward]:
  "distinct3(S,a,b,c) \<Longrightarrow> \<exists>R\<in>linorder_space(S). prefer3(R,a,b,c)"
@proof
  @obtain "R \<in> linorder_space(S)" where "a <\<^sub>R b" @let "R' = mk_top(R,c)"
@qed
      
lemma complete_Lin_mk_top [backward]:
  "linorder(R) \<Longrightarrow> S = carrier(R) \<Longrightarrow> distinct3(S,a,b,c) \<Longrightarrow>
   \<exists>R'\<in>linorder_space(S). eq_prefer(R,a,b,R',a,b) \<and> prefer(R',a,c) \<and> prefer(R',b,c)"
@proof @let "R' = mk_top(R,c)" @qed

lemma complete_Lin_mk_bot [backward]:
  "linorder(R) \<Longrightarrow> S = carrier(R) \<Longrightarrow> distinct3(S,a,b,c) \<Longrightarrow>
   \<exists>R'\<in>linorder_space(S). eq_prefer(R,a,b,R',a,b) \<and> prefer(R',c,a) \<and> prefer(R',c,b)"
@proof @let "R' = mk_bot(R,c)" @qed

section {* Profiles and policies *}
  
definition Prof :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "Prof(I,Cs) = I \<rightarrow> linorder_space(Cs)"
  
definition Policy :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "Policy(I,Cs) = Prof(I,Cs) \<rightarrow> linorder_space(Cs)"
  
definition unanimity :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "unanimity(I,Cs,F) \<longleftrightarrow> (\<forall>P\<in>Prof(I,Cs). \<forall>a b. (\<forall>i\<in>I. prefer(P`i,a,b)) \<longrightarrow> prefer(F`P,a,b))"
setup {* register_wellform_data ("unanimity(I,Cs,F)", ["F \<in> Policy(I,Cs)"]) *}

lemma unanimityE [forward]:
  "F \<in> Policy(I,Cs) \<Longrightarrow> unanimity(I,Cs,F) \<Longrightarrow> \<forall>i\<in>I. prefer(P`i,a,b) \<Longrightarrow> P \<in> source(F) \<Longrightarrow> prefer(F`P,a,b)" by auto2
setup {* del_prfstep_thm_eqforward @{thm unanimity_def} *}

definition IIA :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "IIA(I,Cs,F) \<longleftrightarrow> (\<forall>P\<in>Prof(I,Cs). \<forall>P'\<in>Prof(I,Cs). \<forall>a b.
     (\<forall>i\<in>I. eq_prefer(P`i,a,b, P'`i,a,b)) \<longrightarrow> eq_prefer(F`P,a,b, F`P',a,b))"
setup {* register_wellform_data ("IIA(I,Cs,F)", ["F \<in> Policy(I,Cs)"]) *}

lemma IIA_E [forward]:
  "F \<in> Policy(I,Cs) \<Longrightarrow> IIA(I,Cs,F) \<Longrightarrow> \<forall>i\<in>I. eq_prefer(P`i,a,b, P'`i,a,b) \<Longrightarrow>
   P \<in> source(F) \<Longrightarrow> P' \<in> source(F) \<Longrightarrow> eq_prefer(F`P,a,b, F`P',a,b)" by auto2
setup {* del_prfstep_thm_eqforward @{thm IIA_def} *}

definition dictator :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "dictator(I,Cs,F,i) \<longleftrightarrow> (\<forall>P\<in>Prof(I,Cs). F`P = P`i)"
setup {* register_wellform_data ("dictator(I,Cs,F,i)", ["F \<in> Policy(I,Cs)", "i \<in> I"]) *}

lemma dictatorI [backward]:
  "F \<in> Policy(I,Cs) \<Longrightarrow> i \<in> I \<Longrightarrow> \<forall>P\<in>Prof(I,Cs). \<forall>a b. prefer(P`i,a,b) \<longrightarrow> prefer(F`P,a,b) \<Longrightarrow>
   dictator(I,Cs,F,i)" by auto2
setup {* del_prfstep_thm_str "@invbackward" @{thm dictator_def} *}

definition arrow_conds :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "arrow_conds(I,Cs,F) \<longleftrightarrow> (F \<in> Policy(I,Cs) \<and> unanimity(I,Cs,F) \<and> IIA(I,Cs,F))"

section {* Strict neutrality *}
  
(* Generalization of IIA (which is when a = a', b = b') *)
definition strict_neutral :: "[i, i, i, i, i, i, i] \<Rightarrow> o" where [rewrite]:
  "strict_neutral(I,Cs,F,a,b,a',b') \<longleftrightarrow> a \<in> Cs \<and> b \<in> Cs \<and> a' \<in> Cs \<and> b' \<in> Cs \<and> (
    \<forall>P\<in>Prof(I,Cs). \<forall>P'\<in>Prof(I,Cs). (\<forall>i\<in>I. eq_prefer(P`i,a,b,P'`i,a',b')) \<longrightarrow> eq_prefer(F`P,a,b,F`P',a',b'))"

lemma strict_neutralE1 [forward]:
  "strict_neutral(I,Cs,F,a,b,a',b') \<Longrightarrow> a \<in> Cs \<and> b \<in> Cs \<and> a' \<in> Cs \<and> b' \<in> Cs" by auto2

lemma strict_neutralE2 [forward]:
  "strict_neutral(I,Cs,F,a,b,a',b') \<Longrightarrow> \<forall>i\<in>I. eq_prefer(P`i,a,b,P'`i,a',b') \<Longrightarrow>
   P \<in> Prof(I,Cs) \<Longrightarrow> P' \<in> Prof(I,Cs) \<Longrightarrow> eq_prefer(F`P,a,b,F`P',a',b')" by auto2
setup {* del_prfstep_thm_eqforward @{thm strict_neutral_def} *}

lemma ex_fun: "\<forall>a\<in>X. \<exists>y\<in>Y. P(a,y) \<Longrightarrow> \<exists>f\<in>X\<rightarrow>Y. \<forall>a\<in>X. P(a,f`a)"
@proof @let "f = Fun(X,Y,\<lambda>a. SOME y\<in>Y. P(a,y))" @qed

setup {* add_prfstep_custom ("ex_fun",
  [WithGoal @{term_pat "\<exists>f\<in>?X\<rightarrow>?Y. \<forall>a\<in>?X. ?P(a,f)"}],
  (fn ((id, _), ths) => fn items => fn _ =>
    let
      val ex_fun' = @{thm ex_fun} |> apply_to_thm (Conv.rewr_conv UtilBase.backward_conv_th)
    in
      [AddItems {id = id, sc = SOME 1, raw_items = [Update.thm_to_ritem (ths MRS ex_fun')]},
       ShadowItem {id = id, item = the_single items}]
    end
    handle THM _ => []))
*}

lemma ex_ifb_fun [backward]:
  "ifb C then \<exists>x\<in>S. P(x) else \<exists>x\<in>S. Q(x) \<Longrightarrow> \<exists>x\<in>S. ifb C then P(x) else Q(x)" by auto2

lemma strict_neutrality1:
  "arrow_conds(I,Cs,F) \<Longrightarrow> distinct3(Cs,a,b,b') \<Longrightarrow> strict_neutral(I,Cs,F,a,b,a,b')"
@proof
  @have "\<forall>P\<in>Prof(I,Cs). \<forall>P'\<in>Prof(I,Cs). (\<forall>i\<in>I. eq_prefer(P`i,a,b, P'`i,a,b')) \<longrightarrow> eq_prefer(F`P,a,b, F`P',a,b')" @with
    @case "prefer(F`P,a,b)" @with
      @obtain "P''\<in>Prof(I,Cs)" where "\<forall>i\<in>I. (ifb prefer(P`i,a,b) then prefer3(P''`i,a,b,b') else prefer3(P''`i,b,b',a))"
      @have "\<forall>i\<in>I. prefer(P''`i,b,b')"
      @have "\<forall>i\<in>I. eq_prefer(P`i,a,b, P''`i,a,b)"
      @have "\<forall>i\<in>I. eq_prefer(P`i,a,b, P''`i,a,b')"
      @have "\<forall>i\<in>I. eq_prefer(P''`i,a,b', P'`i,a,b')" @end
    @case "prefer(F`P',a,b')" @with
      @obtain "P''\<in>Prof(I,Cs)" where "\<forall>i\<in>I. (ifb prefer(P`i,b,a) then prefer3(P''`i,b',b,a) else prefer3(P''`i,a,b',b))"
      @have "\<forall>i\<in>I. prefer(P''`i,b',b)"
      @have "\<forall>i\<in>I. eq_prefer(P`i,b,a, P''`i,b,a)"
      @have "\<forall>i\<in>I. eq_prefer(P`i,b,a, P''`i,b',a)"
      @have "\<forall>i\<in>I. eq_prefer(P''`i,b',a, P'`i,b',a)" @end
  @end
@qed
setup {* add_backward2_prfstep_cond @{thm strict_neutrality1} [with_cond "?b \<noteq> ?b'"] *}
  
lemma strict_neutrality2:
  "arrow_conds(I,Cs,F) \<Longrightarrow> distinct3(Cs,a,b,b') \<Longrightarrow> strict_neutral(I,Cs,F,b,a,b',a)"
@proof
  @have "strict_neutral(I,Cs,F,a,b,a,b')"
  @have "\<forall>P\<in>Prof(I,Cs). \<forall>P'\<in>Prof(I,Cs). (\<forall>i\<in>I. eq_prefer(P`i,b,a, P'`i,b',a)) \<longrightarrow> eq_prefer(F`P,b,a, F`P',b',a)" @with
    @have "\<forall>i\<in>I. eq_prefer(P`i,a,b, P'`i,a,b')" @end
@qed
setup {* add_backward2_prfstep_cond @{thm strict_neutrality2} [with_cond "?b \<noteq> ?b'"] *}
  
lemma strict_neutrality_trans [forward]:
  "strict_neutral(I,Cs,F,a,b,a'',b'') \<Longrightarrow> strict_neutral(I,Cs,F,a'',b'',a',b') \<Longrightarrow> a'' \<noteq> b'' \<Longrightarrow> strict_neutral(I,Cs,F,a,b,a',b')"
@proof
  @have "\<forall>P\<in>Prof(I,Cs). \<forall>P'\<in>Prof(I,Cs). (\<forall>i\<in>I. eq_prefer(P`i,a,b, P'`i,a',b')) \<longrightarrow> eq_prefer(F`P,a,b, F`P',a',b')" @with
    @obtain "P''\<in>Prof(I,Cs)" where "\<forall>i\<in>I. (ifb prefer(P`i,a,b) then prefer(P''`i,a'',b'') else prefer(P''`i,b'',a''))"
    @have "\<forall>i\<in>I. eq_prefer(P`i,a,b, P''`i,a'',b'')"
    @have "\<forall>i\<in>I. eq_prefer(P''`i,a'',b'', P'`i,a',b')" @end
@qed

lemma strict_neutrality [backward2]:
  "card_ge3(Cs) \<Longrightarrow> arrow_conds(I,Cs,F) \<Longrightarrow> a \<noteq> b \<Longrightarrow> a' \<noteq> b' \<Longrightarrow> a \<in> Cs \<Longrightarrow> b \<in> Cs \<Longrightarrow> a' \<in> Cs \<Longrightarrow> b' \<in> Cs \<Longrightarrow>
   strict_neutral(I,Cs,F,a,b,a',b')"
@proof
  @have "strict_neutral(I,Cs,F,a,b,b,a)" @with
    @obtain "c\<in>Cs" where "distinct3(Cs,a,b,c)" @have "strict_neutral(I,Cs,F,a,b,a,c)"
    @have "strict_neutral(I,Cs,F,a,c,b,c)" @have "strict_neutral(I,Cs,F,b,c,b,a)" @end
  @have "strict_neutral(I,Cs,F,a,b,a,b)"
  @case "b' = a" @with @have "strict_neutral(I,Cs,F,b,a,a',a)" @end
  @case "a' = b" @with @have "strict_neutral(I,Cs,F,b,a,b,b')" @end
  @case "b' = b" @case "a' = a"  (* All distinct *)
  @have "strict_neutral(I,Cs,F,a,b,a,b')"
  @have "strict_neutral(I,Cs,F,a,b',a',b')"
@qed

section {* Arrow's theorem *}

lemma Arrow: "finite(I) \<Longrightarrow> card_ge3(Cs) \<Longrightarrow> arrow_conds(I,Cs,F) \<Longrightarrow> \<exists>i\<in>I. dictator(I,Cs,F,i)"
@proof
  @let "N = card(I)"
  @have "I \<approx>\<^sub>S nat_less_range(N)"
  @obtain "h \<in> I \<cong> nat_less_range(N)"
  @obtain "a\<in>Cs" "b\<in>Cs" where "a \<noteq> b"
  @obtain "P\<in>nat\<rightarrow>Prof(I,Cs)" where "\<forall>n\<in>nat. \<forall>i\<in>I. ifb h`i \<ge>\<^sub>\<nat> n then prefer(P`n`i,a,b) else prefer(P`n`i,b,a)"
  @have "prefer(F`(P`0),a,b)" @with
    @have "\<forall>i\<in>I. prefer(P`0`i,a,b)" @with
      @have "ifb h`i \<ge>\<^sub>\<nat> 0 then prefer(P`0`i,a,b) else prefer(P`0`i,b,a)" @end @end
  @have "prefer(F`(P`N),b,a)" @with
    @have "\<forall>i\<in>I. prefer(P`N`i,b,a)" @with
      @have "ifb h`i \<ge>\<^sub>\<nat> N then prefer(P`N`i,a,b) else prefer(P`N`i,b,a)" @end @end
  @obtain n where "n <\<^sub>\<nat> N" "\<not>prefer(F`(P`n),b,a) \<and> prefer(F`(P`(n +\<^sub>\<nat> 1)),b,a)"
  @have "dictator(I,Cs,F, inverse(h)`n)" @with
    @have "\<forall>P'\<in>Prof(I,Cs). \<forall>a' b'. prefer(P'`(inverse(h)`n),a',b') \<longrightarrow> prefer(F`P',a',b')" @with
      @obtain "c'\<in>Cs" where "distinct3(Cs,a',b',c')"
      @obtain "P''\<in>Prof(I,Cs)" where "\<forall>i\<in>I. (
        ifb h`i <\<^sub>\<nat> n then eq_prefer(P'`i,a',b', P''`i,a',b') \<and> prefer(P''`i,a',c') \<and> prefer(P''`i,b',c') else
        ifb h`i >\<^sub>\<nat> n then eq_prefer(P'`i,a',b', P''`i,a',b') \<and> prefer(P''`i,c',a') \<and> prefer(P''`i,c',b') else
        prefer3(P''`i,a',c',b'))"
      @have "eq_prefer(F`P',a',b', F`P'',a',b')" @with
        @have "\<forall>i\<in>I. eq_prefer(P'`i,a',b', P''`i,a',b')" @end
      @have "eq_prefer(F`P'',c',b', F`(P`n),a,b)" @with
        @have "\<forall>i\<in>I. eq_prefer(P''`i,c',b', P`n`i,a,b)"
        @have "strict_neutral(I,Cs,F,c',b',a,b)" @end
      @have "eq_prefer(F`P'',a',c', F`(P`(n +\<^sub>\<nat> 1)),b,a)" @with
        @have "\<forall>i\<in>I. eq_prefer(P''`i,a',c', P`(n +\<^sub>\<nat> 1)`i,b,a)" @with
           @have "ifb h`i \<ge>\<^sub>\<nat> n +\<^sub>\<nat> 1 then prefer(P`(n +\<^sub>\<nat> 1)`i,a,b) else prefer(P`(n +\<^sub>\<nat> 1)`i,b,a)" @end
        @have "strict_neutral(I,Cs,F,a',c',b,a)"
      @end
    @end
  @end
@qed

no_notation less ("prefer")

end
