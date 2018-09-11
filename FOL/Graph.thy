(*
  File: Graph.thy
  Author: Bohua Zhan

  Basics of graph of functions (as represented by a set of ordered pairs).
*)

theory Graph
  imports Set
begin

section {* Graphs *}

definition is_graph :: "i \<Rightarrow> o" where [rewrite]:
  "is_graph(G) \<longleftrightarrow> (\<forall>x\<in>G. x = \<langle>fst(x),snd(x)\<rangle>)"

lemma is_graphE [forward]: "is_graph(G) \<Longrightarrow> x \<in> G \<Longrightarrow> x = \<langle>fst(x),snd(x)\<rangle>" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_graph_def} *}

definition gr_source :: "i \<Rightarrow> i" where [rewrite]:
  "gr_source(G) = {fst(p). p \<in> G}"
lemma gr_sourceI [typing2]: "\<langle>a,b\<rangle> \<in> G \<Longrightarrow> a \<in> gr_source(G)" by auto2
lemma gr_sourceE [backward]: "is_graph(G) \<Longrightarrow> a \<in> gr_source(G) \<Longrightarrow> \<exists>b. \<langle>a,b\<rangle>\<in>G" by auto2
setup {* del_prfstep_thm @{thm gr_source_def} *}

definition gr_target :: "i \<Rightarrow> i" where [rewrite]:
  "gr_target(G) = {snd(p). p \<in> G}"
lemma gr_targetI [typing2]: "\<langle>a,b\<rangle> \<in> G \<Longrightarrow> b \<in> gr_target(G)" by auto2
lemma gr_targetE [backward]: "is_graph(G) \<Longrightarrow> b \<in> gr_target(G) \<Longrightarrow> \<exists>a. \<langle>a,b\<rangle>\<in>G" by auto2
setup {* del_prfstep_thm @{thm gr_target_def} *}

definition gr_field :: "i \<Rightarrow> i" where [rewrite]:
  "gr_field(G) = gr_source(G) \<union> gr_target(G)"
lemma gr_fieldI1 [typing2]: "\<langle>a,b\<rangle> \<in> G \<Longrightarrow> a \<in> gr_field(G)" by auto2
lemma gr_fieldI2 [typing2]: "\<langle>a,b\<rangle> \<in> G \<Longrightarrow> b \<in> gr_field(G)" by auto2

definition gr_id :: "i \<Rightarrow> i" where [rewrite]:
  "gr_id(A) = {\<langle>a,a\<rangle>. a \<in> A}"
lemma gr_id_is_graph [forward]: "is_graph(gr_id(A))" by auto2
lemma gr_idI [typing2]: "a \<in> A \<Longrightarrow> \<langle>a,a\<rangle> \<in> gr_id(A)" by auto2
lemma gr_id_iff [rewrite]: "p \<in> gr_id(A) \<longleftrightarrow> (p\<in>A\<times>A \<and> fst(p) = snd(p))" by auto2
setup {* del_prfstep_thm @{thm gr_id_def} *}

definition gr_comp :: "i \<Rightarrow> i \<Rightarrow> i"  (infixr "\<circ>\<^sub>g" 60) where [rewrite]:
  "s \<circ>\<^sub>g r = {p\<in>gr_source(r)\<times>gr_target(s). \<exists>z. \<langle>fst(p),z\<rangle>\<in>r \<and> \<langle>z,snd(p)\<rangle>\<in>s}"

lemma gr_comp_is_graph [forward]: "is_graph(s \<circ>\<^sub>g r)" by auto2
lemma gr_compI [backward2]:
  "\<langle>x,y\<rangle> \<in> r \<Longrightarrow> \<langle>y,z\<rangle> \<in> s \<Longrightarrow> \<langle>x,z\<rangle> \<in> s \<circ>\<^sub>g r" by auto2
lemma gr_compE [forward]:
  "p \<in> s \<circ>\<^sub>g r \<Longrightarrow> \<exists>y. \<langle>fst(p),y\<rangle> \<in> r \<and> \<langle>y,snd(p)\<rangle> \<in> s" by auto2
setup {* del_prfstep_thm @{thm gr_comp_def} *}

section \<open>Evaluation on a graph\<close>

definition is_func_graph :: "i \<Rightarrow> i \<Rightarrow> o" where [rewrite]:
  "is_func_graph(G,X) \<longleftrightarrow> is_graph(G) \<and> gr_source(G) = X \<and> (\<forall>a\<in>X. \<exists>!y. \<langle>a,y\<rangle> \<in> G)"
  
definition func_graphs :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "func_graphs(X,Y) = {G\<in>Pow(X\<times>Y). is_func_graph(G,X)}"

definition graph_eval :: "i \<Rightarrow> i \<Rightarrow> i" where [rewrite]:
  "graph_eval(G,x) = (THE y. \<langle>x,y\<rangle> \<in> G)"

lemma is_func_graphD [forward]:
  "is_func_graph(G,X) \<Longrightarrow> is_graph(G) \<and> gr_source(G) = X" by auto2

lemma is_func_graphD2 [forward]:
  "is_func_graph(G,X) \<Longrightarrow> x \<in> X \<Longrightarrow> \<langle>x, graph_eval(G,x)\<rangle> \<in> G" by auto2

lemma is_func_graphD3 [forward]:
  "is_func_graph(G,X) \<Longrightarrow> \<langle>x,y\<rangle> \<in> G \<Longrightarrow> x \<in> X \<Longrightarrow> graph_eval(G,x) = y" by auto2

lemma graph_eq [backward1]:
  "is_func_graph(G,X) \<Longrightarrow> is_func_graph(H,X) \<Longrightarrow>
   \<forall>x\<in>X. graph_eval(G,x) = graph_eval(H,x) \<Longrightarrow> G = H" by auto2

lemma is_func_graph_cons:
  "is_func_graph(G,X) \<Longrightarrow> a \<notin> X \<Longrightarrow> is_func_graph(cons(\<langle>a,b\<rangle>,G),cons(a,X))"
@proof
  @let "H = cons(\<langle>a,b\<rangle>,G)"
  @have "is_graph(H)"
  @have "\<forall>x\<in>gr_source(H). x \<in> cons(a,X)" @with
    @obtain y where "\<langle>x,y\<rangle> \<in> H"
  @end
  @have "\<forall>c\<in>cons(a,X). \<exists>!y. \<langle>c,y\<rangle> \<in> H" @with
    @case "c = a"
  @end
@qed

lemma is_func_graph_empty: "is_func_graph(\<emptyset>,\<emptyset>)"
@proof
  @have "is_graph(\<emptyset>)"
  @have "\<forall>x\<in>gr_source(\<emptyset>). x \<in> \<emptyset>" @with
    @obtain y where "\<langle>x,y\<rangle> \<in> \<emptyset>"
  @end
@qed

setup {* del_prfstep_thm_eqforward @{thm is_func_graph_def} *}
setup {* del_prfstep_thm @{thm graph_eval_def} *}

section \<open>Graphs from a relation\<close>

definition rel_graph :: "i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> o) \<Rightarrow> i" where [rewrite]:
  "rel_graph(S,R) = {p\<in>S\<times>S. R(fst(p),snd(p))}"

lemma rel_graph_mem [typing]: "rel_graph(S,R) \<in> Pow(S\<times>S)" by auto2
lemma rel_graph_iff [rewrite]: "\<langle>x,y\<rangle> \<in> rel_graph(S,R) \<longleftrightarrow> (x \<in> S \<and> y \<in> S \<and> R(x,y))" by auto2

setup {* del_prfstep_thm @{thm rel_graph_def} *}

end
