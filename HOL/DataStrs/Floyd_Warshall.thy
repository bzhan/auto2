(* Ported from AFP/Floyd_Warshall or Timed_Automata. *)

theory Floyd_Warshall
imports "../Auto2_Main"
begin

section {* Auxiliary *}

lemma distinct_list_single_elem_decomp:
  "{xs. set xs \<subseteq> {0} \<and> distinct xs} = {[], [0::'a::zero]}"
@proof
  @have "\<forall>x. x\<in>{xs. set xs \<subseteq> {0} \<and> distinct xs} \<longleftrightarrow> x\<in>{[], [0::'a]}" @with
    @case "x\<in>{xs. set xs \<subseteq> {0} \<and> distinct xs}" @with
      @case "x = []" @then @have "x = hd x # tl x"
      @case "tl x = []" @then @have "tl x = hd (tl x) # tl (tl x)"
    @end
  @end
@qed

section {* Cycles in Lists *}

definition cnt :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where [rewrite]:
  "cnt x xs = length (filter (\<lambda>y. x = y) xs)"

lemma cnt_rev [rewrite]:
  "cnt x (rev xs) = cnt x xs" by auto2

(* remove_cycles xs x ys:
   If x does not appear in xs, return rev ys @ xs.
   Otherwise, write xs as x1 @ [x] @ x2, where x \<notin> set x2, then return x2. *)
fun remove_cycles :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_cycles [] _ acc = rev acc" |
  "remove_cycles (x#xs) y acc =
    (if x = y then remove_cycles xs y [x] else remove_cycles xs y (x#acc))"
setup {* fold add_rewrite_rule @{thms remove_cycles.simps} *}

lemma remove_cycle_removes:
  "cnt x (remove_cycles xs x ys) \<le> max 1 (cnt x ys)"
@proof @induct xs arbitrary ys @qed
setup {* add_forward_prfstep_cond @{thm remove_cycle_removes} [with_term "cnt ?x (remove_cycles ?xs ?x ?ys)"] *}

lemma remove_cycles_id [rewrite, backward]:
  "x \<notin> set xs \<Longrightarrow> remove_cycles xs x ys = rev ys @ xs"
@proof @induct xs arbitrary ys @with
  @subgoal "xs = x1 # x2"
    @have "x1 # x2 = [x1] @ x2"
  @endgoal @end
@qed

lemma remove_cycles_cnt_id:
  "x \<noteq> y \<Longrightarrow> cnt y (remove_cycles xs x ys) \<le> cnt y ys + cnt y xs"
@proof @induct xs arbitrary ys x @qed
setup {* add_forward_prfstep_cond @{thm remove_cycles_cnt_id} [with_term "remove_cycles ?xs ?x ?ys"] *}

lemma remove_cycles_begins_with [backward]:
  "x \<in> set xs \<Longrightarrow> \<exists>zs. remove_cycles xs x ys = x # zs \<and> x \<notin> set zs"
@proof @induct xs arbitrary ys @qed

lemma remove_cycles_self [rewrite]:
  "x \<in> set xs \<Longrightarrow> remove_cycles (remove_cycles xs x ys) x zs = remove_cycles xs x ys"
@proof
  @obtain ws where "remove_cycles xs x ys = x # ws" "x \<notin> set ws"
@qed

lemma remove_cycles_one [rewrite]:
  "remove_cycles (as @ x # xs) x ys = remove_cycles (x # xs) x ys"
@proof @induct as arbitrary ys @qed

lemma remove_cycles_same [backward]:
  "x \<in> set xs \<Longrightarrow> remove_cycles xs x ys1 = remove_cycles xs x ys2"
@proof @induct xs arbitrary ys1 @qed

lemma remove_cycles_tl [rewrite]:
  "x \<in> set x2 \<Longrightarrow> remove_cycles (x1 # x2) x ys = remove_cycles x2 x ys" by auto2

lemma remove_cycles_cycles [backward]:
  "x \<in> set xs \<Longrightarrow> \<exists>xxs as. as @ concat (map (\<lambda>xs. x # xs) xxs) @ remove_cycles xs x ys = xs \<and> x \<notin> set as"
@proof @induct xs arbitrary ys @with
  @subgoal "xs = y # xs"
    @case "y = x" @with
      @case "x \<in> set xs" @with
        @obtain xxs as where "as @ concat (map (\<lambda>xs. x # xs) xxs) @ remove_cycles xs x ys = xs" "x \<notin> set as"
        @have "[] @ concat (map (\<lambda>xs. x#xs) (as#xxs)) @ remove_cycles (y # xs) x ys = y # xs"
      @end
      @case "x \<notin> set xs" @with
        @have "[] @ concat (map (\<lambda>xs. x # xs) []) @ remove_cycles (y#xs) x ys = y # xs"
      @end
    @end
    @case "y \<noteq> x" @with
      @obtain xxs as where "as @ concat (map (\<lambda>xs. x # xs) xxs) @ remove_cycles xs x ys = xs" "x \<notin> set as"
      @have "(y # as) @ concat (map (\<lambda>xs. x#xs) xxs) @ remove_cycles (y#xs) x ys = y # xs"
    @end
  @endgoal @end
@qed

(* *)
fun start_remove :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "start_remove [] _ acc = rev acc"
| "start_remove (x # xs) y acc =
    (if x = y then rev acc @ remove_cycles xs y [y] else start_remove xs y (x # acc))"
setup {* fold add_rewrite_rule @{thms start_remove.simps} *}

lemma start_remove_decomp [backward]:
  "x \<in> set xs \<Longrightarrow> \<exists>as bs. xs = as @ x # bs \<and> start_remove xs x ys = rev ys @ as @ remove_cycles bs x [x]"
@proof
  @induct xs arbitrary ys @with
  @subgoal "xs = []" @endgoal
  @subgoal "xs = y # xs"
  @case "x = y" @with
    @have "start_remove (y # xs) x ys = rev ys @ [] @ remove_cycles xs x [x]"
  @end
  @case "x \<noteq> y" @with
    @obtain as bs where "xs = as @ x # bs"
                        "start_remove xs x (y # ys) = rev (y # ys) @ as @ remove_cycles bs x [x]"
    @have "start_remove xs x (y # ys) = rev ys @ ([y] @ as) @ remove_cycles bs x [x]"
  @end
  @endgoal @end
@qed

lemma start_remove_removes:
  "cnt x (start_remove xs x ys) \<le> cnt x ys + 1"
@proof @induct xs arbitrary ys @with
  @subgoal "xs = y # xs"
    @case "x = y" @with
      @have "cnt y (remove_cycles xs y [y]) \<le> 1"
    @end
  @endgoal @end
@qed
setup {* add_forward_prfstep_cond @{thm start_remove_removes} [with_term "start_remove ?xs ?x ?ys"] *}

lemma start_remove_id [rewrite]:
  "x \<notin> set xs \<Longrightarrow> start_remove xs x ys = rev ys @ xs"
@proof @induct xs arbitrary ys @with
  @subgoal "xs = x1 # x2"
    @have "x1 # x2 = [x1] @ x2"
  @endgoal @end
@qed

lemma start_remove_cnt_id:
  "x \<noteq> y \<Longrightarrow> cnt y (start_remove xs x ys) \<le> cnt y ys + cnt y xs"
@proof @induct xs arbitrary ys @qed
setup {* add_forward_prfstep_cond @{thm start_remove_cnt_id} [with_term "start_remove ?xs ?x ?ys"] *}

end
