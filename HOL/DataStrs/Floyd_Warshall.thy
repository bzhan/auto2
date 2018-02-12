(* Ported from AFP/Floyd_Warshall or Timed_Automata. *)

theory Floyd_Warshall
imports "../Auto2_Main"
begin

section {* Cycles in Lists *}

definition cnt :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where [rewrite]:
  "cnt x xs = length (filter (\<lambda>y. x = y) xs)"

lemma cnt_rev [rewrite]: "cnt x (rev xs) = cnt x xs" by auto2
lemma cnt_append [rewrite]: "cnt x (xs @ ys) = cnt x xs + cnt x ys" by auto2

(* remove_cycles xs x ys:
   If x does not appear in xs, return rev ys @ xs.
   Otherwise, write xs as x1 @ [x] @ x2, where x \<notin> set x2, then return x2. *)
fun remove_cycles :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_cycles [] _ acc = rev acc" |
  "remove_cycles (x#xs) y acc =
    (if x = y then remove_cycles xs y [x] else remove_cycles xs y (x#acc))"
setup {* fold add_rewrite_rule @{thms remove_cycles.simps} *}

lemma remove_cycle_removes [forward_arg1]:
  "cnt x (remove_cycles xs x ys) \<le> max 1 (cnt x ys)"
@proof @induct xs arbitrary ys @qed

lemma remove_cycles_id [rewrite, backward]:
  "x \<notin> set xs \<Longrightarrow> remove_cycles xs x ys = rev ys @ xs"
@proof @induct xs arbitrary ys @qed

lemma remove_cycles_cnt_id [forward_arg1]:
  "cnt y (remove_cycles xs x ys) \<le> cnt y ys + cnt y xs"
@proof @induct xs arbitrary ys x @qed

lemma remove_cycles_begins_with [rewrite]:
  "x \<in> set xs \<Longrightarrow> remove_cycles xs x ys = x # tl (remove_cycles xs x ys) \<and> x \<notin> set (tl (remove_cycles xs x ys))"
@proof @induct xs arbitrary ys @qed

lemma remove_cycles_self [rewrite]:
  "x \<in> set xs \<Longrightarrow> remove_cycles (remove_cycles xs x ys) x zs = remove_cycles xs x ys" by auto2

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
@proof @induct xs arbitrary ys @with
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

lemma start_remove_removes [forward_arg1]:
  "cnt x (start_remove xs x ys) \<le> cnt x ys + 1"
@proof @induct xs arbitrary ys @qed

lemma start_remove_id [rewrite]:
  "x \<notin> set xs \<Longrightarrow> start_remove xs x ys = rev ys @ xs"
@proof @induct xs arbitrary ys @qed

lemma start_remove_cnt_id [forward_arg1]:
  "cnt y (start_remove xs x ys) \<le> cnt y ys + cnt y xs"
@proof @induct xs arbitrary ys @qed

(* *)
fun remove_all_cycles :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "remove_all_cycles [] xs = xs"
| "remove_all_cycles (x # xs) ys = remove_all_cycles xs (start_remove ys x [])"
setup {* fold add_rewrite_rule @{thms remove_all_cycles.simps} *}

lemma cnt_remove_all_mono [forward_arg1]:
  "cnt y (remove_all_cycles xs ys) \<le> max 1 (cnt y ys)"
@proof @induct xs arbitrary ys @qed

lemma cnt_remove_all_cycles [forward_arg1]:
  "x \<in> set xs \<Longrightarrow> cnt x (remove_all_cycles xs ys) \<le> 1"
@proof @induct xs arbitrary ys @qed

lemma cnt_zero [forward]:
  "cnt x xs = 0 \<Longrightarrow> x \<notin> set xs"
@proof @induct xs @qed

lemma cnt_distinct_intro [forward]:
  "\<forall>x\<in>set xs. cnt x xs \<le> 1 \<Longrightarrow> distinct xs"
@proof @induct xs @with
  @subgoal "xs = x # xs"
    @have "\<forall>x'\<in>set xs. cnt x' xs \<le> 1"
    @have "cnt x xs = 0"
  @endgoal @end
@qed

lemma remove_cycles_subs [forward_arg1]:
  "set (remove_cycles xs x ys) \<subseteq> set xs \<union> set ys"
@proof @induct xs arbitrary ys @qed

lemma start_remove_subs [forward_arg1]:
  "set (start_remove xs x ys) \<subseteq> set xs \<union> set ys"
@proof @induct xs arbitrary ys @qed

lemma remove_all_cycles_subs [forward_arg1]:
  "set (remove_all_cycles xs ys) \<subseteq> set ys"
@proof @induct xs arbitrary ys @qed

lemma remove_all_cycles_distinct [forward_arg]:
  "set ys \<subseteq> set xs \<Longrightarrow> zs = remove_all_cycles xs ys \<Longrightarrow> distinct zs"
@proof @have "\<forall>x\<in>set zs. cnt x zs \<le> 1" @qed

lemma distinct_remove_cycles_inv [backward]:
  "distinct (xs @ ys) \<Longrightarrow> distinct (remove_cycles xs x ys)"
@proof @induct xs arbitrary ys @qed

(* *)
definition remove_all :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "remove_all x xs = (if x \<in> set xs then tl (remove_cycles xs x []) else xs)"

lemma remove_all_distinct [backward]:
  "distinct xs \<Longrightarrow> distinct (x # remove_all x xs)" by auto2

lemma remove_all_removes [resolve]:
  "x \<notin> set (remove_all x xs)" by auto2

lemma remove_all_subs [forward_arg1]:
  "set (remove_all x xs) \<subseteq> set xs" by auto2

definition remove_all_rev :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "remove_all_rev x xs = (if x \<in> set xs then rev (tl (remove_cycles (rev xs) x [])) else xs)"

lemma remove_all_rev_distinct [backward]:
  "distinct xs \<Longrightarrow> distinct (x # remove_all_rev x xs)"
@proof
  @case "x \<in> set xs" @with
    @have "distinct (remove_cycles (rev xs) x [])"
  @end
@qed

lemma remove_all_rev_removes [resolve]:
  "x \<notin> set (remove_all_rev x xs)" by auto2

lemma remove_all_rev_subs [forward_arg1]:
  "set (remove_all_rev x xs) \<subseteq> set xs" by auto2

definition rem_cycles :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where [rewrite]:
  "rem_cycles i j xs = remove_all i (remove_all_rev j (remove_all_cycles xs xs))"

lemma rem_cycles_distinct' [backward]:
  "i \<noteq> j \<Longrightarrow> distinct (i # j # rem_cycles i j xs)"
@proof
  @have "distinct (remove_all_cycles xs xs)" @with
    @have "set xs \<subseteq> set xs" @end
  @have "distinct (j # remove_all_rev j (remove_all_cycles xs xs))"
  @have "distinct (i # rem_cycles i j xs)"
@qed

lemma rem_cycles_removes_i [resolve]:
  "i \<notin> set (rem_cycles i j xs)" by auto2

lemma rem_cycles_removes_j [resolve]:
  "j \<notin> set (rem_cycles i j xs)" by auto2

lemma rem_cycles_distinct [forward]:
  "distinct (rem_cycles i j xs)"
@proof
  @case "i \<noteq> j" @with
    @have "distinct (i # j # rem_cycles i j xs)" @end
  @have "distinct (remove_all_cycles xs xs)" @with
    @have "set xs \<subseteq> set xs" @end
  @have "distinct (i # rem_cycles i j xs)"
@qed

lemma rem_cycles_subs [forward_arg1]:
  "set (rem_cycles i j xs) \<subseteq> set xs" by auto2

section {* Matrices *}

datatype 'c mat = Mat (eval_fun: "nat \<Rightarrow> nat \<Rightarrow> 'c")
setup {* add_simple_datatype "mat" *}

fun mat_eval :: "'c mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c" ("_\<langle>_,_\<rangle>" [90,91]) where
  "(Mat f)\<langle>a,b\<rangle> = f a b"
setup {* add_rewrite_rule @{thm mat_eval.simps} *}

lemma mat_eval_ext: "\<forall>x y. M\<langle>x,y\<rangle> = N\<langle>x,y\<rangle> \<Longrightarrow> M = N"
  apply (cases M) apply (cases N) by auto
setup {* add_backward_prfstep_cond @{thm mat_eval_ext} [with_filt (order_filter "M" "N")] *}

fun mat_update :: "'c mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'c mat" ("_ { _,_ \<rightarrow> _}" [89,90,90,90] 90) where
  "(Mat f) {x,y \<rightarrow> v} = Mat (\<lambda>x' y'. if x = x' then if y = y' then v else f x' y' else f x' y')"
setup {* add_rewrite_rule @{thm mat_update.simps} *}

lemma mat_update_eval [rewrite]:
  "M {x,y \<rightarrow> v} \<langle>x',y'\<rangle> = (if x = x' then if y = y' then v else M\<langle>x',y'\<rangle> else M\<langle>x',y'\<rangle>)" by auto2

lemma mat_update_eval' [rewrite]:
  "M {x,y \<rightarrow> v} \<langle>x,y\<rangle> = v"
  "x \<noteq> x' \<Longrightarrow> M {x,y \<rightarrow> v} \<langle>x',y'\<rangle> = M\<langle>x',y'\<rangle>"
  "y \<noteq> y' \<Longrightarrow> M {x,y \<rightarrow> v} \<langle>x',y'\<rangle> = M\<langle>x',y'\<rangle>" by auto2+
setup {* del_simple_datatype "mat" *}

section {* Definition of the Algorithm *}

abbreviation fw_upd :: "('a::linordered_ring) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw_upd M k i j \<equiv> M {i,j \<rightarrow> min (M\<langle>i,j\<rangle>) (M\<langle>i,k\<rangle> + M\<langle>k,j\<rangle>)}"

lemma fw_upd_mono [forward_arg1]:
  "(fw_upd M k i j)\<langle>i',j'\<rangle> \<le> M\<langle>i',j'\<rangle>" by auto2

fun fw :: "('a::linordered_ring) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat" where
  "fw M n 0       0       0        = fw_upd M 0 0 0" |
  "fw M n (Suc k) 0       0        = fw_upd (fw M n k n n) (Suc k) 0 0" |
  "fw M n k       (Suc i) 0        = fw_upd (fw M n k i n) k (Suc i) 0" |
  "fw M n k       i       (Suc j)  = fw_upd (fw M n k i j) k i (Suc j)"
setup {* fold add_rewrite_rule @{thms fw.simps} *}
setup {* register_wellform_data ("fw M n k i j", ["i \<le> n", "j \<le> n", "k \<le> n"]) *}

lemma fw_invariant_aux_1 [backward]:
  "j'' \<le> j \<Longrightarrow> (fw M n k i j)\<langle>i',j'\<rangle> \<le> (fw M n k i j'')\<langle>i',j'\<rangle>"
@proof @induct j @with
  @subgoal "j = Suc j"
    @case "j'' = Suc j"
  @endgoal @end
@qed

lemma fw_invariant_aux_2 [backward]:
  "j \<le> n \<Longrightarrow> i'' \<le> i \<Longrightarrow> j'' \<le> j \<Longrightarrow> (fw M n k i j)\<langle>i',j'\<rangle> \<le> (fw M n k i'' j'')\<langle>i',j'\<rangle>"
@proof @induct i @with
  @subgoal "i = Suc i"
    @case "i'' = Suc i" @then
    @have "(fw M n k (Suc i) j) \<langle>i',j'\<rangle> \<le> (fw M n k (Suc i) 0) \<langle>i',j'\<rangle>"
    @have "(fw M n k (Suc i) 0) \<langle>i',j'\<rangle> \<le> (fw M n k i n) \<langle>i',j'\<rangle>"
    @have "(fw M n k i n) \<langle>i',j'\<rangle> \<le> (fw M n k i j) \<langle>i',j'\<rangle>"
  @endgoal @end
@qed

lemma fw_invariant [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k' \<le> k \<Longrightarrow> j'' \<le> j \<Longrightarrow> i'' \<le> i \<Longrightarrow>
   (fw M n k i j)\<langle>i', j'\<rangle> \<le> (fw M n k' i'' j'')\<langle>i',j'\<rangle>"
@proof @induct k @with
  @subgoal "k = Suc k"
    @case "k' = Suc k" @then
    @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> \<le> (fw M n (Suc k) 0 0)\<langle>i',j'\<rangle>"
    @have "(fw M n (Suc k) 0 0)\<langle>i',j'\<rangle> \<le> (fw M n k n n)\<langle>i',j'\<rangle>"
    @have "(fw M n k n n)\<langle>i',j'\<rangle> \<le> (fw M n k i j)\<langle>i',j'\<rangle>"
  @endgoal @end
@qed

lemma single_row_inv [backward]:
  "j' < j \<Longrightarrow> (fw M n k i' j) \<langle>i',j'\<rangle> = (fw M n k i' j') \<langle>i',j'\<rangle>"
@proof @induct j @qed

lemma single_iteration_inv' [backward]:
  "j' \<le> n \<Longrightarrow> i' < i \<Longrightarrow> (fw M n k i j)\<langle>i',j'\<rangle> = (fw M n k i' j')\<langle>i',j'\<rangle>"
@proof @induct i arbitrary j @with
  @subgoal "i = Suc i" @induct j @endgoal @end
@qed

lemma single_iteration_inv [backward]:
  "j \<le> n \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> (fw M n k i j)\<langle>i',j'\<rangle> = (fw M n k i' j')\<langle>i',j'\<rangle>"
@proof @induct i arbitrary j @qed

lemma fw_innermost_id [rewrite]:
  "j' \<le> n \<Longrightarrow> i' < i \<Longrightarrow> (fw M n 0 i' j')\<langle>i,j\<rangle> = M\<langle>i,j\<rangle>"
@proof
  @induct i' arbitrary j' @with
  @subgoal "i' = 0" @induct j' @endgoal
  @subgoal "i' = Suc i'" @induct j' @endgoal @end
@qed

lemma fw_middle_id [backward]:
  "j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> (fw M n 0 i' j')\<langle>i,j\<rangle> = M\<langle>i,j\<rangle>"
@proof
  @induct i' arbitrary j' @with
  @subgoal "i' = 0" @induct j' @endgoal
  @subgoal "i' = Suc i'" @induct j' @endgoal @end
@qed

lemma fw_outermost_mono [resolve]:
  "(fw M n 0 i j)\<langle>i,j\<rangle> \<le> M\<langle>i,j\<rangle>"
@proof
  @case "j = 0" @with @cases i @end
  @have "(fw M n 0 i (j-1))\<langle>i,j\<rangle> = M\<langle>i,j\<rangle>"
@qed

lemma Suc_innermost_id1 [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' < i \<Longrightarrow> (fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k i j)\<langle>i,j\<rangle>"
@proof @induct i' arbitrary j' @with
  @subgoal "i' = 0" @induct j' @endgoal
  @subgoal "i' = Suc i'" @induct j' @endgoal @end
@qed

lemma Suc_innermost_id2 [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> (fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k i j)\<langle>i,j\<rangle>"
@proof @induct i' arbitrary j' @with
  @subgoal "i' = 0" @induct j' @endgoal
  @subgoal "i' = Suc i'" @induct j' @endgoal @end
@qed

lemma Suc_innermost_id1' [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' < i \<Longrightarrow> (fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k n n)\<langle>i,j\<rangle>"
@proof
  @have "(fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k i j)\<langle>i,j\<rangle>"
@qed

lemma Suc_innermost_id2' [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> j' < j \<Longrightarrow> i' \<le> i \<Longrightarrow> (fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k n n)\<langle>i,j\<rangle>"
@proof
  @have "(fw M n (Suc k) i' j')\<langle>i,j\<rangle> = (fw M n k i j)\<langle>i,j\<rangle>"
@qed

lemma fw_mono' [forward_arg1]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> (fw M n k i j)\<langle>i,j\<rangle> \<le> M\<langle>i,j\<rangle>"
@proof @induct k @with
  @subgoal "k = Suc k"
    @have "(fw M n (Suc k) i j)\<langle>i,j\<rangle> \<le> (fw M n k i j)\<langle>i,j\<rangle>"
  @endgoal @end
@qed

lemma fw_mono [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> (fw M n k i j)\<langle>i',j'\<rangle> \<le> M\<langle>i',j'\<rangle>"
@proof @cases k @with
  @subgoal "k = 0"
    @case "i < i'" @then
    @case "j' \<le> j" @with
      @have "(fw M n 0 i j)\<langle>i',j'\<rangle> \<le> (fw M n 0 i' j')\<langle>i',j'\<rangle>"
    @end
    @case "i = i'" @with
      @have "(fw M n 0 i' j)\<langle>i',j'\<rangle> = M\<langle>i',j'\<rangle>"
    @end
    @have "(fw M n 0 i j)\<langle>i',j'\<rangle> = (fw M n 0 i' j')\<langle>i',j'\<rangle>"
  @endgoal
  @subgoal "k = Suc k"
    @case "i' \<le> i \<and> j' \<le> j" @with
      @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = (fw M n (Suc k) i' j')\<langle>i',j'\<rangle>"
    @end
    @case "\<not>i' \<le> i" @with
      @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = (fw M n k i' j')\<langle>i',j'\<rangle>"
    @end
    @case "\<not>j' \<le> j" @with
      @case "i = i'" @with
        @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = (fw M n k i' j')\<langle>i',j'\<rangle>"
      @end
      @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = (fw M n (Suc k) i' j')\<langle>i',j'\<rangle>"
    @end
  @endgoal @end
@qed

lemma min_plus1 [rewrite]: "(b::'a::linordered_ring) \<ge> 0 \<Longrightarrow> min a (b + a) = a"
@proof @have "b + a \<ge> a" @qed

lemma min_plus2 [rewrite]: "(b::'a::linordered_ring) \<ge> 0 \<Longrightarrow> min a (a + b) = a"
@proof @have "a + b \<ge> a" @qed

lemma fw_step_0 [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> M\<langle>0,0\<rangle> \<ge> 0 \<Longrightarrow> (fw M n 0 i j)\<langle>i,j\<rangle> = min (M\<langle>i,j\<rangle>) (M\<langle>i,0\<rangle> + M\<langle>0,j\<rangle>)"
@proof @induct i @with
  @subgoal "i = 0"
    @have "(fw M n 0 0 0)\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
    @cases j @with
      @subgoal "j = Suc j"
        @let "M' = fw M n 0 0 j"
        @have "M'\<langle>0,Suc j\<rangle> = M\<langle>0,Suc j\<rangle>"
        @have "M'\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
      @endgoal
    @end
  @endgoal
  @subgoal "i = Suc i"
    @have "(fw M n 0 0 0)\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
    @cases j @with
      @subgoal "j = 0"
        @let "M' = fw M n 0 i n"
        @have "M'\<langle>Suc i,0\<rangle> = M\<langle>Suc i,0\<rangle>"
        @have "M'\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
      @endgoal
      @subgoal "j = Suc j"
        @have "(fw M n 0 0 (Suc j))\<langle>0,Suc j\<rangle> = M\<langle>0,Suc j\<rangle>" @with
          @have "(fw M n 0 0 j)\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
        @end
        @have "(fw M n 0 (Suc i) (Suc j))\<langle>0,Suc j\<rangle> = M\<langle>0,Suc j\<rangle>"
        @have "(fw M n 0 (Suc i) 0)\<langle>Suc i,0\<rangle> = M\<langle>Suc i,0\<rangle>" @with
          @have "(fw M n 0 i n)\<langle>0,0\<rangle> = M\<langle>0,0\<rangle>"
        @end
        @have "(fw M n 0 (Suc i) j)\<langle>Suc i,0\<rangle> = M\<langle>Suc i,0\<rangle>"
        @have "(fw M n 0 (Suc i) j)\<langle>Suc i,Suc j\<rangle> = M\<langle>Suc i,Suc j\<rangle>"
      @endgoal
    @end
  @endgoal @end
@qed

lemma fw_step_Suc [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> M' = fw M n k n n \<Longrightarrow> \<forall>k'\<le>n. M'\<langle>k',k'\<rangle> \<ge> 0 \<Longrightarrow> Suc k \<le> n \<Longrightarrow>
   (fw M n (Suc k) i j)\<langle>i,j\<rangle> = min (M'\<langle>i,j\<rangle>) (M'\<langle>i,Suc k\<rangle> + M'\<langle>Suc k,j\<rangle>)"
@proof @induct i @with
  @subgoal "i = 0"
    @cases j @with
      @subgoal "j = Suc j"
        @have "(fw M n (Suc k) 0 j)\<langle>0,Suc j\<rangle> = M'\<langle>0,Suc j\<rangle>"
        @have "(fw M n (Suc k) 0 j)\<langle>0,Suc k\<rangle> = M'\<langle>0,Suc k\<rangle>" @with
          @case "j < Suc k" @then
          @have "(fw M n (Suc k) 0 k)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>"
          @have "(fw M n (Suc k) 0 j)\<langle>0,Suc k\<rangle> = (fw M n (Suc k) 0 (Suc k))\<langle>0,Suc k\<rangle>"
        @end
        @have "(fw M n (Suc k) 0 j)\<langle>Suc k,Suc j\<rangle> = M'\<langle>Suc k,Suc j\<rangle>"
      @endgoal
    @end
  @endgoal
  @subgoal "i = Suc i"
    @cases j @with
      @subgoal "j = 0"
        @have "(fw M n (Suc k) i n)\<langle>Suc i,0\<rangle> = M'\<langle>Suc i,0\<rangle>"
        @have "(fw M n (Suc k) i n)\<langle>Suc i,Suc k\<rangle> = M'\<langle>Suc i,Suc k\<rangle>"
        @have "(fw M n (Suc k) i n)\<langle>Suc k,0\<rangle> = M'\<langle>Suc k,0\<rangle>" @with
          @case "i < Suc k" @then
          @have "(fw M n (Suc k) k n)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>"
          @have "(fw M n (Suc k) i n)\<langle>Suc k,0\<rangle> = (fw M n (Suc k) (Suc k) 0)\<langle>Suc k,0\<rangle>"
        @end
      @endgoal
      @subgoal "j = Suc j"
        @have "(fw M n (Suc k) (Suc i) j)\<langle>Suc i,Suc j\<rangle> = M'\<langle>Suc i,Suc j\<rangle>"
        @have "(fw M n (Suc k) (Suc i) j)\<langle>Suc i,Suc k\<rangle> = M'\<langle>Suc i,Suc k\<rangle>" @with
          @case "j < Suc k" @then
          @have "(fw M n (Suc k) (Suc i) k)\<langle>Suc i,Suc k\<rangle> = M'\<langle>Suc i,Suc k\<rangle>"
          @have "(fw M n (Suc k) (Suc i) k)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>" @with
            @case "Suc i \<le> Suc k" @then
            @have "(fw M n (Suc k) (Suc i) k)\<langle>Suc k,Suc k\<rangle> = (fw M n (Suc k) (Suc k) (Suc k))\<langle>Suc k,Suc k\<rangle>"
            @have "(fw M n (Suc k) (Suc k) k)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>"
          @end
          @have "(fw M n (Suc k) (Suc i) j)\<langle>Suc i,Suc k\<rangle> = (fw M n (Suc k) (Suc i) (Suc k))\<langle>Suc i,Suc k\<rangle>"
        @end
        @have "(fw M n (Suc k) (Suc i) j)\<langle>Suc k,Suc j\<rangle> = M'\<langle>Suc k,Suc j\<rangle>" @with
          @case "Suc i \<le> Suc k" @then
          @have "(fw M n (Suc k) (Suc k) j)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>" @with
            @case "j < Suc k" @then
            @have "(fw M n (Suc k) (Suc k) j)\<langle>Suc k,Suc k\<rangle> = (fw M n (Suc k) (Suc k) (Suc k))\<langle>Suc k,Suc k\<rangle>"
            @have "(fw M n (Suc k) (Suc k) k)\<langle>Suc k,Suc k\<rangle> = M'\<langle>Suc k,Suc k\<rangle>"
          @end
          @have "(fw M n (Suc k) (Suc k) (Suc j))\<langle>Suc k,Suc j\<rangle> = M'\<langle>Suc k,Suc j\<rangle>"
        @end
      @endgoal
    @end
  @endgoal @end
@qed

subsection {* Length of paths *}

fun len :: "('a::linordered_ring) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'a" where
  "len M u v [] = M\<langle>u,v\<rangle>" |
  "len M u v (w # ws) = M\<langle>u,w\<rangle> + len M w v ws"
setup {* fold add_rewrite_rule @{thms len.simps}*}

lemma len_decomp [rewrite]:
  "len M x z (ys @ y # zs) = len M x y ys + len M y z zs"
@proof @induct ys arbitrary x @qed

subsection {* Shortening Negative Cycles *}

lemma remove_cycles_neg_cycles_aux [backward1]:
  "xs' = i # ys \<Longrightarrow> i \<notin> set ys \<Longrightarrow>
   xs = as @ concat (map (\<lambda>xs. i # xs) xss) @ xs' \<Longrightarrow> i \<in> set xs \<Longrightarrow>
   len M i j ys > len M i j xs \<Longrightarrow>
   \<exists>ys. set ys \<subseteq> set xs \<and> len M i i ys < 0"
@proof @induct xss arbitrary xs as @with
  @subgoal "xss = []"
    @case "len M i i as \<ge> 0" @with
      @have "len M i j ys \<le> len M i j xs"
    @end
  @endgoal
  @subgoal "xss = zs # xss"
    @let "xs'' = zs @ concat (map (\<lambda>xs. i # xs) xss) @ xs'"
    @case "len M i i as \<ge> 0" @with
      @have "len M i j xs'' \<le> len M i j xs"
    @end
  @endgoal @end
@qed

lemma remove_cycles_neg_cycles_aux' [backward1]:
  "j \<notin> set ys \<Longrightarrow>
   xs = ys @ j # concat (map (\<lambda>xs. xs @ [j]) xss) @ as \<Longrightarrow> j \<in> set xs \<Longrightarrow>
   len M i j ys > len M i j xs \<Longrightarrow> 
   \<exists>ys. set ys \<subseteq> set xs \<and> len M j j ys < 0"
@proof @induct xss arbitrary xs as @with
  @subgoal "xss = []"
    @case "len M j j as \<ge> 0" @with
      @have "len M i j ys \<le> len M i j xs"
    @end
  @endgoal
  @subgoal "xss = zs # xss"
    @let "xs'' = ys @ j # concat (map (\<lambda>xs. xs @ [j]) xss) @ as"
    @let "t = concat (map (\<lambda>xs. xs @ [j]) xss) @ as"
    @case "len M i j xs'' \<le> len M i j xs" @then
    @have "len M j j (concat (map (\<lambda>xs. xs @ [j]) (zs # xss)) @ as) < len M j j t"
    @have "len M j j (zs @ j # t) < len M j j t"
  @endgoal @end
@qed

lemma start_remove_neg_cycles [resolve]:
  "len M i j (start_remove xs k []) > len M i j xs \<Longrightarrow>
   \<exists>ys. set ys \<subseteq> set xs \<and> len M k k ys < 0"
@proof
  @let "xs' = start_remove xs k []"
  @case "len M i j xs' > len M i j xs" @with
    @have "k \<in> set xs"
    @obtain as bs where "xs = as @ k # bs" "xs' = rev [] @ as @ remove_cycles bs k [k]"
    @have "xs' = as @ remove_cycles bs k [k]"
    @let "xs'' = remove_cycles bs k [k]"
    @have "k \<in> set bs"
    @have "len M k j bs < len M k j (tl xs'')"
    @obtain xss as' where "as' @ concat (map (\<lambda>xs. k # xs) xss) @ xs'' = bs \<and> k \<notin> set as'"
    @have "as' @ concat (map (\<lambda>xs. k # xs) xss) @ k # (tl xs'') = bs"
    @obtain ys' where "set ys' \<subseteq> set bs \<and> len M k k ys' < 0"
  @end
@qed

lemma remove_all_cycles_neg_cycles [resolve]:
  "len M i j (remove_all_cycles ys xs) > len M i j xs \<Longrightarrow>
   \<exists>ys k. set ys \<subseteq> set xs \<and> k \<in> set xs \<and> len M k k ys < 0"
@proof @induct ys arbitrary xs @with
  @subgoal "ys = y # ys"
    @let "xs' = start_remove xs y []"
    @case "len M i j xs < len M i j xs'" @with
      @have "y \<in> set xs"
      @obtain ys' where "set ys' \<subseteq> set xs \<and> len M y y ys' < 0"
    @end
  @endgoal @end
@qed

lemma concat_map_cons_rev [rewrite]:
  "rev (concat (map (\<lambda>xs. j # xs) xss)) = concat (map (\<lambda>xs. xs @ [j]) (rev (map rev xss)))"
  by (induction xss) auto

lemma negative_cycle_dest [resolve]:
  "len M i j (rem_cycles i j xs) > len M i j xs \<Longrightarrow>
   \<exists>i' ys. len M i' i' ys < 0 \<and> set ys \<subseteq> set xs \<and> i' \<in> set (i # j # xs)"
@proof
  @let "xsij = rem_cycles i j xs"
  @let "xs' = remove_all_cycles xs xs"
  @let "xsj = remove_all_rev j xs'"
  @case "len M i j xsij > len M i j xs" @with
    @case "len M i j xsij \<le> len M i j xsj" @with
      @have "len M i j xsj > len M i j xs"
      @case "len M i j xsj \<le> len M i j xs'" @with
        @obtain ys k where "set ys \<subseteq> set xs \<and> k \<in> set xs \<and> len M k k ys < 0"
      @end
      @have "len M i j xsj > len M i j xs'"
      @case "j \<notin> set xs'"
      @have "j \<notin> set xsj"
      @have "j \<in> set (rev xs')"
      @obtain xss as where "as @ concat (map (\<lambda>xs. j # xs) xss) @ remove_cycles (rev xs') j [] = rev xs'" "j \<notin> set as"
      @have "xsj = rev (tl (remove_cycles (rev xs') j []))"
      @have "xsj @ j # concat (map (\<lambda>xs. xs @ [j]) (rev (map rev xss))) @ rev as = xs'" @with
        @have "remove_cycles (rev xs') j [] = j # rev xsj"
        @have "rev (as @ concat (map (\<lambda>xs. j # xs) xss) @ j # rev xsj) = xs'"
        @have "xsj @ j # rev (concat (map (\<lambda>xs. j # xs) xss)) @ rev as = xs'"
      @end
      @obtain ys where "set ys \<subseteq> set xs' \<and> len M j j ys < 0"
    @end
    @case "i \<notin> set xsj"
    @have "i \<notin> set xsij"
    @obtain xss as where "as @ concat (map (\<lambda>xs. i # xs) xss) @ remove_cycles xsj i [] = xsj" "i \<notin> set as"
    @have "xsij = tl (remove_cycles xsj i [])"
    @have "remove_cycles xsj i [] = i # xsij"
    @have "as @ concat (map (\<lambda>xs. i # xs) xss) @ i # xsij = xsj"
    @obtain ys where "set ys \<subseteq> set xsj \<and> len M i i ys < 0"
  @end
@qed

setup {* del_prfstep_thm @{thm rem_cycles_def} *}

section {* Definition of shortest paths *}

definition D :: "('a::linordered_ring) mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where [rewrite]:
  "D M i j k = Min {len M i j xs | xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"

lemma distinct_length_le [resolve]:
  "finite s \<Longrightarrow> distinct xs \<Longrightarrow> set xs \<subseteq> s \<Longrightarrow> length xs \<le> card s"
@proof @have "card (set xs) \<le> card s" @qed

lemma finite_distinct [forward_arg]:
  "finite s \<Longrightarrow> finite {xs . set xs \<subseteq> s \<and> distinct xs}"
@proof
  @have "{xs . set xs \<subseteq> s \<and> distinct xs} \<subseteq> {xs. set xs \<subseteq> s \<and> length xs \<le> card s}"
  @have "finite {xs. set xs \<subseteq> s \<and> length xs \<le> card s}"
@qed

lemma D_base_finite [forward_arg]:
  "finite {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct xs}" by auto2

lemma D_base_finite' [forward_arg]:
  "finite {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
@proof
  @have "{len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}
       \<subseteq> {len m i j xs | xs. set xs \<subseteq> {0..k} \<and> distinct xs}"
@qed

definition cycle_free :: "'a::linordered_ring mat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "cycle_free M n = (\<forall>i\<le>n. \<forall>j\<le>n. \<forall>xs. set xs \<subseteq> {0..n} \<longrightarrow>
      len M i j (rem_cycles i j xs) \<le> len M i j xs \<and> len M i i xs \<ge> 0)"

lemma cycle_freeD1 [backward2]:
  "cycle_free M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow>
   len M i j (rem_cycles i j xs) \<le> len M i j xs" by auto2

lemma cycle_freeD2 [backward2]:
  "cycle_free M n \<Longrightarrow> i \<le> n \<Longrightarrow> set xs \<subseteq> {0..n} \<Longrightarrow> len M i i xs \<ge> 0" by auto2
setup {* del_prfstep_thm_eqforward @{thm cycle_free_def} *}

lemma D_eqI [backward2]:
  "A = {len M i j xs | xs. set xs \<subseteq> {0..k}} \<Longrightarrow>
   A' = {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs} \<Longrightarrow>
   cycle_free M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> \<forall>y\<in>A'. x \<le> y \<Longrightarrow> x \<in> A \<Longrightarrow>
   D M i j k = x"
@proof
  @let "S = {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "\<forall>y\<in>S. x \<le> y"
  @have "x \<in> S" @with
    @obtain xs where "x = len M i j xs" "set xs \<subseteq> {0..k}"
    @let "y = len M i j (rem_cycles i j xs)"
    @have "y \<le> x"
    @have "y \<in> A'"
  @end
@qed

lemma D_base_not_empty [resolve]:
   "{len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs} \<noteq> {}"
@proof
  @have "len M i j [] \<in> {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
@qed

lemma D_dest [resolve]:
  "\<exists>xs. D m i j k = len m i j xs \<and> set xs \<subseteq> {0..Suc k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs"
@proof
  @let "S = {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "D m i j k \<in> S"
@qed

lemma D_dest' [resolve]:
  "\<exists>xs. D m i j k = len m i j xs \<and> set xs \<subseteq> {0..Suc k}"
@proof
  @let "S = {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "D m i j k \<in> S"
@qed

lemma D_dest'' [resolve]:
  "\<exists>xs. D m i j k = len m i j xs \<and> set xs \<subseteq> {0..k}"
@proof
  @let "S = {len m i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "D m i j k \<in> S"
@qed

definition cycle_free_up_to :: "'a::linordered_ring mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "cycle_free_up_to M k n = (\<forall>i\<le>n. \<forall>j\<le>n. \<forall>xs. set xs \<subseteq> {0..k} \<longrightarrow>
      len M i j (rem_cycles i j xs) \<le> len M i j xs \<and> len M i i xs \<ge> 0)"

lemma cycle_free_up_toD1 [backward2]:
  "cycle_free_up_to M k n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> set xs \<subseteq> {0..k} \<Longrightarrow>
   len M i j (rem_cycles i j xs) \<le> len M i j xs" by auto2

lemma cycle_free_up_toD2 [backward2]:
  "cycle_free_up_to M k n \<Longrightarrow> i \<le> n \<Longrightarrow> set xs \<subseteq> {0..k} \<Longrightarrow> len M i i xs \<ge> 0" by auto2
setup {* del_prfstep_thm_eqforward @{thm cycle_free_up_to_def} *}

lemma cycle_free_up_to_diag [backward2]:
  "cycle_free_up_to M k n \<Longrightarrow> i \<le> n \<Longrightarrow> M\<langle>i,i\<rangle> \<ge> 0"
@proof @have "len M i i [] \<ge> 0" @qed

lemma D_eqI2 [backward2]:
  "A = {len M i j xs | xs. set xs \<subseteq> {0..k}} \<Longrightarrow>
   A' = {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs} \<Longrightarrow>
   cycle_free_up_to M k n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow> \<forall>y\<in>A'. x \<le> y \<Longrightarrow> x \<in> A \<Longrightarrow>
   D M i j k = x"
@proof
  @let "S = {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "x \<in> S" @with
    @obtain xs where "x = len M i j xs" "set xs \<subseteq> {0..k}"
    @let "y = len M i j (rem_cycles i j xs)"
    @have "y \<le> x" @have "y \<in> A'"
  @end
@qed

section {* Result under the absence of negative cycles *}

lemma distinct_list_single_elem_decomp [resolve]:
  "distinct xs \<Longrightarrow> set xs \<subseteq> {0} \<Longrightarrow> xs = [] \<or> xs = [0::'a::zero]"
@proof
  @case "xs = []" @then @have "xs = hd xs # tl xs"
  @case "tl xs = []" @then @have "tl xs = hd (tl xs) # tl (tl xs)"
@qed

theorem fw_shortest_path_up_to [backward2]:
  "cycle_free_up_to M k n \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow>
   D M i' j' k = (fw M n k i j)\<langle>i',j'\<rangle>"
@proof @induct k arbitrary i j i' j' @with
  @subgoal "k = 0"
    @have "{(0::nat)..0} = {0}"
    @let "S = {len M i' j' xs |xs. set xs \<subseteq> {0} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
    @have "\<forall>l\<in>S. (fw M n 0 i j)\<langle>i',j'\<rangle> \<le> l" @with
      @obtain xs where "l = len M i' j' xs" "set xs \<subseteq> {0}" "distinct xs"
      @have (@rule) "xs = [] \<or> xs = [0]"
      @case "xs = [0]" @with
        @have "(fw M n 0 i j)\<langle>i',j'\<rangle> \<le> (fw M n 0 i' j')\<langle>i',j'\<rangle>"
        @have "(fw M n 0 i' j')\<langle>i',j'\<rangle> \<le> M\<langle>i',0\<rangle> + M\<langle>0,j'\<rangle>" @with
          @cases j' @with @subgoal "j' = Suc j'"
            @have "(fw M n 0 i' j')\<langle>i',0\<rangle> + (fw M n 0 i' j')\<langle>0,Suc j'\<rangle> \<le> M\<langle>i',0\<rangle> + M\<langle>0,Suc j'\<rangle>" @with
              @have "(fw M n 0 i' j')\<langle>0,Suc j'\<rangle> \<le> M\<langle>0,Suc j'\<rangle>"
            @end
          @endgoal @end
        @end
      @end
    @end
    @have "(fw M n 0 i j)\<langle>i',j'\<rangle> = (fw M n 0 i' j')\<langle>i',j'\<rangle>"
    @have "(fw M n 0 i' j')\<langle>i',j'\<rangle> = min (M\<langle>i',j'\<rangle>) (M\<langle>i',0\<rangle> + M\<langle>0,j'\<rangle>)"
    @have "(fw M n 0 i j)\<langle>i',j'\<rangle> \<in> S" @with
      @case "M\<langle>i',j'\<rangle> \<le> M\<langle>i',0\<rangle> + M\<langle>0,j'\<rangle>" @with
        @have "(fw M n 0 i j)\<langle>i',j'\<rangle> = len M i' j' []"
      @end
      @have "M\<langle>i',0\<rangle> + M\<langle>0,j'\<rangle> \<le> M\<langle>i',j'\<rangle>"
      @have "M\<langle>i',0\<rangle> + M\<langle>0,j'\<rangle> = len M i' j' [0]"
    @end
  @endgoal
  @subgoal "k = Suc k"
    @have "\<forall>k'\<le>n. (fw M n k n n)\<langle>k',k'\<rangle> \<ge> 0" @with
      @have "D M k' k' k = (fw M n k n n)\<langle>k',k'\<rangle>"
      @have "(fw M n k n n)\<langle>k',k'\<rangle> \<in> {len M k' k' xs |xs. set xs \<subseteq> {0..k}}"
    @end
    @let "S = {len M i' j' xs | xs. set xs \<subseteq> {0..Suc k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
    @have "\<forall>l\<in>S. (fw M n (Suc k) i j)\<langle>i',j'\<rangle> \<le> l" @with
      @obtain xs where "l = len M i' j' xs" "set xs \<subseteq> {0..Suc k}" "i' \<notin> set xs" "j' \<notin> set xs" "distinct xs"
      @have "D M i' j' k = (fw M n k i j)\<langle>i',j'\<rangle>"
      @case "Suc k \<notin> set xs" @with
        @have "set xs \<subseteq> {0..k}"
        @have "l \<in> {len M i' j' xs | xs. set xs \<subseteq> {0..k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
        @have "(fw M n k i j)\<langle>i',j'\<rangle> \<le> l"
        @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> \<le> (fw M n k i j)\<langle>i',j'\<rangle>"
      @end
      @case "Suc k \<in> set xs" @with
        @obtain ys zs where "xs = ys @ Suc k # zs"
  
        @have "(fw M n k n n)\<langle>i',Suc k\<rangle> \<le> len M i' (Suc k) ys" @with
          @have "set ys \<subseteq> {0..k}"
          @let "S1 = {len M i' (Suc k) xs |xs. set xs \<subseteq> {0..k} \<and> i' \<notin> set xs \<and> Suc k \<notin> set xs \<and> distinct xs}"
          @have "len M i' (Suc k) ys \<in> S1"
          @have "Min S1 \<le> len M i' (Suc k) ys"
          @have "(fw M n k n n)\<langle>i',Suc k\<rangle> = D M i' (Suc k) k"
        @end
  
        @have "(fw M n k n n)\<langle>Suc k,j'\<rangle> \<le> len M (Suc k) j' zs" @with
          @have "set zs \<subseteq> {0..k}"
          @let "S2 = {len M (Suc k) j' xs |xs. set xs \<subseteq> {0..k} \<and> Suc k \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
          @have "len M (Suc k) j' zs \<in> S2"
          @have "Min S2 \<le> len M (Suc k) j' zs"
          @have "(fw M n k n n)\<langle>Suc k,j'\<rangle> = D M (Suc k) j' k"
        @end
  
        @have "l = len M i' (Suc k) ys + len M (Suc k) j' zs"
        @have "(fw M n (Suc k) i' j')\<langle>i',j'\<rangle> = min ((fw M n k n n)\<langle>i',j'\<rangle>)
                  ((fw M n k n n)\<langle>i',Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j'\<rangle>)"
        @have "((fw M n k n n)\<langle>i',Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j'\<rangle>) \<le> l"
        @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> \<le> (fw M n (Suc k) i' j')\<langle>i',j'\<rangle>"
      @end
    @end
    @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = (fw M n (Suc k) i' j')\<langle>i',j'\<rangle>"
    @have "(fw M n (Suc k) i' j')\<langle>i',j'\<rangle> =
             min ((fw M n k n n)\<langle>i',j'\<rangle>) ((fw M n k n n)\<langle>i',Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j'\<rangle>)"
    @case "(fw M n k n n)\<langle>i',j'\<rangle> \<le> (fw M n k n n)\<langle>i',Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j'\<rangle>" @with
      @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = D M i' j' k"
    @end
    @have "(fw M n k n n)\<langle>i',Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j'\<rangle> \<le> (fw M n k n n)\<langle>i',j'\<rangle>"
    @have "(fw M n k n n)\<langle>i',j'\<rangle> = D M i' j' k"
    @have "(fw M n k n n)\<langle>i',j'\<rangle> \<in> {len M i' j' xs |xs. set xs \<subseteq> {0..Suc k} \<and> i' \<notin> set xs \<and> j' \<notin> set xs \<and> distinct xs}"
    @obtain xs where "(fw M n k n n)\<langle>i',Suc k\<rangle> = len M i' (Suc k) xs" "set xs \<subseteq> {0..Suc k}" @with
      @have "(fw M n k n n)\<langle>i',Suc k\<rangle> = D M i' (Suc k) k"
    @end
    @obtain ys where "(fw M n k n n)\<langle>Suc k,j'\<rangle> = len M (Suc k) j' ys" "set ys \<subseteq> {0..Suc k}" @with
      @have "(fw M n k n n)\<langle>Suc k,j'\<rangle> = D M (Suc k) j' k"
    @end
    @have "(fw M n (Suc k) i j)\<langle>i',j'\<rangle> = len M i' j' (xs @ Suc k # ys)"
    @have "set (xs @ Suc k # ys) \<subseteq> {0..Suc k}"
  @endgoal @end
@qed

corollary fw_shortest_path:
  "cycle_free M n \<Longrightarrow> i' \<le> i \<Longrightarrow> j' \<le> j \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow>
   D M i' j' k = (fw M n k i j)\<langle>i',j'\<rangle>"
@proof @have "cycle_free_up_to M k n" @qed

corollary fw_shortest:
  "cycle_free M n \<Longrightarrow> i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> k \<le> n \<Longrightarrow>
   (fw M n n n n)\<langle>i,j\<rangle> \<le> (fw M n n n n)\<langle>i,k\<rangle> + (fw M n n n n)\<langle>k,j\<rangle>"
@proof
  @have "cycle_free_up_to M n n"
  @let "FW = fw M n n n n"
  @have "FW\<langle>i,j\<rangle> = D M i j n" @have "FW\<langle>i,k\<rangle> = D M i k n" @have "FW\<langle>k,j\<rangle> = D M k j n"
  @obtain xs where "FW\<langle>i,k\<rangle> = len M i k xs" "set xs \<subseteq> {0..n}"
  @obtain ys where "FW\<langle>k,j\<rangle> = len M k j ys" "set ys \<subseteq> {0..n}"
  @let "zs = rem_cycles i j (xs @ k # ys)"
  @have "FW\<langle>i,j\<rangle> = Min {len M i j xs |xs. set xs \<subseteq> {0..n} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "set (xs @ k # ys) \<subseteq> {0..n}"
  @have "len M i j zs \<le> len M i j (xs @ k # ys)"
  @have "i \<notin> set zs" @have "j \<notin> set zs" @have "distinct zs"
  @have "set zs \<subseteq> {0..n}"
  @have "len M i j zs \<in> {len M i j xs |xs. set xs \<subseteq> {0..n} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs}"
  @have "FW\<langle>i,j\<rangle> \<le> len M i j zs"
@qed

section {* Result under the presence of negative cycles *}

lemma D_not_diag_le [resolve]:
  "x \<in> {len M i j xs |xs. set xs \<subseteq> {0..k} \<and> i \<notin> set xs \<and> j \<notin> set xs \<and> distinct xs} \<Longrightarrow>
   D M i j k \<le> x" by auto2

lemma D_not_diag_le' [backward]:
  "distinct xs \<Longrightarrow> set xs \<subseteq> {0..k} \<Longrightarrow> i \<notin> set xs \<Longrightarrow> j \<notin> set xs \<Longrightarrow>
   D M i j k \<le> len M i j xs" by auto2

lemma fw_Suc [backward]:
  "i \<le> n \<Longrightarrow> j \<le> n \<Longrightarrow> i' \<le> n \<Longrightarrow> j' \<le> n \<Longrightarrow> (fw M n (Suc k) i' j')\<langle>i,j\<rangle> \<le> (fw M n k n n)\<langle>i,j\<rangle>"
  by (metis Suc_innermost_id1' Suc_innermost_id2 Suc_n_not_le_n fw_invariant linear not_less
            single_iteration_inv single_iteration_inv')

lemma negative_len_shortest [backward]:
  "len M i i xs < 0 \<Longrightarrow> \<exists>j ys. distinct (j # ys) \<and> len M j j ys < 0 \<and> j \<in> set (i # xs) \<and> set ys \<subseteq> set xs"
@proof
  @let "n = length xs"
  @strong_induct n arbitrary xs i
  @case "xs = []"
  @case "i \<in> set xs" @with
    @obtain as bs where "xs = as @ i # bs"
    @have "length xs = length as + length bs + 1"
    @case "len M i i as < 0" @with
      @apply_induct_hyp "length as" as i
    @end
    @have "len M i i xs = len M i i as + len M i i bs"
    @apply_induct_hyp "length bs" bs i
  @end
  @case "i \<notin> set xs" @with
    @case "distinct xs"
    @obtain a as bs cs where "xs = as @ [a] @ bs @ [a] @ cs"
    @case "len M a a bs < 0" @with
      @have "length bs < n"
      @apply_induct_hyp "length bs" bs a
    @end
    @have "len M i i (as @ a # cs) < 0" @with
      @have "len M i i xs = len M i a as + (len M a a bs + len M a i cs)"
      @have "len M a a bs + len M a i cs \<ge> len M a i cs"
      @have "len M i a as + len M a i cs < 0"
    @end
    @have "length (as @ a # cs) < n" @with
      @have "length xs = length bs + (length as + length cs + 2)"
      @have "length (as @ a # cs) = length as + length cs + 1"
      @have "length (as @ a # cs) < length as + length cs + 2"
    @end
    @apply_induct_hyp "length (as @ a # cs)" "as @ a # cs" i
  @end
@qed

theorem FW_neg_cycle_detect:
  "\<not>cycle_free M n \<Longrightarrow> \<exists>i\<le>n. (fw M n n n n)\<langle>i,i\<rangle> < 0"
@proof
  @let "K = {k. k \<le> n \<and> \<not>cycle_free_up_to M k n}"
  @have "K \<noteq> {}" @with
    @have "n \<in> {k. k \<le> n \<and> \<not>cycle_free_up_to M k n}"
  @end
  @have "finite K" @with @have "K \<subseteq> {0..n}" @end
  @let "k = Min K"
  @have "\<forall>k'<k. cycle_free_up_to M k' n"
  @have "\<not>cycle_free_up_to M k n \<and> k \<le> n" @with
    @have "k \<in> {k. k \<le> n \<and> \<not>cycle_free_up_to M k n}"
  @end
  @obtain as a where "a \<le> n" "len M a a as < 0" "set as \<subseteq> {0..k}" @with
    @contradiction
    @have (@rule) "\<forall>i\<le>n. \<forall>j\<le>n. \<forall>xs. set xs \<subseteq> {0..k} \<longrightarrow>
                   len M i j (rem_cycles i j xs) \<le> len M i j xs" @with
      @contradiction
      @obtain i' ys where "len M i' i' ys < 0" "set ys \<subseteq> set xs" "i' \<in> set (i # j # xs)"
    @end
  @end
  @obtain j xs where "distinct (j # xs)" "len M j j xs < 0" "j \<in> set (a # as)" "set xs \<subseteq> set as"
  @cases k @with
    @subgoal "k = 0"
      @have (@rule) "xs = [] \<or> xs = [0]" @with
        @have "set xs \<subseteq> {0}"
      @end
      @case "xs = []" @with
        @have "(fw M n n n n)\<langle>j,j\<rangle> \<le> M\<langle>j,j\<rangle>"
      @end
      @case "xs = [0]" @with
        @have "M\<langle>j,0\<rangle> + M\<langle>0,j\<rangle> < 0"
        @have "(fw M n 0 j j)\<langle>j,j\<rangle> < 0" @with
          @cases j @with @subgoal "j = Suc j"
            @have "(fw M n 0 (Suc j) (Suc j))\<langle>Suc j,Suc j\<rangle> \<le> (fw M n 0 (Suc j) j)\<langle>Suc j,0\<rangle> + (fw M n 0 (Suc j) j)\<langle>0,Suc j\<rangle>"
            @have "(fw M n 0 (Suc j) j)\<langle>Suc j,0\<rangle> + (fw M n 0 (Suc j) j)\<langle>0,Suc j\<rangle> \<le> M\<langle>Suc j,0\<rangle> + M\<langle>0,Suc j\<rangle>" @with
              @have "(fw M n 0 (Suc j) j)\<langle>0,Suc j\<rangle> \<le> M\<langle>0,Suc j\<rangle>"
            @end
          @endgoal @end
        @end
        @have "(fw M n n n n)\<langle>j,j\<rangle> \<le> (fw M n 0 j j)\<langle>j,j\<rangle>"
      @end
    @endgoal
    @subgoal "k = Suc k"
      @have "cycle_free_up_to M k n"
      @have "Suc k \<in> set xs" @with
        @contradiction
        @have "set xs \<subseteq> {0..k}"
        @have "len M j j xs \<ge> 0"
      @end
      @obtain ys zs where "xs = ys @ Suc k # zs"
      @have "set ys \<subseteq> {0..k}"
      @have "set zs \<subseteq> {0..k}"
      @have "(fw M n k n n)\<langle>j,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j\<rangle> \<le> len M j (Suc k) ys + len M (Suc k) j zs" @with
        @have "D M j (Suc k) k = (fw M n k n n)\<langle>j,Suc k\<rangle>"
        @have "D M (Suc k) j k = (fw M n k n n)\<langle>Suc k,j\<rangle>"
        @have "(fw M n k n n)\<langle>Suc k,j\<rangle> \<le> len M (Suc k) j zs"
      @end
      @have "(fw M n k n n)\<langle>j,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j\<rangle> < 0"
      @have "(fw M n (Suc k) j j)\<langle>j,j\<rangle> \<le> (fw M n k n n)\<langle>j,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,j\<rangle>" @with
        @cases j @with
          @subgoal "j = 0"
            @have "(fw M n (Suc k) 0 0)\<langle>0,0\<rangle> \<le> (fw M n k n n)\<langle>0,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,0\<rangle>"
          @endgoal
          @subgoal "j = Suc j"
            @let "M1 = fw M n (Suc k) (Suc j) j" "M2 = fw M n (Suc k) (Suc j) (Suc j)"
            @have "M2\<langle>Suc j,Suc j\<rangle> \<le> (fw M n k n n)\<langle>Suc j,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,Suc j\<rangle>" @with
              @have "M2\<langle>Suc j,Suc j\<rangle> \<le> M1\<langle>Suc j,Suc k\<rangle> + M1\<langle>Suc k,Suc j\<rangle>"
              @have "M1\<langle>Suc j,Suc k\<rangle> + M1\<langle>Suc k,Suc j\<rangle> \<le> (fw M n k n n)\<langle>Suc j,Suc k\<rangle> + (fw M n k n n)\<langle>Suc k,Suc j\<rangle>" @with
                @have "M1\<langle>Suc k,Suc j\<rangle> \<le> (fw M n k n n)\<langle>Suc k,Suc j\<rangle>"
              @end
            @end
          @endgoal
        @end
      @end
      @have "(fw M n n n n)\<langle>j,j\<rangle> \<le> (fw M n (Suc k) j j)\<langle>j,j\<rangle>"
    @endgoal
  @end
@qed

end
