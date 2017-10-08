theory Percolation_Func
imports Union_Find_Func
begin

section {* Connectedness for a set of undirected edges. *}

fun is_path :: "(nat \<times> nat) set \<Rightarrow> nat list \<Rightarrow> bool" where
  "is_path S [] = False"
| "is_path S [x] = True"
| "is_path S (x # y # ys) = (((x, y) \<in> S \<or> (y, x) \<in> S) \<and> is_path S (y # ys))"
setup {* fold add_rewrite_rule @{thms is_path.simps} *}

definition has_path :: "(nat \<times> nat) set \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_path S i j \<longleftrightarrow> (\<exists>p. is_path S p \<and> hd p = i \<and> last p = j)"

lemma is_path_nonempty [forward]: "is_path S p \<Longrightarrow> p \<noteq> []" by auto2
lemma nonempty_is_not_path [resolve]: "\<not>is_path S []" by auto2

lemma is_path_extend [forward]:
  "is_path S p \<Longrightarrow> S \<subseteq> T \<Longrightarrow> is_path T p"
@proof @induct p @with
  @subgoal "p = x # xs" @case "xs = []" @endgoal @end
@qed

lemma has_path_extend [forward]:
  "has_path S i j \<Longrightarrow> S \<subseteq> T \<Longrightarrow> has_path T i j" by auto2

definition joinable :: "nat list \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "joinable p q \<longleftrightarrow> (last p = hd q)"

definition path_join :: "nat list \<Rightarrow> nat list \<Rightarrow> nat list" where [rewrite]:
  "path_join p q = p @ tl q"
setup {* register_wellform_data ("path_join p q", ["joinable p q"]) *}
setup {* add_prfstep_check_req ("path_join p q", "joinable p q") *}

lemma path_join_hd [rewrite]: "p \<noteq> [] \<Longrightarrow> hd (path_join p q) = hd p" by auto2

lemma path_join_last [rewrite]: "joinable p q \<Longrightarrow> q \<noteq> [] \<Longrightarrow> last (path_join p q) = last q"
@proof @case "tl q = []" @qed

lemma path_join_is_path [backward]:
  "joinable p q \<Longrightarrow> is_path S p \<Longrightarrow> is_path S q \<Longrightarrow> is_path S (path_join p q)"
@proof @induct p @with
  @subgoal "p = x # xs" @case "xs = []" @endgoal @end
@qed

lemma has_path_trans [forward]:
  "has_path S i j \<Longrightarrow> has_path S j k \<Longrightarrow> has_path S i k"
@proof
  @obtain p where "is_path S p" "hd p = i" "last p = j"
  @obtain q where "is_path S q" "hd q = j" "last q = k"
  @have "is_path S (path_join p q)"
@qed

lemma has_path_single1 [resolve]: "(a, b) \<in> S \<Longrightarrow> has_path S a b"
@proof @have "is_path S [a, b]" @qed

lemma has_path_single2 [resolve]: "(a, b) \<in> S \<Longrightarrow> has_path S b a"
@proof @have "is_path S [b, a]" @qed

lemma has_path_refl [resolve]: "has_path S a a"
@proof @have "is_path S [a]" @qed

definition connected_rel :: "(nat \<times> nat) set \<Rightarrow> (nat \<times> nat) set" where
  "connected_rel S = {(a,b). has_path S a b}"

lemma connected_rel_iff [rewrite]:
  "(a, b) \<in> connected_rel S \<longleftrightarrow> has_path S a b" using connected_rel_def by simp

lemma connected_rel_trans [forward]:
  "trans (connected_rel S)" by auto2

lemma is_path_per_union [rewrite]:
  "has_path (S \<union> {(a, b)}) i j \<longleftrightarrow> (i, j) \<in> per_union (connected_rel S) a b"
@proof
  @let "R = connected_rel S"
  @let "S' = S \<union> {(a, b)}" @have "S \<subseteq> S'"
  @case "(i, j) \<in> per_union R a b" @with
    @case "(i, a) \<in> R \<and> (b, j) \<in> R" @with
      @have "has_path S' i a" @have "has_path S' a b" @have "has_path S' b j"
    @end
    @case "(i, b) \<in> R \<and> (a, j) \<in> R" @with
      @have "has_path S' i b" @have "has_path S' b a" @have "has_path S' a j"
    @end
  @end
  @case "has_path S' i j" @with
    @have (@rule) "\<forall>p. is_path S' p \<longrightarrow> (hd p, last p) \<in> per_union R a b" @with
      @induct p @with
      @subgoal "p = x # xs" @case "xs = []"
        @have "(x, hd xs) \<in> per_union R a b"
      @endgoal @end
    @end
    @obtain p where "is_path S' p" "hd p = i" "last p = j"
  @end
@qed

lemma connected_rel_union [rewrite]:
  "connected_rel (S \<union> {(a, b)}) = per_union (connected_rel S) a b" by auto2

end
