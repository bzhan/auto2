theory Graph
imports "../Auto2_Main"
begin

lemma last_eval1 [rewrite]: "last [x] = x" by simp
lemma last_eval2 [rewrite]: "last [u, v] = v" by simp
lemma last_cons [rewrite]: "xs \<noteq> [] \<Longrightarrow> last (x # xs) = last xs" by simp
lemma last_append [rewrite]: "ys \<noteq> [] \<Longrightarrow> last (xs @ ys) = last ys" by simp

lemma butlast_eval2 [rewrite]: "butlast [x, y] = [x]" by simp
lemma butlast_cons [rewrite]: "as \<noteq> [] \<Longrightarrow> butlast (a # as) = a # butlast as" by simp
lemma butlast_append' [rewrite]: "bs \<noteq> [] \<Longrightarrow> butlast (as @ bs) = as @ butlast bs"
  by (simp add: butlast_append)

lemma butlast_last [rewrite]: "as \<noteq> [] \<Longrightarrow> butlast as @ [last as] = as" by simp

lemma last_mem [resolve]: "xs \<noteq> [] \<Longrightarrow> last xs \<in> set xs" by simp

lemma set_two [rewrite]: "set [u, v] = {u, v}" by simp
lemma set_two_mem [rewrite]: "{u, v} \<subseteq> S \<longleftrightarrow> u \<in> S \<and> v \<in> S" by simp
lemma mem_diff [rewrite]: "x \<in> A - B \<longleftrightarrow> x \<in> A \<and> x \<notin> B" by simp

section {* Graphs *}

datatype graph = Graph "nat list list"

fun size :: "graph \<Rightarrow> nat" where
  "size (Graph G) = length G"

fun weight :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "weight (Graph G) m n = (G ! m) ! n"

fun valid_graph :: "graph \<Rightarrow> bool" where
  "valid_graph (Graph G) \<longleftrightarrow> (\<forall>i<length G. length (G ! i) = length G)"
setup {* add_rewrite_rule @{thm valid_graph.simps} *}

section {* Paths on graphs *}

(* The set of vertices less than n. *)
definition verts :: "graph \<Rightarrow> nat set" where
  "verts G = {i. i < size G}"

lemma verts_mem [rewrite]: "i \<in> verts G \<longleftrightarrow> i < size G" by (simp add: verts_def)

definition is_path :: "graph \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "is_path G p \<longleftrightarrow> p \<noteq> [] \<and> set p \<subseteq> verts G"

lemma is_path_to_in_verts [forward]: "is_path G p \<Longrightarrow> hd p \<in> verts G \<and> last p \<in> verts G"
@proof @have "last p \<in> set p" @qed

definition joinable :: "graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "joinable G p q \<longleftrightarrow> (is_path G p \<and> is_path G q \<and> last p = hd q)"

definition path_join :: "graph \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> nat list" where [rewrite]:
  "path_join G p q = p @ tl q"
setup {* register_wellform_data ("path_join G p q", ["joinable G p q"]) *}
setup {* add_prfstep_check_req ("path_join G p q", "joinable G p q") *}

lemma path_join_is_path:
  "joinable G p q \<Longrightarrow> is_path G (path_join G p q)" by auto2
setup {* add_forward_prfstep_cond @{thm path_join_is_path} [with_term "path_join ?G ?p ?q"] *}

fun path_weight :: "graph \<Rightarrow> nat list \<Rightarrow> nat" where
  "path_weight G [] = 0"
| "path_weight G [x] = 0"
| "path_weight G (x # y # ys) = weight G x y + path_weight G (y # ys)"
setup {* fold add_rewrite_rule @{thms path_weight.simps} *}

lemma path_weight_sum [rewrite]:
  "joinable G p q \<Longrightarrow> path_weight G (path_join G p q) = path_weight G p + path_weight G q"
@proof @induct p @qed

fun path_set :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list set" where
  "path_set G m n = {p. is_path G p \<and> hd p = m \<and> last p = n}"

lemma path_set_mem [rewrite]:
  "p \<in> path_set G m n \<longleftrightarrow> is_path G p \<and> hd p = m \<and> last p = n" by simp

lemma path_join_set: "joinable G p q \<Longrightarrow> path_join G p q \<in> path_set G (hd p) (last q)"
@proof @case "tl q = []" @qed
setup {* add_forward_prfstep_cond @{thm path_join_set} [with_term "path_join ?G ?p ?q"] *}

section {* Shortest paths *}

definition is_shortest_path :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where [rewrite]:
  "is_shortest_path G m n p \<longleftrightarrow>
     (p \<in> path_set G m n \<and> (\<forall>p'\<in>path_set G m n. path_weight G p' \<ge> path_weight G p))"

lemma is_shortest_pathD1 [forward]:
  "is_shortest_path G m n p \<Longrightarrow> p \<in> path_set G m n" by auto2

lemma is_shortest_pathD2 [forward]:
  "is_shortest_path G m n p \<Longrightarrow> p' \<in> path_set G m n \<Longrightarrow> path_weight G p' \<ge> path_weight G p" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_shortest_path_def} *}

definition has_dist :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_dist G m n \<longleftrightarrow> (\<exists>p. is_shortest_path G m n p)"

lemma has_distI [forward]: "is_shortest_path G m n p \<Longrightarrow> has_dist G m n" by auto2
lemma has_distD [resolve]: "has_dist G m n \<Longrightarrow> \<exists>p. is_shortest_path G m n p" by auto2
lemma has_dist_to_in_verts [forward]: "has_dist G u v \<Longrightarrow> u \<in> verts G \<and> v \<in> verts G" by auto2
setup {* del_prfstep_thm @{thm has_dist_def} *}

definition dist :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where [rewrite]:
  "dist G m n = path_weight G (SOME p. is_shortest_path G m n p)"
setup {* register_wellform_data ("dist G m n", ["has_dist G m n"]) *}

lemma dist_eq [rewrite]:
  "is_shortest_path G m n p \<Longrightarrow> dist G m n = path_weight G p" by auto2

lemma distD [forward]:
  "has_dist G m n \<Longrightarrow> p \<in> path_set G m n \<Longrightarrow> path_weight G p \<ge> dist G m n" by auto2
setup {* del_prfstep_thm @{thm dist_def} *}

lemma shortest_init [resolve]: "n \<in> verts G \<Longrightarrow> is_shortest_path G n n [n]" by auto2

section {* Interior points *}

(* List of interior points *)
definition int_pts :: "nat list \<Rightarrow> nat set" where [rewrite]:
  "int_pts p = set (butlast p)"

definition path_set_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat list set" where
  "path_set_on G m n V = {p. p \<in> path_set G m n \<and> int_pts p \<subseteq> V}"

lemma path_set_on_mem [rewrite]:
  "p \<in> path_set_on G m n V \<longleftrightarrow> p \<in> path_set G m n \<and> int_pts p \<subseteq> V" by (simp add: path_set_on_def)

(* Version of shortest path on a set of points *)
definition is_shortest_path_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "is_shortest_path_on G m n p V \<longleftrightarrow>
    (p \<in> path_set_on G m n V \<and> (\<forall>p'\<in>path_set_on G m n V. path_weight G p' \<ge> path_weight G p))"

lemma is_shortest_path_onD1 [forward]:
  "is_shortest_path_on G m n p V \<Longrightarrow> p \<in> path_set_on G m n V" by auto2

lemma is_shortest_path_onD2 [forward]:
  "is_shortest_path_on G m n p V \<Longrightarrow> p' \<in> path_set_on G m n V \<Longrightarrow> path_weight G p' \<ge> path_weight G p" by auto2
setup {* del_prfstep_thm_eqforward @{thm is_shortest_path_on_def} *}

definition has_dist_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "has_dist_on G m n V \<longleftrightarrow> (\<exists>p. is_shortest_path_on G m n p V)"

lemma has_dist_onI [forward]: "is_shortest_path_on G m n p V \<Longrightarrow> has_dist_on G m n V" by auto2
lemma has_dist_onD [resolve]: "has_dist_on G m n V \<Longrightarrow> \<exists>p. is_shortest_path_on G m n p V" by auto2
setup {* del_prfstep_thm @{thm has_dist_on_def} *}

definition dist_on :: "graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat set \<Rightarrow> nat" where [rewrite]:
  "dist_on G m n V = path_weight G (SOME p. is_shortest_path_on G m n p V)"
setup {* register_wellform_data ("dist_on G m n V", ["has_dist_on G m n V"]) *}

lemma dist_on_eq [rewrite]:
  "is_shortest_path_on G m n p V \<Longrightarrow> dist_on G m n V = path_weight G p" by auto2

lemma dist_onD [forward]:
  "has_dist_on G m n V \<Longrightarrow> p \<in> path_set_on G m n V \<Longrightarrow> path_weight G p \<ge> dist_on G m n V" by auto2
setup {* del_prfstep_thm @{thm dist_on_def} *}

section {* Two splitting lemmas *}

lemma path_split1 [backward]: "is_path G p \<Longrightarrow> hd p \<in> V \<Longrightarrow> last p \<notin> V \<Longrightarrow>
  \<exists>p1 p2. joinable G p1 p2 \<and> p = path_join G p1 p2 \<and> int_pts p1 \<subseteq> V \<and> hd p2 \<notin> V"
@proof @induct p @with
  @subgoal "p = a # p'"
    @let "p = a # p'"
    @case "p' = []" @then
    @case "hd p' \<notin> V" @with @have "p = path_join G [a, hd p'] p'" @end
    @obtain p1 p2 where "joinable G p1 p2" "p' = path_join G p1 p2" "int_pts p1 \<subseteq> V" "hd p2 \<notin> V"
    @have "p = path_join G (a # p1) p2"
  @endgoal @end
@qed

lemma path_split2 [backward]: "is_path G p \<Longrightarrow> hd p \<noteq> last p \<Longrightarrow>
  \<exists>q n. joinable G q [n, last p] \<and> p = path_join G q [n, last p]"
@proof
  @have "p = butlast p @ [last p]"
  @have "butlast p \<noteq> []"
  @let "n = last (butlast p)"
  @have "p = path_join G (butlast p) [n, last p]"
@qed

section {* Deriving has_dist and has_dist_on *}

definition known_dists :: "graph \<Rightarrow> nat set \<Rightarrow> bool" where [rewrite]:
  "known_dists G V \<longleftrightarrow> (V \<subseteq> verts G \<and> 0 \<in> V \<and>
      (\<forall>i\<in>verts G. has_dist_on G 0 i V) \<and>
      (\<forall>i\<in>V. has_dist G 0 i \<and> dist G 0 i = dist_on G 0 i V))"

lemma derive_dist [backward2]:
  "known_dists G V \<Longrightarrow>
   m \<in> verts G - V \<Longrightarrow>
   \<forall>i\<in>verts G - V. dist_on G 0 i V \<ge> dist_on G 0 m V \<Longrightarrow>
   has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
@proof
  @obtain p where "is_shortest_path_on G 0 m p V"
  @have "is_shortest_path G 0 m p" @with
    @have "p \<in> path_set G 0 m"
    @have "\<forall>p'\<in>path_set G 0 m. path_weight G p' \<ge> path_weight G p" @with
      @obtain p1 p2 where "joinable G p1 p2" "p' = path_join G p1 p2" "int_pts p1 \<subseteq> V" "hd p2 \<notin> V"
      @let "x = last p1"
      @have "dist_on G 0 x V \<ge> dist_on G 0 m V"
      @have "p1 \<in> path_set_on G 0 x V"
      @have "path_weight G p1 \<ge> dist_on G 0 x V"
      @have "path_weight G p' \<ge> dist_on G 0 m V + path_weight G p2"
    @end
  @end
@qed

lemma join_def' [resolve]: "joinable G p q \<Longrightarrow> path_join G p q = butlast p @ q"
@proof
  @have "p = butlast p @ [last p]"
  @have "path_join G p q = butlast p @ [last p] @ tl q"
@qed

lemma int_pts_join [rewrite]:
  "joinable G p q \<Longrightarrow> int_pts (path_join G p q) = int_pts p \<union> int_pts q"
@proof @have "path_join G p q = butlast p @ q" @qed

lemma dist_on_triangle_ineq [backward]:
  "has_dist_on G k m V \<Longrightarrow> has_dist_on G k n V \<Longrightarrow> V \<subseteq> verts G \<Longrightarrow> n \<in> verts G \<Longrightarrow> m \<in> V \<Longrightarrow>
   dist_on G k m V + weight G m n \<ge> dist_on G k n V"
@proof
  @obtain p where "is_shortest_path_on G k m p V"
  @let "q = [m, n]"
  @let "pq = path_join G p q"
  @have "V \<union> {m} = V"
  @have "pq \<in> path_set_on G k n V"
@qed

lemma derive_dist_on [backward2]:
  "known_dists G V \<Longrightarrow>
   m \<in> verts G - V \<Longrightarrow>
   \<forall>i\<in>verts G - V. dist_on G 0 i V \<ge> dist_on G 0 m V \<Longrightarrow>
   V' = V \<union> {m} \<Longrightarrow>
   n \<in> verts G - V' \<Longrightarrow>
   has_dist_on G 0 n V' \<and> dist_on G 0 n V' = min (dist_on G 0 n V) (dist_on G 0 m V + weight G m n)"
@proof
  @have "has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
  @let "M = min (dist_on G 0 n V) (dist_on G 0 m V + weight G m n)"
  @have "\<forall>p\<in>path_set_on G 0 n V'. path_weight G p \<ge> M" @with
    @obtain q n' where "joinable G q [n', n]" "p = path_join G q [n', n]"
    @have "q \<in> path_set G 0 n'"
    @have "n' \<in> V'"
    @case "n' \<in> V" @with
      @have "dist_on G 0 n' V = dist G 0 n'"
      @have "path_weight G q \<ge> dist_on G 0 n' V"
      @have "path_weight G p \<ge> dist_on G 0 n' V + weight G n' n"
      @have "dist_on G 0 n' V + weight G n' n \<ge> dist_on G 0 n V"
    @end
    @have "n' = m"
    @have "path_weight G q \<ge> dist G 0 m"
    @have "path_weight G p \<ge> dist G 0 m + weight G m n"
  @end
  @case "dist_on G 0 m V + weight G m n \<ge> dist_on G 0 n V" @with
    @obtain p where "is_shortest_path_on G 0 n p V"
    @have "is_shortest_path_on G 0 n p V'" @with
      @have "p \<in> path_set_on G 0 n V'" @with @have "V \<subseteq> V'" @end
    @end
  @end
  @have "M = dist_on G 0 m V + weight G m n"
  @obtain pm where "is_shortest_path_on G 0 m pm V"
  @have "path_weight G pm = dist G 0 m"
  @let "p = path_join G pm [m, n]"
  @have "joinable G pm [m, n]"
  @have "path_weight G p = path_weight G pm + weight G m n"
  @have "is_shortest_path_on G 0 n p V'"
@qed

section {* States for the Dijkstra's algorithm *}

(* The state consists of an array maintaining the best estimates,
   and a set of vertices for which the shortest distance is known.
 *)
datatype state = State (est: "nat list") (known: "nat set")

setup {* fold add_rewrite_rule @{thms state.sel} *}
setup {* add_forward_prfstep_cond @{thm state.collapse} [with_term "?state"] *}
setup {* add_forward_prfstep (equiv_forward_th @{thm state.simps(1)}) *}

abbreviation est_of :: "state \<Rightarrow> nat \<Rightarrow> nat" where
  "est_of S n \<equiv> (est S) ! n"

(* Invariant: for every vertex, the estimate is at least the shortest distance.
   Furthermore, for the known vertices the estimate is exact. *)
definition inv :: "graph \<Rightarrow> state \<Rightarrow> bool" where [rewrite]:
  "inv G S \<longleftrightarrow> (length (est S) = size G \<and> known_dists G (known S) \<and>
                (\<forall>i\<in>known S. est_of S i = dist G 0 i) \<and>
                (\<forall>i\<in>verts G. est_of S i = dist_on G 0 i (known S)))"

lemma invE1 [forward]: "inv G S \<Longrightarrow> length (est S) = size G \<and> known_dists G (known S)" by auto2
lemma invE2 [forward]: "inv G S \<Longrightarrow> i \<in> known S \<Longrightarrow> est_of S i = dist G 0 i" by auto2
lemma invE3 [forward]: "inv G S \<Longrightarrow> i \<in> verts G \<Longrightarrow> est_of S i = dist_on G 0 i (known S)" by auto2
setup {* del_prfstep_thm_str "@eqforward" @{thm inv_def} *}

fun dijkstra_step :: "graph \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> state" where
  "dijkstra_step G m (State e V) =
    (let V' = V \<union> {m};
         e' = list (\<lambda>i. if i \<in> V' then e ! i else min (e ! m + weight G m i) (e ! i)) (size G)
     in State e' V')"
setup {* add_rewrite_rule @{thm dijkstra_step.simps} *}

lemma has_dist_on_larger [backward1]:
  "has_dist G m n \<Longrightarrow> has_dist_on G m n V \<Longrightarrow> dist_on G m n V = dist G m n \<Longrightarrow>
   has_dist_on G m n (V \<union> {x}) \<and> dist_on G m n (V \<union> {x}) = dist G m n"
@proof
  @obtain p where "is_shortest_path_on G m n p V"
  @let "V' = V \<union> {x}"
  @have "p \<in> path_set_on G m n V'" @with @have "V \<subseteq> V'" @end
  @have "is_shortest_path_on G m n p V'"
@qed

lemma dijkstra_step_preserves_inv:
  "inv G (State e V) \<Longrightarrow>
   m \<in> verts G - V \<Longrightarrow>
   \<forall>i\<in>verts G - V. dist_on G 0 i V \<ge> dist_on G 0 m V \<Longrightarrow>
   inv G (dijkstra_step G m (State e V))"
@proof
  @let "V' = V \<union> {m}"
  @have (@rule) "\<forall>i\<in>V. has_dist G 0 i \<and> has_dist_on G 0 i V' \<and> dist_on G 0 i V' = dist G 0 i" @with
    @have "has_dist_on G 0 i V' \<and> dist_on G 0 i V' = dist G 0 i"
  @end
  @have "has_dist G 0 m \<and> dist G 0 m = dist_on G 0 m V"
  @have "has_dist_on G 0 m V' \<and> dist_on G 0 m V' = dist G 0 m"
  @have (@rule) "\<forall>i\<in>verts G - V'. has_dist_on G 0 i V' \<and> dist_on G 0 i V' = min (dist_on G 0 i V) (dist_on G 0 m V + weight G m i)"
@qed

end
