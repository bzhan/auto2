theory Rect_Intersect
imports Interval_Tree
begin

section {* Definition of rectangles *}

datatype 'a rectangle = Rectangle (xint: "'a interval") (yint: "'a interval")
setup {* add_rewrite_rule_back @{thm rectangle.collapse} *}
setup {* add_rewrite_rule @{thm rectangle.case} *}
setup {* fold add_rewrite_rule @{thms rectangle.sel} *}

definition is_rect :: "('a::linorder) rectangle \<Rightarrow> bool" where [rewrite]:
  "is_rect rect \<longleftrightarrow> is_interval (xint rect) \<and> is_interval (yint rect)"
setup {* add_property_const @{term is_rect} *}

definition is_rect_list :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "is_rect_list rects \<longleftrightarrow> (\<forall>i<length rects. is_rect (rects ! i))"
setup {* add_property_const @{term is_rect_list} *}

lemma is_rect_listD: "is_rect_list rects \<Longrightarrow> i < length rects \<Longrightarrow> is_rect (rects ! i)" by auto2
setup {* add_forward_prfstep_cond @{thm is_rect_listD} [with_term "?rects ! ?i"] *}

setup {* del_prfstep_thm_eqforward @{thm is_rect_list_def} *}

definition is_rect_overlap :: "('a::linorder) rectangle \<Rightarrow> ('a::linorder) rectangle \<Rightarrow> bool" where [rewrite]:
  "is_rect_overlap A B \<longleftrightarrow> (is_overlap (xint A) (xint B) \<and> is_overlap (yint A) (yint B))"

definition has_rect_overlap :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "has_rect_overlap As \<longleftrightarrow> (\<exists>i<length As. \<exists>j<length As. i \<noteq> j \<and> is_rect_overlap (As ! i) (As ! j))"

section {* INS / DEL operations *}

datatype ('a::linorder) operation =
  INS (pos: 'a) (idx: nat) (int: "'a interval")
| DEL (pos: 'a) (idx: nat) (int: "'a interval")
setup {* fold add_rewrite_rule_back @{thms operation.collapse} *}
setup {* fold add_rewrite_rule @{thms operation.sel} *}
setup {* fold add_rewrite_rule @{thms operation.simps(1-2)} *}
setup {* add_resolve_prfstep @{thm operation.simps(3)} *}
setup {* add_forward_prfstep_cond @{thm operation.disc(1)} [with_term "INS ?x11.0 ?x12.0 ?x13.0"] *}
setup {* add_forward_prfstep_cond @{thm operation.disc(2)} [with_term "DEL ?x21.0 ?x22.0 ?x23.0"] *}

instantiation operation :: (linorder) linorder begin

definition less: "(a < b) = (if pos a \<noteq> pos b then pos a < pos b else
                             if is_INS a \<noteq> is_INS b then is_INS a > is_INS b
                             else if idx a \<noteq> idx b then idx a < idx b else int a < int b)"
definition less_eq: "(a \<le> b) = (if pos a \<noteq> pos b then pos a < pos b else
                              if is_INS a \<noteq> is_INS b then is_INS a > is_INS b
                              else if idx a \<noteq> idx b then idx a < idx b else int a \<le> int b)"

instance proof
  fix x y z :: "'a operation"
  show a: "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (smt Rect_Intersect.less Rect_Intersect.less_eq leD le_cases3 not_less_iff_gr_or_eq)
  show b: "x \<le> x"
    by (simp add: local.less_eq)
  show c: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (smt Rect_Intersect.less Rect_Intersect.less_eq a dual_order.trans less_trans)
  show d: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (metis Rect_Intersect.less Rect_Intersect.less_eq a le_imp_less_or_eq operation.expand)
  show e: "x \<le> y \<or> y \<le> x"
    using local.less_eq by fastforce
qed end

setup {* fold add_rewrite_rule [@{thm less_eq}, @{thm less}] *}

lemma operation_leD [forward]:
  "(a::('a::linorder operation)) \<le> b \<Longrightarrow> pos a \<le> pos b" by auto2

lemma operation_lessI [backward]:
  "p1 \<le> p2 \<Longrightarrow> INS p1 n1 i1 < DEL p2 n2 i2"
@proof
  @have "is_INS (INS p1 n1 i1) = True"
  @have "is_INS (DEL p2 n2 i2) = False"
@qed

setup {* fold del_prfstep_thm [@{thm less_eq}, @{thm less}] *}

section {* Set of operations corresponding to a list of rectangles *}

fun ins_op :: "'a rectangle list \<Rightarrow> nat \<Rightarrow> ('a::linorder) operation" where
  "ins_op rects i = INS (low (yint (rects ! i))) i (xint (rects ! i))"
setup {* add_rewrite_rule @{thm ins_op.simps} *}

fun del_op :: "'a rectangle list \<Rightarrow> nat \<Rightarrow> ('a::linorder) operation" where
  "del_op rects i = DEL (high (yint (rects ! i))) i (xint (rects ! i))"
setup {* add_rewrite_rule @{thm del_op.simps} *}

definition ins_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "ins_ops rects = list (\<lambda>i. ins_op rects i) (length rects)"

definition del_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "del_ops rects = list (\<lambda>i. del_op rects i) (length rects)"

lemma ins_ops_distinct [forward]: "distinct (ins_ops rects)"
@proof
  @let "xs = ins_ops rects"
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

lemma del_ops_distinct [forward]: "distinct (del_ops rects)"
@proof
  @let "xs = del_ops rects"
  @have "\<forall>i<length xs. \<forall>j<length xs. i \<noteq> j \<longrightarrow> xs ! i \<noteq> xs ! j"
@qed

lemma set_ins_ops [rewrite]:
  "oper \<in> set (ins_ops rects) \<longleftrightarrow> idx oper < length rects \<and> oper = ins_op rects (idx oper)"
@proof
  @case "oper \<in> set (ins_ops rects)" @with
    @obtain i where "i < length rects" "ins_ops rects ! i = oper" @end
  @case "idx oper < length rects \<and> oper = ins_op rects (idx oper)" @with
    @have "oper = (ins_ops rects) ! (idx oper)" @end
@qed

lemma set_del_ops [rewrite]:
  "oper \<in> set (del_ops rects) \<longleftrightarrow> idx oper < length rects \<and> oper = del_op rects (idx oper)"
@proof
  @case "oper \<in> set (del_ops rects)" @with
    @obtain i where "i < length rects" "del_ops rects ! i = oper" @end
  @case "idx oper < length rects \<and> oper = del_op rects (idx oper)" @with
    @have "oper = (del_ops rects) ! (idx oper)" @end
@qed

definition all_ops :: "'a rectangle list \<Rightarrow> ('a::linorder) operation list" where [rewrite]:
  "all_ops rects = sort (ins_ops rects @ del_ops rects)"

lemma all_ops_distinct [forward]: "distinct (all_ops rects)"
@proof @have "distinct (ins_ops rects @ del_ops rects)" @qed

lemma set_all_ops_idx [forward]:
  "oper \<in> set (all_ops rects) \<Longrightarrow> idx oper < length rects" by auto2

lemma set_all_ops_ins [forward]:
  "INS p n i \<in> set (all_ops rects) \<Longrightarrow> INS p n i = ins_op rects n" by auto2

lemma set_all_ops_del [forward]:
  "DEL p n i \<in> set (all_ops rects) \<Longrightarrow> DEL p n i = del_op rects n" by auto2

lemma ins_in_set_all_ops:
  "i < length rects \<Longrightarrow> ins_op rects i \<in> set (all_ops rects)" by auto2
setup {* add_forward_prfstep_cond @{thm ins_in_set_all_ops} [with_term "ins_op ?rects ?i"] *}

lemma del_in_set_all_ops:
  "i < length rects \<Longrightarrow> del_op rects i \<in> set (all_ops rects)" by auto2
setup {* add_forward_prfstep_cond @{thm del_in_set_all_ops} [with_term "del_op ?rects ?i"] *}

lemma all_ops_sorted [forward]: "sorted (all_ops rects)" by auto2
setup {* del_prfstep_thm @{thm all_ops_def} *}

section {* Applying a set of operations *}

definition apply_ops_k :: "('a::linorder) rectangle list \<Rightarrow> nat \<Rightarrow> nat set" where [rewrite]:
  "apply_ops_k rects k = (let ops = all_ops rects in
     {i. i < length rects \<and> (\<exists>j<k. ins_op rects i = ops ! j) \<and> \<not>(\<exists>j<k. del_op rects i = ops ! j)})"
setup {* register_wellform_data ("apply_ops_k rects k", ["k < length (all_ops rects)"]) *}

lemma apply_ops_set_mem [rewrite]:
  "ops = all_ops rects \<Longrightarrow>
   i \<in> apply_ops_k rects k \<longleftrightarrow> (i < length rects \<and> (\<exists>j<k. ins_op rects i = ops ! j) \<and> \<not>(\<exists>j<k. del_op rects i = ops ! j))"
  by auto2
setup {* del_prfstep_thm @{thm apply_ops_k_def} *}

definition xints_of :: "'a rectangle list \<Rightarrow> nat set \<Rightarrow> ('a::linorder) interval set" where
  "xints_of rect is = (\<lambda>i. xint (rect ! i)) ` is"

lemma xints_of_mem [rewrite]:
  "it \<in> xints_of rect is \<longleftrightarrow> (\<exists>i\<in>is. xint (rect ! i) = it)" using xints_of_def by auto

definition has_overlap_at_k :: "('a::linorder) rectangle list \<Rightarrow> nat \<Rightarrow> bool" where [rewrite]:
  "has_overlap_at_k rects k \<longleftrightarrow> (
    let S = apply_ops_k rects k; ops = all_ops rects in
      is_INS (ops ! k) \<and> has_overlap (xints_of rects S) (int (ops ! k)))"
setup {* register_wellform_data ("has_overlap_at_k rects k", ["k < length (all_ops rects)"]) *}

lemma has_overlap_at_k_equiv [forward]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> k < length ops \<Longrightarrow>
   has_overlap_at_k rects k \<Longrightarrow> has_rect_overlap rects"
@proof
  @let "S = apply_ops_k rects k"
  @have "has_overlap (xints_of rects S) (int (ops ! k))"
  @obtain "xs \<in> xints_of rects S" where "is_overlap xs (int (ops ! k))"
  @obtain "i \<in> S" where "xint (rects ! i) = xs"
  @let "j = idx (ops ! k)"
  @have "ops ! k \<in> set ops"
  @have "ops ! k = ins_op rects j"
  @have "i \<noteq> j" @with @contradiction
    @obtain k' where "k' < k" "ops ! k' = ins_op rects i"
    @have "ops ! k = ops ! k'"
  @end
  @have "low (yint (rects ! i)) \<le> pos (ops ! k)" @with
    @obtain k' where "k' < k" "ops ! k' = ins_op rects i"
    @have "ops ! k' \<le> ops ! k"
  @end
  @have "high (yint (rects ! i)) \<ge> pos (ops ! k)" @with
    @obtain k' where "k' < length ops" "ops ! k' = del_op rects i"
    @have "ops ! k' \<ge> ops ! k"
  @end
  @have "is_rect_overlap (rects ! i) (rects ! j)"
@qed

lemma has_overlap_at_k_equiv2 [resolve]:
  "is_rect_list rects \<Longrightarrow> ops = all_ops rects \<Longrightarrow> has_rect_overlap rects \<Longrightarrow>
   \<exists>k<length ops. has_overlap_at_k rects k"
@proof
  @obtain i j where "i < length rects" "j < length rects" "i \<noteq> j"
                    "is_rect_overlap (rects ! i) (rects ! j)"
  @have "is_rect_overlap (rects ! j) (rects ! i)"
  @obtain i1 where "i1 < length ops" "ops ! i1 = ins_op rects i"
  @obtain j1 where "j1 < length ops" "ops ! j1 = ins_op rects j"
  @obtain i2 where "i2 < length ops" "ops ! i2 = del_op rects i"
  @obtain j2 where "j2 < length ops" "ops ! j2 = del_op rects j"
  @case "ins_op rects i < ins_op rects j" @with
    @have "i1 < j1"
    @have "j1 < i2" @with @have "ops ! j1 < ops ! i2" @end
    @have "has_overlap_at_k rects j1"
  @end
  @case "ins_op rects j < ins_op rects i" @with
    @have "j1 < i1"
    @have "i1 < j2" @with @have "ops ! i1 < ops ! j2" @end
    @have "has_overlap_at_k rects i1"
  @end
@qed

definition has_overlap_lst :: "('a::linorder) rectangle list \<Rightarrow> bool" where [rewrite]:
  "has_overlap_lst rects = (let ops = all_ops rects in (\<exists>k<length ops. has_overlap_at_k rects k))"

lemma has_overlap_equiv [rewrite]:
  "is_rect_list rects \<Longrightarrow> has_overlap_lst rects \<longleftrightarrow> has_rect_overlap rects" by auto2

end
