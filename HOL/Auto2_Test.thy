(* Unit tests for auto2. *)

theory Auto2_Test
imports Auto2_Main
begin

ML_file "util_test.ML"
ML_file "subterms_test.ML"
ML_file "rewrite_test.ML"
ML_file "matcher_test.ML"
ML_file "normalize_test.ML"
ML_file "logic_steps_test.ML"

ML_file "acdata_test.ML"
ML_file "order_test.ML"

ML_file "nat_order.ML"
ML_file "nat_order_test.ML"

setup {* register_wellform_data ("(a::nat) - b", ["a \<ge> b"]) *}

(* Normalize any expression to "a - b" form. *)
lemma nat_sub_norm:
  "(a::nat) = a - 0 \<and> a \<ge> 0" by simp

(* Adding and subtracting two normalized expressions. *)
lemma nat_sub1:
  "(a::nat) \<ge> b \<Longrightarrow> c \<ge> d \<Longrightarrow> (a - b) + (c - d) = (a + c) - (b + d) \<and> a + c \<ge> b + d" by simp

lemma nat_sub2:
  "(a::nat) \<ge> b \<Longrightarrow> c \<ge> d \<Longrightarrow> a - b \<ge> c - d \<Longrightarrow> (a - b) - (c - d) = (a + d) - (b + c) \<and> a + d \<ge> b + c" by simp

(* Cancel identical terms on two sides, yielding a normalized expression. *)
lemma nat_sub3:
  "(a::nat) + b \<ge> c + b \<Longrightarrow> (a + b) - (c + b) = a - c \<and> a \<ge> c" by simp

(* Cancel constants on two sides, yielding a normalized expression. *)
lemma nat_sub4:
  "n \<ge> m \<Longrightarrow> (a::nat) + n \<ge> c + m \<Longrightarrow> (a + n) - (c + m) = (a + (n - m)) - c \<and> a + (n - m) \<ge> c \<and> n \<ge> m" by arith

lemma nat_sub5:
  "n \<le> m \<Longrightarrow> (a::nat) + n \<ge> c + m \<Longrightarrow> (a + n) - (c + m) = a - (c + (m - n)) \<and> a \<ge> c + (m - n) \<and> m \<ge> n" by simp

ML_file "nat_sub.ML"
ML_file "nat_sub_test.ML"

end
