theory DynamicArray
imports SepAuto "../DataStrs/Arrays_Ex"
begin

datatype 'a dynamic_array = Dyn_Array (alen: nat) (amax: nat) (aref: "'a array")
setup {* add_rewrite_rule_back @{thm dynamic_array.collapse} *}
setup {* add_rewrite_rule @{thm dynamic_array.case} *}
setup {* fold add_rewrite_rule @{thms dynamic_array.sel} *}

fun dyn_array :: "'a::heap list \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where
  "dyn_array xs (Dyn_Array al am a) =
     (\<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(xs = take al xs') * \<up>(al \<le> length xs') * \<up>(am = length xs'))"
setup {* add_rewrite_ent_rule @{thm dyn_array.simps} *}

definition dyn_array_new :: "'a::heap dynamic_array Heap" where [sep_proc]:
  "dyn_array_new = do {
     p \<leftarrow> Array.new 5 undefined;
     return (Dyn_Array 0 5 p)
   }"

lemma dyn_array_new_rule [hoare_triple]:
  "<emp> dyn_array_new <dyn_array []>" by auto2

fun array_copy :: "'a::heap array \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_copy a b 0 = (return ())"
| "array_copy a b (Suc n) = do {
      array_copy a b n;
      x \<leftarrow> Array.nth a n;
      Array.upd n x b;
      return () }"
declare array_copy.simps [sep_proc]

lemma array_copy_rule [hoare_triple]:
  "n \<le> length as \<Longrightarrow> n \<le> length bs \<Longrightarrow>
   <a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a bs>
    array_copy a b n
   <\<lambda>_. a \<mapsto>\<^sub>a as * b \<mapsto>\<^sub>a Arrays_Ex.array_copy as bs n>"
@proof @induct n @qed

definition ensure_length :: "'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where [sep_proc]:
  "ensure_length d = (case d of Dyn_Array al am ar \<Rightarrow>
    if al < am then return d
    else do {
      p \<leftarrow> Array.new (2 * am + 1) undefined;
      array_copy ar p am;
      return (Dyn_Array am (2 * am + 1) p)
    })"

lemma ensure_length_rule [hoare_triple]:
  "<dyn_array xs p>
   ensure_length p
   <\<lambda>r. dyn_array xs r * \<up>(alen r < amax r)>\<^sub>t" by auto2

definition push_array :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where [sep_proc]:
  "push_array x d = do {
    p \<leftarrow> ensure_length d;
    Array.upd (alen d) x (aref p);
    return (Dyn_Array (alen p + 1) (amax p) (aref p))
   }"

lemma push_array_rule [hoare_triple]:
  "<dyn_array xs p>
   push_array x p
   <dyn_array (xs @ [x])>\<^sub>t"
@proof @have "length (xs @ [x]) = length xs + 1" @qed

definition pop_array :: "'a::heap dynamic_array \<Rightarrow> ('a \<times> 'a dynamic_array) Heap" where [sep_proc]:
  "pop_array d = do {
    x \<leftarrow> Array.nth (aref d) (alen d - 1);
    return (x, Dyn_Array (alen d - 1) (amax d) (aref d))
   }"

lemma pop_array_heap_preserving [heap_presv]:
  "heap_preserving (pop_array d)" by auto2

lemma pop_array_rule [hoare_triple]:
  "xs \<noteq> [] \<Longrightarrow>
   <dyn_array xs p>
   pop_array p
   <\<lambda>(x, r). dyn_array (butlast xs) r * \<up>(x = last xs)>"
@proof @have "last xs = xs ! (length xs - 1)" @qed

definition array_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> unit Heap" where [sep_proc]:
  "array_upd i x d = do { Array.upd i x (aref d); return () }"

lemma array_upd_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p>
   array_upd i x p
   <\<lambda>_. dyn_array (list_update xs i x) p>" by auto2

definition array_nth :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> 'a Heap" where [sep_proc]:
  "array_nth d i = Array.nth (aref d) i"

lemma array_nth_heap_preserving [heap_presv]:
  "heap_preserving (array_nth d i)" by auto2

lemma array_nth_rule [hoare_triple]:
  "i < length xs \<Longrightarrow>
   <dyn_array xs p>
   array_nth p i
   <\<lambda>r. dyn_array xs p * \<up>(r = xs ! i)>" by auto2

definition array_length :: "'a dynamic_array \<Rightarrow> nat Heap" where [sep_proc]:
  "array_length d = return (alen d)"

lemma array_length_heap_preserving [heap_presv]:
  "heap_preserving (array_length d)" by auto2

lemma array_length_rule [hoare_triple]:
  "<dyn_array xs p>
   array_length p
   <\<lambda>r. dyn_array xs p * \<up>(r = length xs)>" by auto2

setup {* del_prfstep_thm @{thm dynamic_array.collapse} *}
setup {* fold del_prfstep_thm @{thms dyn_array.simps} *}

definition array_swap :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where [sep_proc]:
  "array_swap d i j = do {
    x \<leftarrow> array_nth d i;
    y \<leftarrow> array_nth d j;
    array_upd i y d;
    array_upd j x d;
    return ()
   }"

lemma array_swap_rule [hoare_triple]:
  "i < length xs \<Longrightarrow> j < length xs \<Longrightarrow>
   <dyn_array xs p>
   array_swap p i j
   <\<lambda>_. dyn_array (list_swap xs i j) p>" by auto2

end
