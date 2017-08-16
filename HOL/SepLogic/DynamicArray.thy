theory DynamicArray
imports SepAuto More_Lists
begin

datatype 'a dynamic_array = Dyn_Array (alen: nat) (amax: nat) (defv: 'a) (aref: "'a array")
setup {* add_rewrite_rule_back @{thm dynamic_array.collapse} *}
setup {* add_rewrite_rule @{thm dynamic_array.case} *}
setup {* fold add_rewrite_rule @{thms dynamic_array.sel} *}

fun dyn_array :: "'a::heap list \<Rightarrow> 'a dynamic_array \<Rightarrow> assn" where
  "dyn_array xs (Dyn_Array al am dv a) =
     (\<exists>\<^sub>Axs'. a \<mapsto>\<^sub>a xs' * \<up>(xs = take al xs') * \<up>(al \<le> length xs') * \<up>(am = length xs'))"
setup {* add_rewrite_ent_rule @{thm dyn_array.simps} *}

theorem dyn_array_length [forward_ent]:
  "dyn_array xs (Dyn_Array al am dv a) \<Longrightarrow>\<^sub>A true * \<up>(al = length xs)" by auto2

theorem dyn_array_prec [sep_prec_thms]:
  "h \<Turnstile> dyn_array xs p * F1 \<Longrightarrow> h \<Turnstile> dyn_array ys p * F2 \<Longrightarrow> xs = ys" by auto2

definition dyn_array_new :: "'a \<Rightarrow> 'a::heap dynamic_array Heap" where
  "dyn_array_new x = do {
    p \<leftarrow> Array.new 5 x;
    return (Dyn_Array 0 5 x p)
   }"
declare dyn_array_new_def [sep_proc_defs]

theorem dyn_array_new_rule [hoare_triple]:
  "<emp> dyn_array_new x <dyn_array []>" by auto2

fun array_copy :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_copy src si dst di n =
   (if n = 0 then return ()
    else do {
      x \<leftarrow> Array.nth src si;
      Array.upd di x dst;
      array_copy src (si+1) dst (di+1) (n-1)
     })"
declare array_copy.simps [sep_proc_defs]

theorem array_copy_rule [hoare_triple, hoare_create_case]:
  "<src \<mapsto>\<^sub>a lsrc * dst \<mapsto>\<^sub>a ldst * \<up>(si + len \<le> length lsrc) * \<up>(di + len \<le> length ldst)>
    array_copy src si dst di len
   <\<lambda>_. src \<mapsto>\<^sub>a lsrc * dst \<mapsto>\<^sub>a list_update_range ldst di (take len (drop si lsrc))>"
@proof @var_induct len arbitrary si di ldst @qed

definition ensure_length :: "nat \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "ensure_length nl d = (case d of
    Dyn_Array al am dv a \<Rightarrow>
      if nl > am then do {
        p \<leftarrow> Array.new (2 * nl) dv;
        array_copy a 0 p 0 al;
        return (Dyn_Array al (2 * nl) dv p)
      } else return d)"
declare ensure_length_def [sep_proc_defs]

theorem ensure_length_rule [hoare_triple]:
  "<dyn_array xs p> ensure_length nl p <\<lambda>r. dyn_array xs r * \<up>(amax r \<ge> nl)>\<^sub>t" by auto2

definition push_array :: "'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> 'a dynamic_array Heap" where
  "push_array x d = (case d of
    Dyn_Array al am dv a \<Rightarrow> do {
      p \<leftarrow> ensure_length (al + 1) d;
      Array.upd al x (aref p);
      return (Dyn_Array (alen p + 1) (amax p) (defv p) (aref p)) })"
declare push_array_def [sep_proc_defs]

theorem push_array_rule [hoare_triple]:
  "<dyn_array xs p> push_array x p <\<lambda>r. dyn_array (xs @ [x]) r>\<^sub>t" by auto2

definition pop_array :: "'a::heap dynamic_array \<Rightarrow> ('a \<times> 'a dynamic_array) Heap" where
  "pop_array d = (case d of
    Dyn_Array al am dv a \<Rightarrow> do {
      x \<leftarrow> Array.nth a (al - 1);
      return (x, Dyn_Array (al - 1) am dv a)
    })"
declare pop_array_def [sep_proc_defs]

theorem pop_array_rule [hoare_triple]:
  "<dyn_array xs p * \<up>(length xs > 0)>
   pop_array p
   <\<lambda>(x, r). dyn_array (butlast xs) r * \<up>(x = last xs)>" by auto2

theorem pop_array_heap_preserving [heap_presv_thms]:
  "heap_preserving (pop_array d)" by auto2

definition array_upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap dynamic_array \<Rightarrow> unit Heap" where
  "array_upd i x d = do { Array.upd i x (aref d); return () }"
declare array_upd_def [sep_proc_defs]

theorem array_upd_rule [hoare_triple, hoare_create_case]:
  "<dyn_array l p * \<up>(i < length l)>
   array_upd i x p
   <\<lambda>_. dyn_array (list_update l i x) p>" by auto2

definition array_nth :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  "array_nth d i = Array.nth (aref d) i"
declare array_nth_def [sep_proc_defs]

theorem array_nth_rule [hoare_triple, hoare_create_case]:
  "<dyn_array xs p * \<up>(i < length xs)>
   array_nth p i
   <\<lambda>r. dyn_array xs p * \<up>(r = xs ! i)>" by auto2

theorem array_nth_heap_preserving [heap_presv_thms]:
  "heap_preserving (array_nth d i)" by auto2

definition array_length :: "'a dynamic_array \<Rightarrow> nat Heap" where
  "array_length d = return (alen d)"
declare array_length_def [sep_proc_defs]

theorem array_length_rule [hoare_triple_direct]:
  "<dyn_array xs p>
   array_length p
   <\<lambda>r. dyn_array xs p * \<up>(r = length xs)>" by auto2

theorem array_length_heap_preserving [heap_presv_thms]:
  "heap_preserving (array_length d)" by auto2

definition array_swap :: "'a::heap dynamic_array \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> unit Heap" where
  "array_swap d i j = do {
    x \<leftarrow> array_nth d i;
    y \<leftarrow> array_nth d j;
    array_upd i y d;
    array_upd j x d;
    return ()
   }"
declare array_swap_def [sep_proc_defs]

theorem array_swap_rule [hoare_triple, hoare_create_case]:
  "<dyn_array xs p * \<up>(i < length xs) * \<up>(j < length xs)>
   array_swap p i j
   <\<lambda>_. dyn_array (list_swap xs i j) p>" by auto2

setup {* del_prfstep_thm @{thm dynamic_array.collapse} *}
declare array_upd_def [sep_proc_defs del]

end
