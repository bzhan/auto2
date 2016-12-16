theory Feval
imports "~~/src/HOL/Library/FuncSet" "../Auto2"
begin

definition feval :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" ("_\<langle>_\<rangle>" [90]) where
  "feval f a = f a"
declare feval_def [simp]

theorem feval_def' [rewrite]: "feval (\<lambda>x. f x) x = f x" by simp

theorem compose_eq' [rewrite]: "x \<in> A \<Longrightarrow> (compose A g f)\<langle>x\<rangle> = g\<langle>f\<langle>x\<rangle>\<rangle>" by (simp add: compose_eq)

theorem inv_into_feval: "f\<langle>x\<rangle> = y \<Longrightarrow> inj_on f A \<Longrightarrow> x \<in> A \<Longrightarrow> (inv_into A f)\<langle>y\<rangle> = x" by (simp add: inv_into_f_eq)
setup {* add_forward_prfstep_cond @{thm inv_into_feval} [with_term "(inv_into ?A ?f)\<langle>?y\<rangle>"] *}

theorem inv_into_mem: "f ` A = B \<Longrightarrow> x \<in> B \<Longrightarrow> (inv_into A f)\<langle>x\<rangle> \<in> A"
  by (simp add: inv_into_into)
setup {* add_forward_prfstep_cond @{thm inv_into_mem} [with_term "(inv_into ?A ?f)\<langle>?x\<rangle>"] *}

(* Set image *)
theorem set_image_memE [forward]: "x \<in> h ` A \<Longrightarrow> \<exists>y\<in>A. h\<langle>y\<rangle> = x" by auto
theorem set_image_memI [backward1]: "y \<in> A \<Longrightarrow> h\<langle>y\<rangle> = x \<Longrightarrow> x \<in> h ` A" by auto

(* the_elem *)
theorem the_elem_image_unique' [backward]: "A \<noteq> {} \<Longrightarrow> \<forall>y\<in>A. f\<langle>y\<rangle> = f\<langle>x\<rangle> \<Longrightarrow> the_elem (f ` A) = f\<langle>x\<rangle>"
  by (simp add: the_elem_image_unique)

end
