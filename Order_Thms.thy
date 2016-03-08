(* Setup for proof steps related to ordering. *)

theory Order_Thms
imports Auto2_Base
begin

section {* Results in class order or preorder *}

setup {* add_forward_prfstep_cond @{thm Orderings.order_class.order.trans} [with_filt (not_type_filter "a" natT)] *}
setup {* add_forward_prfstep_cond @{thm Orderings.order_class.order.strict_trans} [with_filt (not_type_filter "a" natT)] *}
setup {* add_forward_prfstep_cond @{thm Orderings.order_le_less_trans} [with_filt (not_type_filter "x" natT)] *}
setup {* add_forward_prfstep_cond @{thm Orderings.order_less_le_trans} [with_filt (not_type_filter "x" natT)] *}
setup {* add_resolve_prfstep @{thm Orderings.order_class.order.irrefl} *}
setup {* add_forward_prfstep_cond @{thm Orderings.le_neq_trans} [with_cond "?a \<noteq> ?b"] *}
setup {* add_forward_prfstep_cond @{thm Orderings.order_antisym} [with_filt (order_filter "x" "y"), with_cond "?x \<noteq> ?y"] *}

section {* Rewriting of negation, in linorder *}

setup {* fold add_gen_prfstep [
  ("not_less",
   [WithItem (TY_PROP, @{term_pat "\<not> (?x::(?'a::linorder)) < ?y"}),
    GetFact (@{term_pat "?y \<le> (?x::(?'a::linorder))"}, (equiv_forward_th @{thm linorder_not_less}))]),
  ("not_le",
   [WithItem (TY_PROP, @{term_pat "\<not> (?x::(?'a::linorder)) \<le> ?y"}),
    GetFact (@{term_pat "?y < (?x::(?'a::linorder))"}, (equiv_forward_th @{thm linorder_not_le}))])]
*}
setup {* fold add_fixed_sc [("not_less", 1), ("not_le", 1)] *}

section {* Properties of max and min (in linorder) *}

setup {* add_rewrite_rule @{thm min.commute} *}
setup {* add_rewrite_rule @{thm min.idem} *}
setup {* add_resolve_prfstep @{thm min.cobounded1} *}
setup {* add_backward2_prfstep @{thm min.boundedI} *}
setup {* add_resolve_prfstep @{thm min.coboundedI1} *}
setup {* add_resolve_prfstep @{thm min.strict_coboundedI1} *}
setup {* add_backward2_prfstep @{thm min.mono} *}
theorem min_boundedE: "(a::('a::linorder)) \<le> min b c \<Longrightarrow> a \<le> b" by simp
setup {* add_forward_prfstep_cond @{thm min_boundedE} [with_cond "?a \<noteq> ?b"]*}

setup {* add_rewrite_rule @{thm max.commute} *}
setup {* add_rewrite_rule @{thm max.idem} *}
setup {* add_resolve_prfstep @{thm max.cobounded1} *}
setup {* add_backward2_prfstep @{thm max.boundedI} *}
setup {* add_resolve_prfstep @{thm max.coboundedI1} *}
setup {* add_resolve_prfstep @{thm max.strict_coboundedI1} *}
setup {* add_backward2_prfstep @{thm max.mono} *}
theorem max_boundedE: "(a::('a::linorder)) \<ge> max b c \<Longrightarrow> a \<ge> b" by simp
setup {* add_forward_prfstep_cond @{thm max_boundedE} [with_cond "?a \<noteq> ?b"] *}

subsection {* Existence of numbers satisfying inequalities *}

theorem exists_ge [resolve]: "\<exists>k. k \<ge> (i::('a::order))" by auto
setup {* fold add_resolve_prfstep [@{thm lt_ex}, @{thm gt_ex}] *}
setup {* add_backward_prfstep @{thm dense} *}

end
