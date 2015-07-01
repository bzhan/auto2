(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  val var_count_filter: string -> int -> prfstep_filter
  val bdvar_split_filter: string -> string -> prfstep_filter
  val add_quantifier_proofsteps: theory -> theory
  val normalize_pred_comm: conv
  val imp_to_disj_cv: Proof.context -> conv
  val DISJ_MUT: string
  val DISJ_MUT_ACTIVE: string
  val disj_update: mut_update
  val disj_concl: bool -> mut_concl
  val disj_eq_better: mut_eq_better
  val add_disj_mut_proofsteps: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

(* Verify number of bound variables in s. *)
fun var_count_filter s n _ (_, inst) =
    let val var_s = Term.add_vars (lookup_inst inst s) []
    in length var_s = n end

(* In expressions of the form (EX/!) x y. (...), where ?s1 and ?s2
   appear inside, require that ?s1 depends only on x, and ?s2 depends
   only on y.
 *)
fun bdvar_split_filter s1 s2 _ (_, inst) =
    let
      val var_s1 = Term.add_vars (lookup_inst inst s1) []
      val var_s2 = Term.add_vars (lookup_inst inst s2) []
    in
      if length var_s1 <> 1 orelse length var_s2 <> 1 then false
      else let val ((_, i), _) = the_single var_s1
               val ((_, j), _) = the_single var_s2
           in i = 0 andalso j = 1 end
    end

fun resolve_impl items rtype st =
    let
      val ((item1 as {id = id1, ...}), item2) = the_pair items
      val (fact1, fact2) = (get_fact item1, get_fact item2)
    in
      if not (is_implies fact1) orelse has_vars fact2 then [] else
      let
        val A = fact1 |> Logic.dest_implies |> fst
        val insts = get_insts [A] [item2] rtype
        fun inst_to_updt ((id, _), ths) =
            Update.thm_update (Status.merge_boxes st (id, id1),
                               ths MRS (get_thm item1))
      in
        map inst_to_updt insts
      end
    end
val resolve_impl_filt = [fn _ => is_implies o get_fact,
                         fn _ => not o has_vars o get_fact]

fun resolve_eq items rtype (st as {ctxt, ...}) =
    let
      val ((item1 as {id = id1, ...}), item2) = the_pair items
      val (fact1, fact2) = (get_fact item1, get_fact item2)
    in
      if not (is_equals_term fact1) orelse has_vars fact2 then [] else
      let
        val tbl = RewriteTable.table_of_rewrite_type rtype
        val A = fact1 |> Logic.dest_equals |> fst
        val insts = get_insts [Logic.mk_term A] [item2] rtype
        val cv = Conv.rewr_conv (get_thm item1)
        fun inst_to_updt ((id, _), ths) =
            let
              val ct = ths |> the_single |> Thm.prop_of |> Logic.dest_term
                           |> cert ctxt
              val eq_th = (Conv.try_conv cv) ct
              val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
            in
              if lhs aconv rhs then
                raise AUTO2CT ("resolve_eq failed.", [ct])
              else if RewriteTable.is_equiv id tbl (lhs, rhs) then []
              else [Update.thm_update (Status.merge_boxes st (id, id1),
                                       eq_th |> to_obj_eq)]
            end
      in
        maps inst_to_updt insts
      end
    end
val resolve_eq_filt = [fn _ => is_equals_term o get_fact,
                       fn _ => not o has_vars o get_fact]

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context.
 *)
val exists_elim =
    prfstep_custom
        "exists_elim"
        [WithFact @{term_pat "EX x. ?A"}]
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val tbl = Status.get_rewrite_table st
              val patA = HOLogic.mk_Trueprop (lookup_inst inst "A")
              val var = Var (the_single (Term.add_vars patA []))
                        handle List.Empty =>
                               raise AUTO2 "exists without bound variable."
              val new_th = Thm.trivial (cert ctxt patA)
              val prev_th = the_single ths

              (* Whether patA is the body of a trivial exists statement. *)
              val detect_trivial =
                  case HOLogic.dest_Trueprop patA of
                      Const ("HOL.eq", _) $ A $ B =>
                      if has_vars A andalso has_vars B then false else
                      let
                        val (pat, trm) = if has_vars A then (A, B) else (B, A)
                        val insts = (fo_table_match id tbl (pat, trm))
                                        |> filter (fn ((id', _), _) => id = id')
                      in
                        length insts <> 0
                      end
                    | _ => false

              fun extract_freevar t =
                  let
                    val ((nm, i), _) = dest_Var var
                    val inst = pattern_fo_match ctxt (patA, t)
                  in
                    lookup_instn inst (nm, i)
                  end

              fun ready (t, ts) =
                  forall (fn t' => t' aconv t orelse
                                   not (occurs_free (extract_freevar t) t')) ts

              fun handler (t, th) =
                  th |> Thm.implies_intr (cert ctxt t)
                     |> ex_elim ctxt (extract_freevar t)
                     |> Thm.elim_implies prev_th
            in
              if detect_trivial then [] else
              [Update.AddItems {
                  id = id, raw_items = [FreeVar var, Fact new_th,
                                        Handler (patA, (ready, handler))]}]
            end)

(* Normalize order of existence and forall statements. *)
fun normalize_pred_comm ct =
    let
      val cv = Conv.try_conv (
            Conv.first_conv (map rewr_obj_eq [@{thm ex_comm}, @{thm all_comm}]))
      val th = cv ct
    in
      if Term_Ord.termless (Thm.prop_of th |> Logic.dest_equals) then th
      else Conv.all_conv ct
    end

val add_quantifier_proofsteps =
    fold add_prfstep_thm [
      ("exists_intro",
       [WithGoal @{term_pat "EX x. ?P & ?Q"},
        Filter (ac_atomic_filter @{const_name conj} "P"),
        Filter (subset_var_filter "Q" "P")],
       @{thm exists_intro}),

      ("exists_intro2",
       [WithGoal @{term_pat "EX x y. ?P & ?Q"},
        Filter (ac_atomic_filter @{const_name conj} "P"),
        Filter (subset_var_filter "Q" "P")],
       @{thm exists_intro2}),

      ("exists_resolve",
       [WithGoal @{term_pat "EX x. ?P"},
        Filter (var_count_filter "P" 1)],
       @{thm exists_resolve}),

      ("forall_resolve0",
       [WithFact @{term_pat "! x. ?P"},
        Filter (fn _ => fn (_, inst) => not (is_neg (lookup_inst inst "P"))),
        Filter (var_count_filter "P" 1)],
       @{thm forall_resolve0}),

      ("forall_resolve0'",
       [WithFact @{term_pat "! x. ~ ?P"},
        Filter (var_count_filter "P" 1)],
       @{thm forall_resolve0'}),

      ("forall_resolve",
       [WithFact @{term_pat "! x. ?P --> ?Q"},
        Filter (subset_var_filter "Q" "P")],
       @{thm forall_resolve}),

      ("forall_resolve_opp",
       [WithFact @{term_pat "! x. ?P --> (~ ?Q)"},
        Filter (subset_var_filter "P" "Q")],
       @{thm forall_resolve_opp}),

      ("forall_resolve2",
       [WithFact @{term_pat "! x y. ?P --> ?Q"},
        Filter (subset_var_filter "Q" "P")],
       @{thm forall_resolve2}),

      (* Result is used for rewriting P -> Q. *)
      ("forall_eq",
       [WithFact @{term_pat "! x. ?P = ?Q"},
        Filter (subset_var_filter "Q" "P")],
       @{thm forall_eq}),

      (* Result is used for rewriting Q -> P. *)
      ("forall_eq'",
       [WithFact @{term_pat "! x. ?P = ?Q"},
        Filter (subset_var_filter "P" "Q")],
       @{thm forall_eq'}),

      (* Result is used for rewriting P -> Q. *)
      ("forall_eq2",
       [WithFact @{term_pat "! x y. ?P = ?Q"},
        Filter (subset_var_filter "Q" "P")],
       @{thm forall_eq2}),

      (* Result is used for rewriting Q -> P. *)
      ("forall_eq2'",
       [WithFact @{term_pat "! x y. ?P = ?Q"},
        Filter (subset_var_filter "P" "Q")],
       @{thm forall_eq2'})

    ] #> fold add_prfstep_conv [
      ("exists_split",
       [WithTerm @{term_pat "EX x y. ?P & ?Q"},
        Filter (bdvar_split_filter "P" "Q")],
       (rewr_obj_eq @{thm exists_split})),

      ("forall_split1",
       [WithTerm @{term_pat "! x y. ?P & ?Q --> ?R"},
        Filter (bdvar_split_filter "P" "Q")],
       (rewr_obj_eq @{thm forall_split1})),

      ("forall_split2",
       [WithTerm @{term_pat "! x y. ?P & ?Q --> ?R"},
        Filter (bdvar_split_filter "P" "Q")],
       (rewr_obj_eq @{thm forall_split2})),

      ("forall_or",
       [WithTerm @{term_pat "! x. (?A | ?B) --> ?C"}],
       (rewr_obj_eq @{thm forall_or})),

      ("rewrite_not_forall",
       [WithTerm @{term_pat "~ (! x. ?A)"}],
       (rewr_obj_eq @{thm HOL.not_all}))

    ] #> fold add_prfstep [
      {name = "resolve_impl", filt = resolve_impl_filt, func = resolve_impl},
      {name = "resolve_eq", filt = resolve_eq_filt, func = resolve_eq},
      exists_elim

    ] #> fold add_eq_th_normalizer [
      @{thm exists_split}, @{thm exists_split'}

    ] #> add_conv_normalizer ("normalize_pred", normalize_pred_comm)

(* Disjunctive mutable states. *)
val disj_ac = the (lookup_ac_data @{theory} @{const_name disj})
val dest_disj_prop = ACUtil.dest_ac disj_ac o prop_of'
val DISJ_MUT = "DISJ_MUT"
val DISJ_MUT_ACTIVE = "DISJ_MUT_ACTIVE"

val disj_state_intro =
    prfstep_custom
        "disj_state_intro"
        [WithFact @{term_pat "?A | ?B"},
         Filter (canonical_split_filter @{const_name disj} "A" "B")]
        (fn ((id, _), ths) => fn _ =>
            [Update.AddMutState {id = id, mut_type = DISJ_MUT_ACTIVE,
                                 sval = the_single ths}])

(* Convert term of form A_1 --> ... --> A_n to ~A_1 | ... | ~A_(n-1) |
   A_n. Note each A_i remains the same.
 *)
fun imp_conv_disj_cv ct =
    case Thm.term_of ct of
        Const ("HOL.implies", _) $ _ $ _ =>
        (rewr_obj_eq @{thm imp_conv_disj}
                          then_conv (Conv.arg_conv imp_conv_disj_cv)) ct
      | _ => Conv.all_conv ct

(* Convert proposition of form A_1 --> ... --> A_n to ~A_1 | ... |
   ~A_(n-1) | A_n. Expand any ~A_i of form ~(A_i1 & ... & A_in) using
   de Morgan's law.
 *)
fun imp_to_disj_cv ctxt =
    let
      val cv_imp = Conv.arg_conv imp_conv_disj_cv
      val cv_deMorgan = rewr_obj_eq_top @{thm de_Morgan_conj} ctxt
      val cv_nn = rewr_obj_eq_top nn_cancel_th ctxt
      val cv_assoc = Conv.arg_conv (ACUtil.rearrange_assoc disj_ac)
    in
      cv_imp then_conv cv_deMorgan then_conv cv_nn then_conv cv_assoc
    end

val conj_goal_intro =
    prfstep_custom
        "conj_goal_intro"
        [WithGoal @{term_pat "?A & ?B"},
         Filter (canonical_split_filter @{const_name conj} "A" "B")]
        (fn ((id, _), ths) => fn {ctxt, ...} =>
            let
              (* Only using the cv_deMorgan and cv_nn parts. *)
              val disj_th = apply_to_thm (imp_to_disj_cv ctxt) (the_single ths)
            in
              [Update.AddMutState {id = id, mut_type = DISJ_MUT_ACTIVE,
                                   sval = disj_th}]
            end)

val imp_disj_state_intro =
    prfstep_custom
        "imp_disj_state_intro"
        [WithFact @{term_pat "?A --> ?B"}]
        (fn ((id, _), ths) => fn {ctxt, ...} =>
            let
              val disj_th = apply_to_thm (imp_to_disj_cv ctxt) (the_single ths)
            in
              [Update.AddMutState {id = id, mut_type = DISJ_MUT,
                                   sval = disj_th}]
            end)

(* sval is of form A_1 | ... | A_n. Look for equivalences between item
   and ~A_i.
 *)
fun disj_update (id, sval) rtype item (st as {ctxt, ...}) =
    if length (dest_disj_prop sval) = 1 then [] else
    let
      val thy = Status.theory_of st
      val tbl = RewriteTable.table_of_rewrite_type rtype

      (* Given a term t (part of ts), find equivalences between ~t and
         the given item. Write resulting theorems in t = False form.
       *)
      fun get_rewrs t =
          let
            val negt = t |> HOLogic.mk_Trueprop |> get_neg'
            val insts = get_insts [negt] [item] rtype
            fun process_inst ((id', _), ths) =
                let
                  val negt_th = the_single ths
                  val eq_False_th = if is_neg t then @{thm eq_False'}
                                    else @{thm eq_False}
                  val eq_False_cv =
                      Conv.arg_conv (rewr_obj_eq (obj_sym eq_False_th))
                  val teqF = (apply_to_thm eq_False_cv negt_th) |> to_meta_eq
                in
                  (Status.merge_boxes st (id, id'), teqF)
                end
            val all_rewrs = map process_inst insts
          in
            if exists (fn (id', _) => id' = id) all_rewrs then all_rewrs
            else (id, Thm.reflexive (cert ctxt t)) :: all_rewrs
          end

      val (sval', subs) = Subterms.dest_subterms thy (prop_of' sval)
      val ac_len = length subs
    in
      (map get_rewrs subs)
          |> RewriteTable.merge_simp_infos tbl
          |> map (fn (id, equivs) =>
                     (id, Subterms.build_equiv ctxt equivs sval'))
          |> map (apsnd (apply_to_rhs (ACUtil.rearrange_subterms disj_ac)))
          |> RewriteTable.reduce_simp_info tbl
          |> map (fn (id, eq_th) =>
                     (id, Thm.equal_elim (make_trueprop_eq eq_th) sval))
          |> filter (fn (_, th') => length (dest_disj_prop th') < ac_len)
    end

fun disj_concl is_active (id, sval) _ =
    let
      val ts = dest_disj_prop sval
      val single_updt =
          if length ts = 1 then [Update.thm_update (id, sval)] else []
      val case_updt =
          if not is_active then []
          else if length ts = 1 then []
          else [Update.AddBoxes {
                   id = id, freevars = [],
                   assums = [HOLogic.mk_Trueprop (hd ts)],
                   concls = [], cb = Update.null_callback}]
    in
      single_updt @ case_updt
    end

(* sval1 dominates sval2 if the disjunctive terms in sval1 is a subset
   of that for sval2.
 *)
fun disj_eq_better sval1 sval2 =
    let
      val ts1 = prop_of' sval1 |> ACUtil.dest_ac disj_ac
      val ts2 = prop_of' sval2 |> ACUtil.dest_ac disj_ac
    in
      subset (op aconv) (ts1, ts2)
    end

fun add_disj_mut_proofsteps thy =
    thy |> add_prfstep imp_disj_state_intro
        |> add_mut_update (DISJ_MUT, disj_update)
        |> add_mut_concl (DISJ_MUT, disj_concl false)
        |> add_mut_eq_better (DISJ_MUT, disj_eq_better)
        |> add_prfstep disj_state_intro
        |> add_prfstep conj_goal_intro
        |> add_mut_update (DISJ_MUT_ACTIVE, disj_update)
        |> add_mut_concl (DISJ_MUT_ACTIVE, disj_concl true)
        |> add_mut_eq_better (DISJ_MUT_ACTIVE, disj_eq_better)

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_quantifier_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_mut_proofsteps
