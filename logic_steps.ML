(* Core (logic) proofsteps. *)

signature LOGIC_PROOFSTEPS =
sig
  (* General logic *)
  val shadow_prop_item: proofstep
  val shadow_term_item: proofstep
  val eq_elim_prfstep: proofstep
  val cong_on_ineq_prfstep: proofstep

  val exists_elim_prfstep: proofstep
  val add_logic_proofsteps: theory -> theory

  val mk_all_disj: term list * term list -> term
  val strip_all_disj: term -> term list * term list
  val norm_all_disj: Proof.context -> conv
  val disj_prop_match:
      Proof.context -> id_inst -> term * ((indexname * typ) list * cterm list) ->
      id_inst_th list
  val norm_conj: conv

  (* DISJ items. *)
  val TY_DISJ: string
  val disj_to_ritems: bool -> term -> thm -> raw_item list
  val disj_to_update: bool -> term -> box_id * int option * thm -> raw_update
  val dest_tname_of_disj: cterm list -> term * cterm list
  val is_match_prem_only: box_item -> bool
  val forall_elim_sch: thm -> thm
  val analyze_disj_th: Proof.context -> thm -> term * thm
  val disj_rewr_terms: term list -> term list
  val output_disj_fn: item_output
  val disj_prop_matcher: item_matcher

  val reduce_disj_True: conv
  val match_update_prfstep: proofstep
  val match_one_sch_prfstep: proofstep
  val disj_match_iff_prfstep: proofstep
  val disj_create_case_prfstep: proofstep
  val disj_shadow_prfstep: proofstep
  val add_disj_proofsteps: theory -> theory

  (* Normalizers *)
  val split_conj_gen_th: Proof.context -> thm -> thm list
  val eq_normalizer: normalizer
  val property_normalizer: normalizer
  val disj_normalizer: normalizer
  val logic_thm_update: Proof.context -> box_id * thm -> raw_update
  val add_disj_normalizers: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

fun boolVar s = Var ((s, 0), boolT)

(* Shadowing based on equivalence. For both PROP and TERM items,
   shadowing is based on subterm equivalence, skipping any Not (~) at
   head.
 *)
fun shadow_item_fn ictxt item1 item2 =
    if #sc item1 = 0 andalso #sc item2 = 0 then []
    else let
      val ctxt = IncrContext.context_of ictxt
      val id = BoxItem.merged_id ctxt [item1, item2]
      val _ = assert (forall (BoxItem.match_ty_strs [TY_TERM, TY_PROP])
                             [item1, item2])
                     "shadow_item_fn"
      val (tname1, tname2) =
          (the_single (#tname item1), the_single (#tname item2))
          handle List.Empty => raise Fail "shadow_item_fn"
      val (t1, t2) = (Thm.term_of tname1, Thm.term_of tname2)

      val equiv_ids =
          if fastype_of t1 = boolT andalso is_neg t1 andalso
             fastype_of t2 = boolT andalso is_neg t2 then
            (RewriteTable.subequiv_info
                 ctxt id (UtilLogic.get_cneg tname1, UtilLogic.get_cneg tname2))
                |> IncrContext.replace_id_for_type' ictxt |> map fst
                |> Util.max_partial (BoxID.is_eq_ancestor ctxt)
          else
            (RewriteTable.subequiv_info ctxt id (tname1, tname2))
                |> IncrContext.replace_id_for_type' ictxt |> map fst
                |> Util.max_partial (BoxID.is_eq_ancestor ctxt)
      val item_to_shadow =
          if #sc item1 > #sc item2 orelse
             (#sc item1 = #sc item2 andalso #uid item1 > #uid item2) then item1
          else item2
      fun process_id id' =
          ShadowItem {id = id', item = item_to_shadow}
    in
      map process_id equiv_ids
    end

val shadow_prop_item =
    {name = "shadow_prop",
     args = [TypedMatch (TY_PROP, boolVar "A"),
             TypedMatch (TY_PROP, boolVar "B")],
     priority = PRIORITY_URGENT,
     func = TwoStep shadow_item_fn}

val shadow_term_item =
    {name = "shadow_term",
     args = [TypedMatch (TY_TERM, @{term_pat "?A::?'a"}),
             TypedMatch (TY_TERM, @{term_pat "?B::?'a"})],
     priority = PRIORITY_URGENT,
     func = TwoStep shadow_item_fn}

(* Given equality A = B between booleans and proposition A, B, ~A, ~B,
   derive the other side of the equality (or its negation) and shadow
   the equality.
 *)
fun eq_elim_fn ictxt (item1 as {id, prop, ...}) item2 =
    let
      val (A, B) = dest_eq (prop_of' prop)
      fun inst_t t = ItemIO.get_insts (PropMatch t) item2 ictxt (id, fo_init)
      val (inst_A, inst_B) = (inst_t A, inst_t B)
      val (inst_nA, inst_nB) = (inst_t (get_neg A), inst_t (get_neg B))

      (* All the process_inst functions follow the same pattern, up to
         transform function f for prop.
       *)
      fun elim_shadow f ((id', _), th) =
          let
            val th = Thm.equal_elim (make_trueprop_eq (f prop)) th
          in
            [AddItems {id = id', sc = SOME 1,
                       raw_items = [Update.thm_to_ritem th]},
             ShadowItem {id = id', item = item1}]
          end

      val process_inst_A = elim_shadow to_meta_eq
      val process_inst_B = elim_shadow (meta_sym o to_meta_eq)
      val process_inst_nA = elim_shadow (UtilLogic.make_neg_eq o to_meta_eq)
      val process_inst_nB = elim_shadow (UtilLogic.make_neg_eq o meta_sym o to_meta_eq)
    in
      maps process_inst_A inst_A @ maps process_inst_B inst_B @
      maps process_inst_nA inst_nA @ maps process_inst_nB inst_nB
    end

val eq_elim_prfstep =
    {name = "eq_elim",
     args = [TypedMatch (TY_EQ, mk_eq (boolVar "A", boolVar "B")),
             PropMatch (boolVar "C")],
     priority = PRIORITY_SHADOW,
     func = TwoStep eq_elim_fn}

(* Given goal A = B, find rewrites of A and B to terms of the form
   f(a_1, ..., a_n) and g(b_1, ..., b_n), where all but one of the
   pairs a_i and b_i are equal. Reduce the equality goal to the goal
   a_i = b_i for that i.
 *)
fun cong_on_ineq_fn ictxt {id, prop, ...} =
    let
      val (cA, cB) = prop |> cprop_of' |> UtilLogic.get_cneg
                          |> Util.dest_binop_cargs
      val (A, B) = apply2 Thm.term_of (cA, cB)
      val ctxt = IncrContext.context_of ictxt

      fun process_A_equiv (id', eq_A) =
          let
            val A' = Util.rhs_of eq_A
            val (f, argsA') = Term.strip_comb A'
            fun process_i i =
                let
                  val ty_i = fastype_of (nth argsA' i)
                  val args_pat = (take i argsA') @ [Var (("x",0), ty_i)] @
                                 (drop (i + 1) argsA')
                  val pat = Term.list_comb (f, args_pat)
                  val insts =
                      (Matcher.rewrite_match ctxt (pat, cB) (id', fo_init))
                          |> IncrContext.replace_id_for_type ictxt

                  fun process_inst ((id'', inst), eq_B) =
                      let
                        val tx = lookup_inst inst "x"
                        val cv = Conv.every_conv [
                              Conv.arg1_conv (Conv.rewr_conv (meta_sym eq_A)),
                              Conv.arg_conv (Conv.rewr_conv eq_B),
                              UtilBase.to_obj_eq_cv]
                        val cong_th =
                            (Util.eq_cong_th i tx A' ctxt)
                                |> apply_to_thm (Util.concl_conv cv)
                                |> apply_to_thm (Conv.arg1_conv UtilBase.to_obj_eq_cv)
                                |> apply_to_thm (Conv.rewr_conv UtilBase.backward_conv_th)
                      in
                        Update.thm_update (id'', prop RS cong_th)
                      end
                in
                  map process_inst insts
                end
          in
            (* Test only when f is a free variable (not a constant). *)
            if Term.is_Free f then
              maps process_i (0 upto (length argsA' - 1))
            else []
          end
    in
      (* Due to symmetry, only need to process one side. *)
      if Term_Ord.termless (A, B) then
        let
          val A_equivs = (RewriteTable.get_head_equiv ctxt cA)
                             |> maps snd
                             |> BoxID.merge_box_with_info ctxt id
        in
          maps process_A_equiv A_equivs
        end
      else []
    end

val cong_on_ineq_prfstep =
    {name = "cong_on_ineq",
     args = [TypedMatch (TY_PROP, @{term_pat "?A ~= ?B"})],
     priority = PRIORITY_ADD,
     func = OneStep cong_on_ineq_fn}

(* Given an assumption of the form EX x. A, we produce an assumption A
   with x in A replaced by a free variable. To avoid name collisions,
   when the update is produced x is replaced by an "internal" free
   variable, with suffix '_'. When the update is applied, that
   internal free variable is replaced by a fresh variable as
   determined by the context. We produce at most two variables at a
   time.
 *)
fun exists_elim_fn ictxt {id, prop, ...} =
    if not (IncrContext.is_single_ictxt ictxt) then []
    else let
      val t = prop_of' prop
      val ctxt = IncrContext.context_of ictxt
    in
      if is_ex t orelse is_bex t orelse
         (is_neg t andalso is_obj_all (dest_not t)) orelse
         (is_neg t andalso is_ball (dest_not t)) then
        let
          val th = prop |> apply_to_thm' (UtilLogic.normalize_exists ctxt)
          val (vars, _) = (UtilLogic.strip_exists (prop_of' th))
                              |> Util.replace_vars ctxt
                              |> Util.replace_internal_vars
          val xs = map (fst o Term.dest_Free) vars
        in
          Update.apply_exists ctxt xs (id, th)
        end
      else []
    end

val exists_elim_prfstep =
    {name = "exists_elim",
     args = [TypedMatch (TY_PROP, boolVar "A")],
     priority = PRIORITY_ADD,
     func = OneStep exists_elim_fn}

val add_logic_proofsteps =
    fold add_prfstep [
      shadow_prop_item, shadow_term_item, eq_elim_prfstep, cong_on_ineq_prfstep,
      exists_elim_prfstep
    ]

(* Given (x_1 ... x_n, A_1 ... A_n), create the corresponding
   forall-disj term.
 *)
fun mk_all_disj (vars, terms) =
    case vars of
        [] => list_disj terms
      | var :: vars' => mk_obj_all var (mk_all_disj (vars', terms))

(* Normalize t into a disjunction of terms. *)
fun strip_disj t =
    if is_disj t then
      maps strip_disj [dest_arg1 t, dest_arg t]
    else if is_imp t then
      maps strip_disj [get_neg (dest_arg1 t), dest_arg t]
    else if is_neg t then
      let
        val t' = dest_not t
      in
        if is_neg t' then strip_disj (dest_not t')
        else if is_conj t' then
          maps strip_disj [get_neg (dest_arg1 t'), get_neg (dest_arg t')]
        else [t]
      end
    else [t]

(* Normalize a term into the form !x_1 ... x_n. A_1 | ... | A_n *)
fun strip_all_disj t =
    if is_obj_all t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, disjs) = strip_all_disj body
          in
            if exists (Util.occurs_free var) disjs then (var :: vars, disjs)
            else (vars, disjs)
          end
        | f $ arg => strip_all_disj (f $ UtilLogic.force_abs_form arg)
        | _ => raise Fail "strip_all_disj"
    else if is_ball t then
      case t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, disjs) = strip_all_disj body
          in
            (var :: vars, get_neg mem :: disjs)
          end
        | f $ S $ arg => strip_all_disj (f $ S $ UtilLogic.force_abs_form arg)
        | _ => raise Fail "strip_all_disj"
    else if is_neg t andalso is_ex (dest_not t) then
      case dest_not t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, disjs) = strip_all_disj (get_neg body)
          in
            if exists (Util.occurs_free var) disjs then (var :: vars, disjs)
            else (vars, disjs)
          end
        | f $ arg => strip_all_disj (get_neg (f $ UtilLogic.force_abs_form arg))
        | _ => raise Fail "strip_all_disj"
    else if is_neg t andalso is_bex (dest_not t) then
      case dest_not t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, disjs) = strip_all_disj (get_neg body)
          in
            (var :: vars, get_neg mem :: disjs)
          end
        | f $ S $ arg => strip_all_disj (get_neg (f $ S $ UtilLogic.force_abs_form arg))
        | _ => raise Fail "strip_all_disj"
    else if is_disj t then
      let
        val (v1, ts1) = strip_all_disj (dest_arg1 t)
        val (v2, ts2) = strip_all_disj (dest_arg t)
      in
        (v1 @ v2, ts1 @ ts2)
      end
    else if is_imp t then
      let
        val (v1, ts1) = strip_all_disj (get_neg (dest_arg1 t))
        val (v2, ts2) = strip_all_disj (dest_arg t)
      in
        (v1 @ v2, ts1 @ ts2)
      end
    else if is_neg t then
      let
        val t' = dest_not t
      in
        if is_neg t' then strip_all_disj (dest_not t')
        else if is_conj t' then
          let
            val (v1, ts1) = strip_all_disj (get_neg (dest_arg1 t'))
            val (v2, ts2) = strip_all_disj (get_neg (dest_arg t'))
          in
            (v1 @ v2, ts1 @ ts2)
          end
        else ([], [t])
      end
    else ([], [t])

(* Normalize (A_1 | A_2 | ... | A_m) | (B_1 | B_2 | ... | B_n) *)
fun norm_disj_clauses ct =
    let
      val (arg1, _) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_disj arg1 then
        Conv.every_conv [rewr_obj_eq UtilBase.disj_assoc_th,
                         Conv.arg_conv norm_disj_clauses] ct
      else
        Conv.all_conv ct
    end

(* Normalize ct. *)
fun norm_disj ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "norm_disj: wrong type"
    in
      if is_disj t then
        Conv.every_conv [Conv.binop_conv norm_disj, norm_disj_clauses] ct
      else if is_imp t then
        Conv.every_conv [rewr_obj_eq UtilBase.imp_conv_disj_th, norm_disj] ct
      else if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th, norm_disj] ct
      else if is_neg t andalso is_conj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_conj_th, norm_disj] ct
      else
        Conv.all_conv ct
    end

(* Normalize to forall at the top-level *)
fun norm_all_disj ctxt ct =
    let
      val t = Thm.term_of ct
    in
      if is_obj_all t then
        if not (Util.is_subterm (Bound 0) (dest_arg t)) then
          Conv.every_conv [rewr_obj_eq UtilBase.all_trivial_th,
                           norm_all_disj ctxt] ct
        else
          Conv.every_conv [Conv.binder_conv (norm_all_disj o snd) ctxt] ct
      else if is_ball t then
        Conv.every_conv [rewr_obj_eq UtilBase.Ball_def_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_ex (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.not_ex_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_bex (dest_not t) then
        Conv.every_conv [
          Conv.arg_conv (rewr_obj_eq UtilBase.Bex_def_th), norm_all_disj ctxt] ct
      else if is_disj t then
        let
          val eq1 = Conv.binop_conv (norm_all_disj ctxt) ct
          val rhs = Util.rhs_of eq1
        in
          if is_obj_all (dest_arg1 rhs) then
            Conv.every_conv [Conv.rewr_conv eq1,
                             rewr_obj_eq UtilBase.disj_commute_th,
                             rewr_obj_eq UtilBase.swap_all_disj_th,
                             norm_all_disj ctxt] ct
          else if is_obj_all (dest_arg rhs) then
            Conv.every_conv [Conv.rewr_conv eq1,
                             rewr_obj_eq UtilBase.swap_all_disj_th,
                             norm_all_disj ctxt] ct
          else
            Conv.every_conv [Conv.rewr_conv eq1, norm_disj_clauses] ct
        end
      else if is_imp t then
        Conv.every_conv [rewr_obj_eq UtilBase.imp_conv_disj_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th, norm_all_disj ctxt] ct
      else if is_neg t andalso is_conj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_conj_th, norm_all_disj ctxt] ct
      else
        Conv.all_conv ct
    end

fun mk_disj_eq eq_ths =
    case eq_ths of
        [] => raise Fail "mk_disj_eq"
      | [eq] => eq
      | eq :: eqs' => Drule.binop_cong_rule UtilBase.cDisj eq (mk_disj_eq eqs')

(* Sort A | (B_1 | B_2 | ... | B_n), assuming the right side is sorted. *)
fun sort_disj_clause_aux ct =
    if not (is_disj (Thm.term_of ct)) then Conv.all_conv ct else
    let
      val (arg1, arg2) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_disj arg2 then
        if Term_Ord.termless (dest_arg1 arg2, arg1) then
          Conv.every_conv [rewr_obj_eq (obj_sym UtilBase.disj_assoc_th),
                           Conv.arg1_conv (rewr_obj_eq UtilBase.disj_commute_th),
                           rewr_obj_eq UtilBase.disj_assoc_th,
                           Conv.arg_conv sort_disj_clause_aux] ct
        else
          Conv.all_conv ct
      else
        if Term_Ord.termless (arg2, arg1) then
          rewr_obj_eq (obj_sym UtilBase.disj_commute_th) ct
        else
          Conv.all_conv ct
    end

(* Sort A_1 | ... | A_n. *)
fun sort_disj_clause ct =
    if not (is_disj (Thm.term_of ct)) then Conv.all_conv ct
    else Conv.every_conv [Conv.arg_conv sort_disj_clause,
                          sort_disj_clause_aux] ct

(* Apply cv on the body of !x y z. ... .*)
fun forall_body_conv cv ctxt ct =
    if is_obj_all (Thm.term_of ct) then
      Conv.binder_conv (fn (_, ctxt) => forall_body_conv cv ctxt) ctxt ct
    else
      cv ct

fun norm_all_disj_sorted ctxt ct =
    Conv.every_conv [norm_all_disj ctxt,
                     forall_body_conv sort_disj_clause ctxt] ct

fun abstract_eq ctxt var eq =
    let
      val (x, T) = Term.dest_Free var
      val all_const = Const (UtilBase.All_name, (T --> boolT) --> boolT)
    in
      Drule.arg_cong_rule (Thm.cterm_of ctxt all_const)
                          (Thm.abstract_rule x (Thm.cterm_of ctxt var) eq)
    end

fun replace_disj_vars ctxt (vars, disjs) =
    let
      val vars' = vars |> map Term.dest_Free
                       |> Variable.variant_frees ctxt []
                       |> map Free
      val subst = vars ~~ vars'
    in
      (vars', map (subst_atomic subst) disjs)
    end

(* Matching for all-disj propositions *)
fun disj_prop_match ctxt (id, (tyinst, inst)) (t, (var_u, cus)) =
    let
      val thy = Proof_Context.theory_of ctxt
      val us = map Thm.term_of cus
      val (var_t, ts) = (strip_all_disj t) |> replace_disj_vars ctxt
    in
      if length var_t <> length var_u orelse length ts <> length us then [] else
      let
        (* First match the types (return [] if no match). *)
        val tys_t = map fastype_of var_t
        val tys_u = map snd var_u
        val tyinst' = fold (Sign.typ_match thy) (tys_t ~~ tys_u) tyinst
        val var_t' = map (Envir.subst_term_types tyinst') var_t
        val ts' = ts |> map (Envir.subst_term_types tyinst')
        val var_ct' = map (Thm.cterm_of ctxt) var_t'
        val cus' = cus |> map (Thm.instantiate_cterm ([], var_u ~~ var_ct'))

        (* Match the type-instantiated pattern with term. *)
        val insts = Matcher.rewrite_match_subset
                        ctxt var_t' (ts', cus') (id, (tyinst', inst))

        fun process_inst ((id', instsp'), ths) =
            let
              (* Equality between normalized t and u *)
              val eq_th = ths |> mk_disj_eq
                              |> fold (abstract_eq ctxt) (rev var_t')
                              |> apply_to_lhs (norm_all_disj_sorted ctxt)
                              |> apply_to_rhs (norm_all_disj_sorted ctxt)

              (* Equality between un-normalized t and u *)
              val t' = Util.subst_term_norm instsp' t
              val norm1 = norm_all_disj_sorted ctxt (Thm.cterm_of ctxt t')
              val cu = Thm.cterm_of ctxt (mk_all_disj (var_t', map Thm.term_of cus'))
              val norm2 = norm_all_disj_sorted ctxt cu
              val eq_th' = Util.transitive_list [norm1, eq_th, meta_sym norm2]
            in
              ((id', instsp'), eq_th')
            end
      in
        map process_inst insts
      end
      handle Type.TYPE_MATCH => []
    end

(* Normalize (A_1 & A_2 & ... & A_m) & (B_1 & B_2 & ... & B_n) *)
fun norm_conj_clauses ct =
    let
      val (arg1, _) = Util.dest_binop_args (Thm.term_of ct)
    in
      if is_conj arg1 then
        Conv.every_conv [rewr_obj_eq UtilBase.conj_assoc_th,
                         Conv.arg_conv norm_conj_clauses] ct
      else
        Conv.all_conv ct
    end

fun norm_conj ct =
    let
      val t = Thm.term_of ct
      val _ = assert (fastype_of t = boolT) "norm_conj: wrong type"
    in
      if is_conj t then
        Conv.every_conv [Conv.binop_conv norm_conj, norm_conj_clauses] ct
      else if is_neg t andalso is_neg (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.nn_cancel_th, norm_conj] ct
      else if is_neg t andalso is_imp (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.not_imp_th, norm_conj] ct
      else if is_neg t andalso is_disj (dest_not t) then
        Conv.every_conv [rewr_obj_eq UtilBase.de_Morgan_disj_th, norm_conj] ct
      else
        Conv.all_conv ct
    end

(* DISJ items. *)

val TY_DISJ = "DISJ"

(* Given a theorem in the form of a disjunction, possibly containing
   schematic variables, return the corresponding DISJ item.
 *)
fun disj_to_ritems prem_only disj_head th =
    let
      val subs = strip_disj (prop_of' th)
    in
      if length subs = 1 then
        if Util.has_vars (Thm.prop_of th) then
          let
            fun th_to_ritem th =
                Fact (TY_DISJ,
                      UtilLogic.term_of_bool prem_only :: disj :: strip_disj (prop_of' th),
                      th)
          in
            map th_to_ritem (th |> apply_to_thm' norm_conj |> UtilLogic.split_conj_th)
          end
        else
          [Fact (TY_PROP, [prop_of' th], th)]
      else let
        val tname = UtilLogic.term_of_bool prem_only :: disj_head :: subs
      in
        [Fact (TY_DISJ, tname, th)]
      end
    end

fun disj_to_update prem_only disj_head (id, sc, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = sc,
                raw_items = disj_to_ritems prem_only disj_head th}

fun get_disj_head t =
    if is_disj t then disj
    else if is_imp t then get_disj_head (dest_arg t)
    else if is_neg t andalso is_neg (dest_not t) then
      get_disj_head (dest_not (dest_not t))
    else if is_neg t andalso is_conj (dest_not t) then conj
    else if is_obj_all t orelse is_ball t then
      case dest_arg t of
          Abs (x, T, body) => get_disj_head (snd (Term.dest_abs (x, T, body)))
        | _ => imp
    else if is_neg t andalso is_ex (dest_not t) then conj
    else if is_neg t andalso is_bex (dest_not t) then conj
    else imp

(* Convert theorems of form !!x y. P x y into P ?x ?y (arbitrary
   number of quantifiers).
 *)
fun forall_elim_sch th =
    let
      val thy = Thm.theory_of_thm th
    in
      case Thm.prop_of th of
          Const (@{const_name Pure.all}, _) $ Abs (x, T, _) =>
          let
            val var_xs = map fst (Term.add_var_names (Thm.prop_of th) [])
            val x' = if member (op =) var_xs x then
                        singleton (Name.variant_list var_xs) x
                     else x
          in
            th |> Thm.forall_elim (Thm.global_cterm_of thy (Var ((x', 0), T)))
               |> forall_elim_sch
          end
        | _ => th
    end

(* Given a theorem th, return equivalent theorem in disjunctive form,
   with possible schematic variables. Also return whether th is
   "active", that is, whether it is originally a conjunctive goal or
   disjunctive fact, as opposed to implications.
 *)
fun analyze_disj_th ctxt th =
    let
      val head = get_disj_head (prop_of' th)
      val th' = th |> apply_to_thm' (norm_all_disj ctxt)
                   |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                   |> forall_elim_sch
    in
      (head, th')
    end

(* Deconstruct the tname of a DISJ item. *)
fun dest_tname_of_disj tname =
    case tname of
        _ :: disj_head :: rest => (Thm.term_of disj_head, rest)
      | _ => raise Fail "dest_tname_of_disj: too few terms in tname."

(* Determine whether the item is for matching premises only (from the
   first entry in tname.
 *)
fun is_match_prem_only {tname, ...} =
    UtilLogic.bool_of_term (Thm.term_of (hd tname))

fun is_active_head disj_head = (not (disj_head aconv imp))

fun disj_rewr_terms ts =
    if UtilLogic.bool_of_term (hd ts) then [] else drop 2 ts

fun output_disj_fn ctxt (ts, _) =
    let
      val (match_prem, disj_head, subs) = (hd ts, hd (tl ts), tl (tl ts))
      val prefix = if UtilLogic.bool_of_term match_prem then "(match_prem) " else ""
    in
      if disj_head aconv disj then
        prefix ^ ((foldr1 mk_disj subs) |> Syntax.string_of_term ctxt)
      else if disj_head aconv conj then
        prefix ^ ((foldr1 mk_conj (map get_neg subs))
                      |> get_neg |> Syntax.string_of_term ctxt)
      else if disj_head aconv imp then
        prefix ^ ((foldr1 mk_imp (subs |> split_last |> apfst (map get_neg)
                                       |> apsnd single |> (op @)))
                      |> Syntax.string_of_term ctxt)
      else
        raise Fail "output_disj_fn: unexpected disj_head."
    end

val disj_prop_matcher =
    let
      fun pre_match pat {tname, ...} ctxt =
          let
            val (var_t, ts) = (strip_all_disj pat) |> replace_disj_vars ctxt
            val (_, cus) = dest_tname_of_disj tname
            val us = map Thm.term_of cus
            val var_u = fold Term.add_vars us []
          in
            length ts = length us andalso length var_t = length var_u
          end

      fun match pat item ctxt (id, instsp) =
          let
            val {tname, prop = th, ...} = item

            val (_, cus) = dest_tname_of_disj tname
            val us = map Thm.term_of cus
            val var_u = fold Term.add_vars us []

            fun process_perm perm =
                map (pair (map Var perm))
                    (disj_prop_match ctxt (id, instsp) (pat, (perm, cus)))

            fun process_inst (var_u, ((id', instsp'), eq_th)) =
                let
                  val eq_th' = make_trueprop_eq (meta_sym eq_th)
                  val forall_th =
                      th |> fold Thm.forall_intr (rev (map (Thm.cterm_of ctxt) var_u))
                         |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                in
                  ((id', instsp'), Thm.equal_elim eq_th' forall_th)
                end
          in
            var_u |> Util.all_permutes |> maps process_perm
                  |> map process_inst
          end
    in
      {pre_match = pre_match, match = match}
    end

fun is_priority_term t =
    if is_neg t then
      exists (is_ex orf is_bex) (strip_conj (dest_not t))
    else
      exists (is_obj_all orf is_ball) (strip_disj t)

(* Given ct in the form p_1 | ... | p_n, apply cv to each of p_i. *)
fun ac_disj_conv cv ct =
    if is_disj (Thm.term_of ct) then
      Conv.every_conv [Conv.arg1_conv cv,
                       Conv.arg_conv (ac_disj_conv cv)] ct
    else cv ct

(* Assume ct is a disjunction, associating to the right. *)
fun reduce_disj_True ct =
    if is_disj (Thm.term_of ct) then
      ((rewr_obj_eq UtilBase.disj_True1_th)
           else_conv ((Conv.arg_conv reduce_disj_True)
                          then_conv (rewr_obj_eq UtilBase.disj_True2_th))) ct
    else
      Conv.all_conv ct

(* Handles also the case where pat is in not-conj or imp form. *)
fun match_prop ictxt (id, item2) pat =
    let
      val disj_pats = strip_disj pat

      (* th is pat'(inst), where pat' is one of the disjunctive terms
         of pat.
       *)
      fun process_inst ((id, inst), th) =
          let
            val ctxt = IncrContext.context_of ictxt
            (* Construct the theorem pat'(inst) == True. *)
            val to_eqT_cv = (th RS UtilBase.eq_True_th) |> rewr_obj_eq |> Conv.try_conv

            (* Rewrite pat(inst) using the above, then rewrite to True. *)
            val pat_eqT =
                pat |> Thm.cterm_of ctxt |> norm_disj
                    |> Util.subst_thm ctxt inst
                    |> apply_to_rhs (ac_disj_conv to_eqT_cv)
                    |> apply_to_rhs reduce_disj_True
                    |> to_obj_eq
            val patT = pat_eqT RS UtilBase.eq_True_inv_th
          in
            ((id, inst), patT)
          end
    in
      ItemIO.get_insts (PropMatch pat) item2 ictxt (id, fo_init) @
      (if length disj_pats > 1 then
         map process_inst (maps (match_prop ictxt (id, item2)) disj_pats)
       else [])
    end

(* Given theorem ~P, cancel any disjunct that is aconv to P. It is
   possible to leave one disjunct P un-cancelled.
 *)
fun disj_cancel_cv ctxt th ct =
    if is_disj (Thm.term_of ct) then
      Conv.every_conv [Conv.arg_conv (disj_cancel_cv ctxt th),
                       Conv.try_conv (rewr_obj_eq (th RS UtilBase.or_cancel1_th)),
                       Conv.try_conv (rewr_obj_eq (th RS UtilBase.or_cancel2_th))] ct
    else
      Conv.all_conv ct

(* Given theorem ~P and a disjuncion theorem, return new disjunction
   theorem with P cancelled. If all disjuncts can be cancelled, return
   False.
 *)
fun disj_cancel_prop ctxt th prop =
    let
      val prop' = prop |> apply_to_thm' (disj_cancel_cv ctxt th)
      val P = th |> prop_of' |> dest_not
    in
      if prop_of' prop' aconv P then
        [th, prop'] MRS UtilBase.contra_triv_th
      else prop'
    end

fun is_avoid_term t =
    is_mem t andalso Term.is_Var (dest_arg1 t) andalso
    null (Term.add_frees (dest_arg t) [])

(* Reduce a disjunction p_1 | ... | t | ... | p_n by matching ~t with
   the second item. If the disjunction contains schematic variables, t
   must have either zero or the largest number of schematic variables.
 *)
fun match_update_fn ictxt item1 item2 =
    if is_match_prem_only item1 then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, prop, tname, ...} = item1
      val thy = Proof_Context.theory_of ctxt
      val (disj_head, csubs) = dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
      fun count_var t = length (Term.add_vars t [])
      val max_nvar = fold (curry Int.max) (map count_var subs) 0
      val has_priority_term = exists is_priority_term (map get_neg subs)

      val (NO_MATCH, FREE_ONLY, SLOW_MATCH, YES_MATCH) = (0, 1, 2, 3)
      (* Test whether to perform matching on pattern. *)
      fun test_do_match (i, sub, nvar) =
          if max_nvar = 0 then YES_MATCH
          else let
            val nsub = get_neg sub
          in
            if not (Util.is_pattern sub) then NO_MATCH
            else if length subs > 1 andalso
                    Property.is_property_prem thy nsub then NO_MATCH
            else if has_priority_term andalso
                    not (is_priority_term nsub) then SLOW_MATCH
            else if is_avoid_term nsub then SLOW_MATCH
            else if nvar = 0 orelse nvar = max_nvar then YES_MATCH
            else if i > 0 then NO_MATCH else FREE_ONLY
          end

      (* Match the negation of subs[i] with th2. For each match,
         instantiate in prop all schematic variables in t, so that t
         becomes ~th2. Then remove t from prop in the instantiated
         version.
       *)
      fun get_matches i =
          let
            val t = nth subs i
            val nvar = count_var t
            val do_match = test_do_match (i, t, nvar)
            fun process_inst ((id', inst), th) =
                let
                  val th' = if is_neg (prop_of' th) then th
                            else th RS UtilBase.nn_create_th
                  val prop' = prop |> Util.subst_thm_thy thy inst
                                   |> disj_cancel_prop ctxt th'
                  val sc = if max_nvar = 0 then 1
                           else if do_match = SLOW_MATCH then 200 else 10
                in
                  disj_to_update false disj_head (id', SOME sc, prop') ::
                  (if nvar > 0 then [] else
                   [ShadowItem {id = id', item = item1}])
                end
          in
            if do_match = NO_MATCH then []
            else if do_match = FREE_ONLY then
              t |> get_neg |> match_prop ictxt (id, item2)
                |> filter (fn ((_, inst), _) =>
                              forall (fn (_, (_, t)) => Term.is_Free t)
                                     (Vartab.dest (snd inst)))
                |> maps process_inst
            else
              t |> get_neg |> match_prop ictxt (id, item2)
                |> maps process_inst
          end
    in
      maps get_matches (0 upto (length subs - 1))
    end

val match_update_prfstep =
    {name = "disj_match_update",
     args = [TypedMatch (TY_DISJ, boolVar "C"),
             PropMatch (boolVar "A")],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_update_fn}

(* For DISJ items with a single term, of form f p1 ... pn, match t
   against each of p_i.
 *)
fun match_one_sch_fn ictxt item1 item2 =
    if is_match_prem_only item1 then [] else
    let
      val {id, tname, prop = th1, ...} = item1
      val ctxt = IncrContext.context_of ictxt
      val thy = Proof_Context.theory_of ctxt
      val subs = (dest_tname_of_disj tname) |> snd |> map Thm.term_of
    in
      if length subs > 1 then [] else
      let
        val t = the_single subs
        val args = Util.dest_args t
        fun count_var t = length (Term.add_vars t [])
        val nvar = count_var t

        fun get_matches i =
            if count_var (nth args i) < nvar then [] else
            let
              val arg = nth args i
              val insts = ItemIO.get_insts (TypedMatch (TY_TERM, arg)) item2 ictxt
                                           (id, fo_init)
              fun inst_to_updt ((id', inst), _) =
                  let
                    val th1' = Util.subst_thm_thy thy inst th1
                    val prop' = prop_of' th1'
                  in
                    if is_eq_term prop' andalso
                       RewriteTable.is_equiv_t id' ctxt (dest_eq prop')
                    then [] else [Update.thm_update (id', th1')]
                  end
            in
              maps inst_to_updt insts
            end
      in
        maps get_matches (0 upto (length args - 1))
      end
    end

val match_one_sch_prfstep =
    {name = "disj_match_one_sch",
     args = [TypedMatch (TY_DISJ, boolVar "C"),
             TypedMatch (TY_TERM, @{term_pat "?A"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_one_sch_fn}

fun disj_match_iff_fn ictxt {id, tname, prop, ...} =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val (_, csubs) = dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_eq_term (the_single subs) andalso
              fastype_of (dest_arg (the_single subs)) = boolT) then []
      else let
        val cv = (UtilLogic.to_obj_conv ctxt) then_conv (Trueprop_conv norm_disj)
        val forward = prop |> UtilLogic.equiv_forward_th |> apply_to_thm cv
        val backward = prop |> UtilLogic.equiv_backward_th |> apply_to_thm cv
      in
        [disj_to_update false imp (id, NONE, forward),
         disj_to_update false imp (id, NONE, backward)]
      end
    end

val disj_match_iff_prfstep =
    {name = "disj_match_iff",
     args = [TypedMatch (TY_DISJ, boolVar "A")],
     priority = PRIORITY_ADD,
     func = OneStep disj_match_iff_fn}

(* For active case, create box checking the next case. *)
fun disj_create_case_fn ictxt {id, tname, ...} =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    if exists Util.has_vars (map Thm.term_of tname) then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val (disj_head, csubs) = dest_tname_of_disj tname
    in
      if not (is_active_head disj_head) then []
      else if length csubs = 1 then []
      else let
        val subs = map Thm.term_of csubs
        val goal = get_neg (hd subs)
        val (vars, (As, C)) = (UtilLogic.strip_obj_horn goal)
                                  |> Util.replace_horn_vars ctxt
                                  |> Util.replace_horn_internal_vars
        val inits =
            map InitVar vars @ map (InitAssum o mk_Trueprop) As @
            [InitAssum (mk_Trueprop (get_neg C))]
      in
        [AddBoxes {id = id, sc = NONE, inits = inits}]
      end
    end

val disj_create_case_prfstep =
    {name = "disj_create_case",
     args = [TypedMatch (TY_DISJ, boolVar "A")],
     priority = PRIORITY_ADD,
     func = OneStep disj_create_case_fn}

(* item1 dominates item2 if the disjunctive terms in item1 is a subset
   of that for item2.
 *)
fun disj_shadow_fn ictxt (item1 as {tname = tname1, ...})
                   (item2 as {tname = tname2, ...}) =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val id = BoxItem.merged_id ctxt [item1, item2]
      val (disj_head1, subs1) = dest_tname_of_disj tname1
      val (disj_head2, subs2) = dest_tname_of_disj tname2
    in
      if not (is_active_head disj_head1) andalso
         is_active_head disj_head2 then []
      else if is_match_prem_only item1 andalso
              not (is_match_prem_only item2) then []
      else if subset (op aconvc) (subs1, subs2) then
        [ShadowItem {id = id, item = item2}]
      else []
    end

val disj_shadow_prfstep =
    {name = "disj_shadow",
     args = [TypedMatch (TY_DISJ, boolVar "A"),
             TypedMatch (TY_DISJ, boolVar "B")],
     priority = PRIORITY_SHADOW,
     func = TwoStep disj_shadow_fn}

val add_disj_proofsteps =
    fold ItemIO.add_item_type [
      (TY_DISJ, SOME disj_rewr_terms, SOME output_disj_fn)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_DISJ, ItemIO.univ_matcher)

    ] #> fold ItemIO.add_prop_matcher [
      (TY_DISJ, disj_prop_matcher)

    ] #> fold add_prfstep [
      match_update_prfstep, match_one_sch_prfstep, disj_match_iff_prfstep,
      disj_create_case_prfstep, disj_shadow_prfstep
    ]

(* Normalizers *)

(* Generalized form of splitting A & B. Also deal with cases ~(A | B)
   and ~(A --> B).
 *)
fun split_conj_gen_th _ th =
    th |> apply_to_thm' norm_conj
       |> UtilLogic.split_conj_th

fun eq_normalizer _ ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else if is_eq_term (prop_of' th) then
          let
            val (lhs, rhs) = dest_eq (prop_of' th)
          in
            [Fact (TY_EQ, [lhs, rhs], th)]
          end
        else [ritem]

fun property_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else let
          val thy = Proof_Context.theory_of ctxt
          val prop' = prop_of' th
        in
          if Property.is_property_const thy prop' then
            [Fact (TY_PROPERTY, [prop'], th)]
          else [ritem]
        end

fun disj_normalizer ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str <> TY_PROP then [ritem]
        else let
          val t = prop_of' th
        in
          if is_neg t andalso is_conj (dest_not t) orelse
             is_disj t orelse is_imp t orelse
             is_obj_all t orelse is_ball t orelse
             is_neg t andalso is_ex (dest_not t) orelse
             is_neg t andalso is_bex (dest_not t)
          then
            let
              val (disj_head, disj_th) = analyze_disj_th ctxt th
              val prem_only = Auto2_State.lookup_prem_only ctxt t
            in
              disj_to_ritems prem_only disj_head disj_th
            end
          else [ritem]
        end

fun logic_thm_update ctxt (id, th) =
    let
      val t = prop_of' th
    in
      if is_obj_all t orelse is_ball t orelse
         is_neg t andalso is_ex (dest_not t) orelse
         is_neg t andalso is_bex (dest_not t) orelse
         is_disj t orelse is_imp t orelse
         is_neg t andalso is_conj (dest_not t)
      then
        let
          val (disj_head, disj_th) = analyze_disj_th ctxt th
          val raw_items = disj_to_ritems true disj_head disj_th
        in
          AddItems {id = id, sc = NONE, raw_items = raw_items}
        end
      else
        Update.thm_update (id, th)
    end

val add_disj_normalizers =
    Normalizer.add_th_normalizer (
      "split_conj_gen", split_conj_gen_th

    ) #> fold Normalizer.add_normalizer [
      ("eq", eq_normalizer),
      ("property", property_normalizer),
      ("disj", disj_normalizer)
    ]

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup Logic_ProofSteps.add_logic_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_proofsteps
val _ = Theory.setup Logic_ProofSteps.add_disj_normalizers
val TY_DISJ = Logic_ProofSteps.TY_DISJ
