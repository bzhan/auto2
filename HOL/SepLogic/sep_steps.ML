(* Proof steps for separation logic. *)

signature SEP_LOGIC =
sig
  val add_forward_ent_prfstep: thm -> theory -> theory
  val add_forward_ent_shadowing_prfstep: thm -> theory -> theory
  val add_backward_ent_prfstep: thm -> theory -> theory
  val entail_equiv_forward_th: thm -> thm
  val entail_equiv_backward_th: thm -> thm
  val add_rewrite_ent_rule: thm -> theory -> theory
  val frame_entail: proofstep

  val TY_CODE_POS: string
  val TY_MATCH_POS: string
  val output_code_pos_fn: item_output
  val output_code_pos_match_fn: item_output
  val code_pos_typed_matcher: item_matcher

  val find_proc_def: Proof.context -> term -> thm option
  val heap_preservingI: proofstep
  val heap_preserving_effectD: thm -> proofstep
  val add_heap_preserving_thm: thm -> theory -> theory
  val init_pos: proofstep
  val find_heap_preserving_th: Proof.context -> term -> thm option
  val next_code_pos_ritems: Proof.context -> thm -> thm -> thm -> raw_item list
  val match_assn: proofstep
  val rewrite_pos: proofstep
  val match_hoare_disj: proofstep
  val match_assn_pure: proofstep
  val hoare_create_case: proofstep
  val match_assn_spatial: proofstep
  val hoare_triple_prfstep: thm -> proofstep
  val add_hoare_triple_prfstep: thm -> theory -> theory

  val add_sep_logic_proofsteps: theory -> theory
end;

structure SepLogic : SEP_LOGIC =
struct

open SepUtil

(* Rewrite on subterms, bottom order. *)
fun rewr_obj_eq_bottom ctxt eq_th =
    Conv.bottom_conv (K (Conv.try_conv (rewr_obj_eq eq_th))) ctxt

(* Proofsteps normalizing assertions. *)
fun normalize_mod_cv_prfstep (prfstep_name, pat) =
    ProofStep.prfstep_custom
        prfstep_name
        [WithItem (TY_PROP, pat)]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn ctxt =>
            let
              val th = the_single ths
              val th' =
                  if is_neg (prop_of' th) then
                    apply_to_thm' (Conv.arg_conv (normalize_mod_cv ctxt)) th
                  else
                    apply_to_thm' (normalize_mod_cv ctxt) th
            in
              if not (Thm.prop_of th aconv Thm.prop_of th') then
                [Update.thm_update (id, th'),
                 ShadowItem {id = id, item = the_single items}]
              else []
            end)

val normalize_mod_cv_prfsteps =
    [normalize_mod_cv_prfstep ("mod_norm", @{term_pat "?h |= ?P"}),
     normalize_mod_cv_prfstep ("mod_norm_neg", @{term_pat "~(?h |= ?P)"})]

fun mod_match_item ictxt (pat, item) (id, inst) =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id', prop, ...} = item
      val id'' = BoxID.merge_boxes ctxt (id, id')
    in
      (AssnMatcher.mod_match ctxt (pat, prop) (id'', inst))
          |> IncrContext.replace_id_for_type ictxt
    end

fun mod_inv_match_item ictxt (pat, item) (id, inst) =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id', prop, ...} = item
      val id'' = BoxID.merge_boxes ctxt (id, id')
    in
      (AssnMatcher.mod_inv_match ctxt (pat, prop) (id'', inst))
          |> IncrContext.replace_id_for_type ictxt
    end

fun forward_ent_prfstep_fn shadowing ent_th ictxt item =
    let
      val (A, B) = dest_entail (prop_of' ent_th)
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, ...} = item
      val h_t = tname |> the_single |> Thm.term_of |> dest_mod |> fst
      val pat = mk_mod (h_t, mk_star (A, Var (("Ru", 0), assnT)))
      val insts = mod_match_item ictxt (pat, item) (id, fo_init)
      val is_pure_B = strip_pure_assn B aconv assn_true

      fun process_inst ((id', _), th) =
          let
            val raw_items =
                ([ent_th, th] MRS @{thm entailsD'})
                    |> apply_to_thm' (normalize_mod_cv ctxt)
                    |> Logic_ProofSteps.split_conj_gen_th ctxt
                    |> (if is_pure_B then filter_out (is_mod o prop_of') else I)
                    |> map Update.thm_to_ritem
          in
            [AddItems {id = id', sc = NONE, raw_items = raw_items}] @
            (if shadowing then [ShadowItem {id = id', item = item}] else [])
          end
    in
      maps process_inst insts
    end

fun forward_ent_prfstep ent_th =
    {name = (Util.name_of_thm ent_th) ^ "@ent",
     args = [TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_ADD,
     func = OneStep (forward_ent_prfstep_fn false ent_th)}

fun forward_ent_shadowing_prfstep ent_th =
    {name = (Util.name_of_thm ent_th) ^ "@ent_shadow",
     args = [TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_SHADOW,
     func = OneStep (forward_ent_prfstep_fn true ent_th)}

fun add_forward_ent_prfstep ent_th =
    let
      val prfstep = forward_ent_prfstep ent_th
      val _ = writeln (#name prfstep)
    in
      add_prfstep prfstep
    end

fun add_forward_ent_shadowing_prfstep ent_th =
    add_prfstep (forward_ent_shadowing_prfstep ent_th)

fun backward_ent_prfstep_fn ent_th ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val (_, B) = dest_entail (prop_of' ent_th)
      val {id, tname, ...} = item
      val h_t = tname |> the_single |> Thm.term_of |> dest_not
                      |> dest_mod |> fst
      val pat = get_neg (mk_mod (h_t, mk_star (B, Var (("Ru", 0), assnT))))
      val insts = mod_inv_match_item ictxt (pat, item) (id, fo_init)

      fun process_inst ((id', _), th) =
          let
            val res_th =
                ([ent_th, th] MRS @{thm entailsD_back})
                    |> apply_to_thm' (Conv.arg_conv (normalize_mod_cv ctxt))
          in
            Update.thm_update (id', res_th)
          end
    in
      map process_inst insts
    end

fun backward_ent_prfstep ent_th =
    {name = (Util.name_of_thm ent_th) ^ "@entback",
     args = [TypedMatch (TY_PROP, @{term_pat "~(?h |= ?P)"})],
     priority = PRIORITY_ADD,
     func = OneStep (backward_ent_prfstep_fn ent_th)}

fun add_backward_ent_prfstep ent_th =
    let
      val prfstep = backward_ent_prfstep ent_th
      val _ = writeln (#name prfstep)
    in
      add_prfstep prfstep
    end

fun entail_equiv_forward_th th =
    (th RS @{thm entail_equiv_forward})
        |> Drule.zero_var_indexes
        |> Util.update_name_of_thm th "@ent_eqforward"

fun entail_equiv_backward_th th =
    (th RS @{thm entail_equiv_backward})
        |> Drule.zero_var_indexes
        |> Util.update_name_of_thm th "@ent_eqbackward"

fun add_rewrite_ent_rule eq_th thy =
    thy |> add_forward_ent_prfstep (entail_equiv_forward_th eq_th)
        |> add_backward_ent_prfstep (entail_equiv_backward_th eq_th)

(* Here item1 is a DISJ item of form A ==>_A B, where A and B may
   contain schematic variables. Match pattern h |= A * Ru with item2,
   and produce h |= B * Ru for each match.
 *)
fun frame_entail_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, prop = th1, ...} = item1
      val (_, csubs) = Logic_ProofSteps.dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_entail (the_single subs)) then []
      else let
        val (A, _) = dest_entail (the_single subs)
        val pat = mk_mod (Var (("h", 0), pheapT),
                          mk_star (A, Var (("Ru", 0), assnT)))
        val insts = mod_match_item ictxt (pat, item2) (id, fo_init)
        fun inst_to_updt ((id', _), th) =
            let
              val th' = ([th1, th] MRS @{thm entailsD'})
                            |> apply_to_thm' (normalize_mod_cv ctxt)
            in
              [Update.thm_update (id', th')]
            end
      in
        maps inst_to_updt insts
      end
    end

val frame_entail =
    {name = "frame_entail",
     args = [TypedMatch (TY_DISJ, @{term_pat "?A::bool"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_ADD,
     func = TwoStep frame_entail_fn}

fun is_bind_cmd t =
    case t of
        Const (@{const_name bind}, _) $ _ $ _ => true
      | _ => false

fun dest_bind t =
    case t of
        Const (@{const_name bind}, _) $ c1 $ rest => (c1, rest)
      | _ => raise Fail "dest_cmd"

fun extract_return_name t =
    case t of
        Const (@{const_name bind}, _) $ _ $ Abs (x, _, _) =>
        if x = "uu_" then "u"  (* no assigned name *)
        else x  (* regular assigned name *)
      | _ => "r"  (* invalid input, return is a pair, etc. *)

(* CODE_POS items indicate current position in the program. Here tname
   is the tuple (h, c), where h is the current heap and c is the first
   of the remaining commands.
 *)
val TY_CODE_POS = "CODE_POS"

(* MATCH_POS item indicate current position together with a hoare
   triple (possibly with schematic variables; either from existing
   theorem or induction hypothesis). The tname is (h, c, P, Q), where
   (P, Q) are the pre/post-condition of the hoare triple. Note Q is
   necessary to distinguish between MATCH_POS items with same
   pre-condition but differnt post-conditions.
 *)
val TY_MATCH_POS = "MATCH_POS"

fun output_code_pos_fn ctxt (tname, th) =
    let
      val is_bind = th |> conj_left_th |> prop_of' |> Util.dest_args |> hd
                       |> is_bind_cmd
    in
      "CODE_POS " ^ (if is_bind then "" else "(last) ") ^
      (Util.string_of_terms ctxt tname)
    end

fun output_code_pos_match_fn ctxt (tname, th) =
    "MATCH_POS " ^ (Syntax.string_of_term ctxt (hd tname)) ^ " " ^
    (Syntax.string_of_term ctxt (prop_of' (hd (UtilLogic.split_conj_th th))))

(* Common matcher for CODE_POS and MATCH_POS. When pattern is a tuple
   of n terms, match the first n terms of tname.
 *)
val code_pos_typed_matcher =
    let
      (* Check pat contains at least as many terms as tname. *)
      fun pre_match pat {tname, ...} ctxt =
          let
            val pats = HOLogic.strip_tuple pat
          in
            if length pats > length tname then false
            else forall (Matcher.pre_match ctxt)
                        (pats ~~ take (length pats) tname)
          end

      (* Use equalities to convert prop to prop'. *)
      fun match pat {tname, prop, ty_str, ...} ctxt (id, inst) =
          let
            val pats = HOLogic.strip_tuple pat
            val pairs = map (pair false)
                            (pats ~~ (take (length pats) tname))

            val insts = Matcher.rewrite_match_list ctxt pairs (id, inst)
            fun process_inst (inst, ths) =
                let
                  val obj_eqs = map (obj_sym o to_obj_eq) ths
                  (* Divide into cases depending on if obj_eqs
                     contains rewrites for P and Q (MATCH_POS) or not.
                   *)
                  val cv =
                      if ty_str = TY_MATCH_POS andalso length obj_eqs = 4 then
                        Conv.every_conv [
                          rewr_obj_eq_bottom ctxt (hd obj_eqs),
                          rewr_obj_eq_bottom ctxt (nth obj_eqs 1),
                          Conv.arg1_conv (
                            Util.argn_conv 0 (rewr_obj_eq (nth obj_eqs 2))),
                          Conv.arg1_conv (
                            Util.argn_conv 2 (rewr_obj_eq (nth obj_eqs 3)))]
                      else
                        Conv.every_conv (
                          map (rewr_obj_eq_bottom ctxt) obj_eqs)
                in
                  (inst, apply_to_thm' cv prop)
                end
          in
            map process_inst insts
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Find definition for a given procedure among the theorems
   sep_proc_defs. Return NONE or SOME (c == c').
 *)
fun find_proc_def ctxt c =
    let
      val ths = Named_Theorems.get ctxt @{named_theorems sep_proc_defs}
      fun rewr_cv th = if Util.is_meta_eq (Thm.prop_of th) then Conv.rewr_conv th
                       else rewr_obj_eq th
    in
      SOME (Conv.first_conv (map rewr_cv ths) (Thm.cterm_of ctxt c))
      handle CTERM _ => NONE
    end

(* To prove facts of form heap_preserving c (as initial goal), try to
   expand c, then use definition of heap_preserving.
 *)
val heap_preservingI =
    ProofStep.prfstep_custom
        "heap_preservingI"
        [WithGoal @{term_pat "heap_preserving ?c"}, ShadowFirst]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn _ => fn ctxt =>
            let
              val th = the_single ths
              val c = th |> prop_of' |> get_neg |> dest_arg
              val th' =
                  case find_proc_def ctxt c of
                      NONE => th
                    | SOME eq =>
                      th |> apply_to_thm' (
                        Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq)))
              val th_res =
                  th' |> apply_to_thm' (
                    Conv.arg_conv (rewr_obj_eq @{thm heap_preserving_def}))
            in
              [Update.thm_update (id, th_res)]
            end)

(* Given heap_preserving c, conclude h = h' from effect c h h' r. *)
fun heap_preserving_effectD presv_th =
    let
      val name = (Util.name_of_thm presv_th) ^ "effectD"
      val pat_c = presv_th |> prop_of' |> dest_arg
      val cT = fastype_of pat_c |> dest_Type |> snd |> the_single
      val heapT = @{typ heap}
      val pat =
          Const (@{const_name effect},
                 Type ("Heap", [cT]) --> heapT --> heapT --> cT --> boolT) $
                pat_c $ Var (("h", 0), heapT) $ Var (("h'", 0), heapT) $
                Var (("r", 0), cT)
      fun prfstep_fn ((id, _), ths) _ _ =
          let
            val res_th =
                [presv_th, the_single ths] MRS @{thm heap_preserving_effectD}
          in
            [Update.thm_update (id, res_th)]
          end
    in
      ProofStep.prfstep_custom name [WithFact pat] PRIORITY_ADD prfstep_fn
    end

(* Add the heap_preserving_effectD proofstep (for proving future
   heap_preserving results).
 *)
fun add_heap_preserving_thm presv_th thy =
    thy |> add_prfstep (heap_preserving_effectD presv_th)
        |> Context.theory_map (
              Named_Theorems.add_thm @{named_theorems sep_heap_presv_thms} presv_th)

(* Given theorem of form ~<P> c <Q>, attempt to expand the definition
   of c, using find_proc_def to lookup definitions.
 *)
fun rewrite_hoare_triple_goal ctxt th =
    let
      val (_, c, _) = dest_hoare_triple (get_neg (prop_of' th))
    in
      case find_proc_def ctxt c of
          NONE => th
        | SOME eq =>
          th |> apply_to_thm' (
            Conv.arg_conv (Conv.arg1_conv (Conv.rewr_conv eq)))
    end

(* Given fact of form h |= P, normalize, then use apply_exists when
   necessary.
 *)
fun mod_fact_ritems ctxt mod_th =
    let
      val mod_th' = apply_to_thm' (normalize_mod_cv ctxt) mod_th
      val (vars, _) = (UtilLogic.strip_exists (prop_of' mod_th'))
                          |> Util.replace_vars ctxt
                          |> Util.replace_internal_vars
      val xs = map (fst o Term.dest_Free) vars
    in
      if null xs then ([], mod_th')
      else Update.apply_exists_ritems ctxt xs mod_th'
    end

val init_pos =
    ProofStep.prfstep_custom
        "sep.init_pos"
        [WithProp @{term_pat "~<?P> ?c <?Q>"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn ctxt =>
            let
              (* First step, replace c by its definition in goal. *)
              val th = rewrite_hoare_triple_goal ctxt (the_single ths)

              val ex_th = th RS @{thm hoare_tripleI}
              val xs = map Name.internal ["h", "\<sigma>", "r"]
              val (ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th

              (* The pair is h_ |= P and what is to be placed into the
                 CODE_POS item.
               *)
              val (modP_th, code_pos_th) =
                  (conj_left_th res_th, conj_right_th res_th)

              val (_, c, _) = dest_hoare_triple (get_neg (prop_of' th))
              val is_bind = is_bind_cmd c
              val c1 = if is_bind then fst (dest_bind c) else c

              val h_t = heap_of_mod_th modP_th

              val (ritems_P, modP_th') = mod_fact_ritems ctxt modP_th
              val ritems' = ritems @ ritems_P @
                            [Update.thm_to_ritem modP_th',
                             Fact (TY_CODE_POS, [h_t, c1], code_pos_th)]
            in
              [AddItems {id = id, sc = SOME 1, raw_items = ritems'}]
            end)

(* Find heap preserving theorem for a command c, return NONE or SOME
   (heap_preserving c).
 *)
fun find_heap_preserving_th ctxt c =
    let
      val thy = Proof_Context.theory_of ctxt
      val ths = Named_Theorems.get ctxt @{named_theorems sep_heap_presv_thms}
      fun process_th th =
          let
            val pat = th |> prop_of' |> dest_arg
            val inst = Pattern.first_order_match thy (pat, c) fo_init
          in
            SOME (th |> Util.subst_thm ctxt inst)
          end
          handle Pattern.MATCH => NONE
    in
      get_first process_th ths
    end

(* Produce the next CODE_POS item, as well as new variables and facts. *)
fun next_code_pos_ritems ctxt code_pos_th mod_th hoare_th =
    let
      val (run_th, all_th) =
          (conj_left_th code_pos_th, conj_right_th code_pos_th)

      (* Find current command, decompose into c1 or c1 ; c2 ... ; cn. *)
      val cur_cmd = run_th |> prop_of' |> Util.dest_args |> hd
      val is_bind = is_bind_cmd cur_cmd
      val c1 = if is_bind then fst (dest_bind cur_cmd) else cur_cmd
      val heap_preserve_opt = find_heap_preserving_th ctxt c1

      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)

      (* When conclusion is of the form h |= Q * emp, reduce to h |=
         Q.
       *)
      val try_reduce_emp_right_th =
          apply_to_thm (
            Util.concl_conv (Trueprop_conv (Conv.try_conv reduce_emp_right)))

      val mod_th' = if P aconv emp then
                      apply_to_thm' (mod_assn_conv mult_emp_left) mod_th
                    else mod_th
    in
      (* Case where the CODE_POS item has a composite command do { c1;
         c2 ; ... ; cn } (intermediate step).
       *)
      if is_bind then let
        val ex_th = [hoare_th, mod_th', run_th] MRS @{thm hoare_tripleE''}
        val ex_th' = if is_none heap_preserve_opt then ex_th
                     else [the (heap_preserve_opt), ex_th]
                              MRS @{thm hoare_tripleE''_preserve}

        (* Below we will use r_ and h_ to denote the new variables. *)
        val x_r = extract_return_name cur_cmd
        val xs = if is_some heap_preserve_opt then [Name.internal x_r]
                 else map Name.internal [x_r, "h"]
        val (ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th'

        (* Output res_th has three parts:

           - run_rest_th: run (c2 ; ... ; cn) (Some (fst h_)) \sigma r

           - modQ_th: h_ |= Q * P'

           - success_th: success c1 h h_ r_

         *)
        val (run_rest_th, modQ_th, success_th) =
            the_triple (UtilLogic.split_conj_th res_th)
        val modQ_th = try_reduce_emp_right_th modQ_th

        (* Extract c2 ; ... ; cn *)
        val rest_c = run_rest_th |> prop_of' |> Util.dest_args |> hd
        val next_is_bind = is_bind_cmd rest_c
        val rest_c1 = if next_is_bind then fst (dest_bind rest_c) else rest_c

        (* Extract h_ (or just h if heap preserving). *)
        val next_h_t = heap_of_mod_th modQ_th

        (* Use success_th to update all_th. *)
        val next_all_th = [success_th, all_th] MRS @{thm success_run_next}

        (* Form tname and prop of the new CODE_POS item. *)
        val tname = [next_h_t, rest_c1]
        val next_code_pos_th = UtilLogic.mk_conjs_th [run_rest_th, next_all_th]

        (* ritems for modQ_th. *)
        val (ritems_Q, modQ_th') = mod_fact_ritems ctxt modQ_th
      in
        ritems @ ritems_Q @
        [Update.thm_to_ritem modQ_th',
         Fact (TY_CODE_POS, tname, next_code_pos_th)]
      end
      (* Case where the command is not composite (last step). *)
      else let
        val ex_th = [hoare_th, mod_th', run_th] MRS @{thm hoare_tripleE'}
        val ex_th' = if is_none heap_preserve_opt then ex_th
                     else [the (heap_preserve_opt), ex_th]
                              MRS @{thm hoare_tripleE'_preserve}

        (* Below we will use h_ to denote the new variables. *)
        val xs = if is_some heap_preserve_opt then []
                 else [Name.internal "h"]
        val (ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th'

        (* The pair is:

           - modQ_th: h_ |= Q * P'

           - rest_th: \sigma = Some (fst h_) & success_run c h h_ r

         *)
        val (modQ_th, rest_th) = (conj_left_th res_th, conj_right_th res_th)
        val modQ_th = try_reduce_emp_right_th modQ_th

        (* \sigma = Some (fst h_) & success_run c h h_ r ==> ... *)
        val vars = [Var (("h_", 0), pheapT)]
        val all_th' = all_th |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                             |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) vars)
        val Q_goal =
            (rest_th RS all_th')
                |> apply_to_thm' (Conv.arg_conv (normalize_mod_cv ctxt))

        (* ritems for modQ_th. *)
        val (ritems_Q, modQ_th') = mod_fact_ritems ctxt modQ_th
      in
        ritems @ ritems_Q @ map (Update.thm_to_ritem) [modQ_th', Q_goal]
      end
    end

(* Matching a MATCH_POS item with tname (h, c, P, Q) to propositions h
   |= P * Ru (or R if P is emp), and produce the next CODE_POS item.
 *)
fun match_assn_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, prop, ...} = item1
      val h_t = Thm.term_of (hd tname)
      val (hoare_th, code_pos_th) = (conj_left_th prop, conj_right_th prop)
      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)
    in
      if has_pure_assn P then []
      else let
        val P_pat = if P aconv emp then Var (("Ru", 0), assnT)
                    else mk_star (P, Var (("Ru", 0), assnT))
        val mod_pat = mk_mod (h_t, P_pat)
        val insts = mod_match_item ictxt (mod_pat, item2) (id, fo_init)
        fun inst_to_updt ((id', _), mod_th) =
            let
              val ritems = next_code_pos_ritems ctxt code_pos_th mod_th hoare_th
            in
              AddItems {id = id', sc = SOME 1, raw_items = ritems}
            end
      in
        map inst_to_updt insts
      end
    end

val match_assn =
    {name = "sep.match_assn",
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "(?h, ?c)"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_assn_fn}

(* Given CODE_POS item with parameters (h, c), where c can be
   rewritten as c1 ; c2 ; ... ; cn (for example, using rewriting rules
   for if or case), update c to c1 and modify the prop accordingly.
 *)
val rewrite_pos =
    ProofStep.prfstep_custom
        "sep.rewrite_pos"
        [WithItem (TY_CODE_POS, @{term_pat "(?h, bind ?c ?c')"}),
         ShadowFirst]
        PRIORITY_SHADOW
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val th = the_single ths
              val tname = map (lookup_inst inst) ["h", "c"]
              val ritem = Fact (TY_CODE_POS, tname, th)
            in
              [AddItems {id = id, sc = SOME 1, raw_items = [ritem]}]
            end)

(* Here item1 is a DISJ item of form <P> c <Q>, where P, c, and Q may
   contain schematic variables. item2 is a CODE_POS item (h,
   c1). Match pattern c with c1, and produce a MATCH_POS item of form
   (h, P) containing the instantiated hoare triple as well as theorems
   from item2.
 *)
fun match_hoare_disj_fn ictxt {id, tname, prop = th1, ...} item2 =
    let
      val (_, csubs) = Logic_ProofSteps.dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_hoare_triple (the_single subs)) then []
      else let
        val ctxt = IncrContext.context_of ictxt
        val thy = Proof_Context.theory_of ctxt
        val _ = assert (length subs = 1)
                       "match_hoare_disj_fn: unexpected DISJ."
        val (_, c, _) = dest_hoare_triple (the_single subs)
        val {id = id', tname = tname2, prop = th2, ...} = item2
        val (h_t, c1) = the_pair (map Thm.term_of tname2)
        val id'' = BoxID.merge_boxes ctxt (id, id')
        val insts =
            (Matcher.rewrite_match ctxt (c, Thm.cterm_of ctxt c1) (id'', fo_init))
                |> IncrContext.replace_id_for_type ictxt
        fun process_inst ((id''', inst), eq_th) =
            let
              (* Substitute and rewrite command to c1. *)
              val th1' =
                  th1 |> Util.subst_thm_thy thy inst
                      |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv eq_th))
              val (P', _, Q') = dest_hoare_triple (prop_of' th1')
              val new_tname = [h_t, c1, P', Q']
              val new_prop = UtilLogic.mk_conjs_th [th1', th2]
              val ritem = Fact (TY_MATCH_POS, new_tname, new_prop)
            in
              [AddItems {id = id''', sc = NONE, raw_items = [ritem]}]
            end
      in
        maps process_inst insts
      end
    end

(* Note we will be matching the instantiations of ?c and ?c' in the
   proofstep, so they may take different values in the pre-filter.
 *)
val match_hoare_disj =
    {name = "sep.match_hoare_disj",
     args = [TypedMatch (TY_DISJ, @{term_pat "?A::bool"}),
             TypedMatch (TY_CODE_POS, @{term_pat "(?h, ?c')"})],
     priority = PRIORITY_ADD,
     func = TwoStep match_hoare_disj_fn}

(* Match a proposition <P> c <Q> (without schematic variables) with a
   CODE_POS item (h, c). Produce MATCH_POS item of form (h, P)
   (similar to match_hoare_disj).
 *)
val match_hoare_prop =
    ProofStep.prfstep_custom
        "sep.match_hoare_prop"
        [WithFact @{term_pat "<?P> ?c::?'a Heap <?Q>"},
         WithItem (TY_CODE_POS, @{term_pat "(?h, ?c::?'a Heap)"})]
        PRIORITY_ADD
        (fn ((id, inst), ths) => fn _ => fn _ =>
            let
              val tname = map (lookup_inst inst) ["h", "c", "P", "Q"]
              val prop = UtilLogic.mk_conjs_th ths
              val ritem = Fact (TY_MATCH_POS, tname, prop)
            in
              [AddItems {id = id, sc = NONE, raw_items = [ritem]}]
            end)

(* Match a MATCH_POS item with hoare triple <P * \<up>(b)> c <Q> with
   proposition b, resulting in a new MATCH_POS item (shadowing the
   original one) with hoare triple <P> c <Q>. Only work in the case
   where there are no schematic variables in b.
 *)
fun match_assn_pure_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, prop, tname, ...} = item1
      val (h, c, P) = the_triple (take 3 (map Thm.term_of tname))
      val Ps = ACUtil.dest_ac assn_ac_info P
      val bs = filter is_pure_assn Ps
    in
      if Util.has_vars P orelse null bs then []
      else let
        val pat = dest_arg (hd bs)
        val insts = ItemIO.get_insts (PropMatch pat) item2 ictxt (id, fo_init)

        fun process_inst ((id', _), th) =
            let
              val move_outmost =
                  Util.argn_conv 0 (ACUtil.move_outmost assn_ac_info (hd bs))
              val norm_th = if length Ps = 1 then @{thm norm_pre_pure_iff2}
                            else @{thm norm_pre_pure_iff}
              val hoare_th = conj_left_th prop
              val hoare_th' =
                  hoare_th |> apply_to_thm' move_outmost
                           |> apply_to_thm' (rewr_obj_eq norm_th)
                           |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                           |> Thm.elim_implies th
              val (P', _, Q') = dest_hoare_triple (prop_of' hoare_th')
              val new_prop =
                  UtilLogic.mk_conjs_th [hoare_th', conj_right_th prop]
              val ritem = Fact (TY_MATCH_POS, [h, c, P', Q'], new_prop)
            in
              [AddItems {id = id', sc = SOME 1, raw_items = [ritem]},
               ShadowItem {id = id', item = item1}]
            end
      in
        maps process_inst insts
      end
    end

val match_assn_pure =
    {name = "sep.match_assn_pure",
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "(?h, ?c, ?P, ?Q)"}),
             PropMatch (@{term_pat "?b::bool"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_assn_pure_fn}

(* Given a MATCH_POS item with tname (h, c, P, Q), where P contains
   schematic variables. Let P' be the spatial (non-pure) part of
   P. Match with propositions h |= P' * Ru, and produce instantiated
   version of MATCH_POS.
 *)
fun match_assn_spatial_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, prop, ...} = item1
      val (h, c, P) = the_triple (take 3 (map Thm.term_of tname))
      val P' = strip_pure_assn P
    in
      if not (Util.has_vars P) orelse not (has_pure_assn P) then []
      else let
        val P_pat = mk_star (P', Var (("Ru", 0), assnT))
        val mod_pat = mk_mod (h, P_pat)
        val insts = mod_match_item ictxt (mod_pat, item2) (id, fo_init)
        fun process_inst ((id', inst), _) =
            let
              val (hoare_th, success_ths) =
                  (conj_left_th prop, conj_right_th prop)
              val hoare_th' = Util.subst_thm ctxt inst hoare_th
              val (P'', _, Q'') = dest_hoare_triple (prop_of' hoare_th')
              val prop' = UtilLogic.mk_conjs_th [hoare_th', success_ths]
              val ritem = Fact (TY_MATCH_POS, [h, c, P'', Q''], prop')
            in
              [AddItems {id = id', sc = SOME 1, raw_items = [ritem]},
               ShadowItem {id = id', item = item1}]
            end
      in
        maps process_inst insts
      end
    end

val match_assn_spatial =
    {name = "sep.match_assn_spatial",
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "(?h, ?c, ?P, ?Q)"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?P'"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_assn_spatial_fn}

fun hoare_create_case_fn ictxt item =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    let
      val {id, tname, ...} = item
      val (_, _, P) = the_triple (take 3 (map Thm.term_of tname))
      val Ps = ACUtil.dest_ac assn_ac_info P
      val bs = filter is_pure_assn Ps
    in
      if Util.has_vars P orelse null bs then []
      else let
        val assum = mk_Trueprop (get_neg (dest_arg (hd bs)))
      in
        [AddBoxes {id = id, sc = SOME 1, inits = [InitAssum assum]}]
      end
    end

val hoare_create_case =
    {name = "sep.hoare_create_case",
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "(?h, ?c, ?P, ?Q)"})],
     priority = PRIORITY_ADD,
     func = OneStep hoare_create_case_fn}

(* Proofstep for moving to next code position. Here hoare_th is the
   hoare triple <P> c <Q>, item1 is the CODE_POS item with parameters
   (h, c), and item2 gives the proposition h |= P * P'.
 *)
fun hoare_triple_prfstep_fn hoare_th ictxt item1 item2 =
    let
      val (P, pat_c, _) = dest_hoare_triple (prop_of' hoare_th)
      val P' = strip_pure_assn P
      val ctxt = IncrContext.context_of ictxt

      (* Match the first item with CODE_POS (h, c), and the second
         item with h |= P'.
       *)
      val h_pat = Var (("h", 0), pheapT)
      val code_pos_pat = HOLogic.mk_tuple [h_pat, pat_c]
      val P_pat = if P' aconv emp then Var (("Ru", 0), assnT)
                  else mk_star (P', Var (("Ru", 0), assnT))
      val mod_pat = mk_mod (h_pat, P_pat)

      val arg1 = TypedMatch (TY_CODE_POS, code_pos_pat)
      val insts = ItemIO.match_arg ctxt arg1 item1 ([], fo_init)

      fun process_inst ((id', inst'), code_pos_th) =
          let
            val mod_pat' = Util.subst_term_norm inst' mod_pat
            val insts' = mod_match_item ictxt (mod_pat', item2) (id', inst')
            fun process_inst' ((id'', inst''), mod_th) =
                if has_pure_assn P then
                  let
                    val (h, c) =
                        apply2 (Util.subst_term_norm inst'') (h_pat, pat_c)
                    val hoare_th' = Util.subst_thm ctxt inst'' hoare_th
                    val (P'', _, Q'') = dest_hoare_triple (prop_of' hoare_th')
                    val prop' = UtilLogic.mk_conjs_th [hoare_th', code_pos_th]
                    val ritem = Fact (TY_MATCH_POS, [h, c, P'', Q''], prop')
                  in
                    [AddItems {id = id'', sc = SOME 1, raw_items = [ritem]},
                     ShadowItem {id = id'', item = item1}]
                  end
                else
                  let
                    val ritems =
                        next_code_pos_ritems ctxt code_pos_th mod_th hoare_th
                  in
                    [AddItems {id = id'', sc = SOME 1, raw_items = ritems},
                     ShadowItem {id = id'', item = item1}]
                  end
          in
            maps process_inst' insts'
          end
    in
      maps process_inst insts
    end

fun hoare_triple_prfstep hoare_th =
    {name = (Util.name_of_thm hoare_th) ^ "@hoare",
     args = [TypedMatch (TY_CODE_POS, @{term_pat "(?h, ?c)"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep (hoare_triple_prfstep_fn hoare_th)}

(* Given hoare_th of the form <?P> ?c <?Q>, produce proofstep matching
   item1 with CODE_POS (?h, ?c) and item2 with proposition ?h |= ?P *
   ?Ru.
 *)
fun add_hoare_triple_prfstep hoare_th thy =
    let
      val name = Util.name_of_thm hoare_th
      val _ = writeln ("Add Hoare triple " ^ name)
    in
      add_prfstep (hoare_triple_prfstep hoare_th) thy
    end

val add_sep_logic_proofsteps =
    fold ItemIO.add_item_type [
      (TY_CODE_POS, NONE, SOME output_code_pos_fn),
      (TY_MATCH_POS, NONE, SOME output_code_pos_match_fn)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_CODE_POS, code_pos_typed_matcher),
      (TY_MATCH_POS, code_pos_typed_matcher)

    ] #> fold add_prfstep (
      normalize_mod_cv_prfsteps @ [
      frame_entail, heap_preservingI, init_pos, rewrite_pos,
      match_assn, match_assn_pure, match_assn_spatial,
      match_hoare_disj, match_hoare_prop, hoare_create_case
    ])

end  (* structure SepLogic *)

val _ = Theory.setup SepLogic.add_sep_logic_proofsteps
val add_heap_preserving_thm = SepLogic.add_heap_preserving_thm
val add_forward_ent_prfstep = SepLogic.add_forward_ent_prfstep
val add_rewrite_ent_rule = SepLogic.add_rewrite_ent_rule
val add_forward_ent_shadowing_prfstep = SepLogic.add_forward_ent_shadowing_prfstep
val add_hoare_triple_prfstep = SepLogic.add_hoare_triple_prfstep
