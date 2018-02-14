(* Proof steps for separation logic. *)

(* Data stored for each imperative command *)
type proc_info = {
  proc_defs: thm list,
  hoare_triples: thm list
}

val hoare_shadowing =
    Attrib.setup_config_bool @{binding "hoare_shadowing"} (K false)

signature SEP_LOGIC =
sig
  val normalize_mod_cv: Proof.context -> conv
  val normalize_hoare_goal_cv: Proof.context -> conv

  val empty_proc_info: proc_info
  val add_proc_def: thm -> theory -> theory
  val get_proc_def: theory -> string -> thm list
  val update_hoare_triple: thm -> theory -> theory
  val get_hoare_triples: theory -> string -> thm list

  val add_forward_ent_prfstep: thm -> theory -> theory
  val add_backward_ent_prfstep: thm -> theory -> theory
  val add_rewrite_ent_rule: thm -> theory -> theory

  val entails_goal: proofstep
  val entails_match: proofstep
  val entails_match_disj: proofstep

  val TY_CODE_POS: string

  val init_pos: proofstep
  val rewrite_pos: proofstep
  val match_hoare_disj: proofstep
  val match_assn_pure: proofstep
  val hoare_create_case: proofstep
  val hoare_triple: proofstep

  val contract_hoare_cv: Proof.context -> conv
  val add_hoare_triple_prfstep: thm -> theory -> theory

  val add_sep_logic_proofsteps: theory -> theory
end;

structure SepLogic : SEP_LOGIC =
struct

open SepUtil

(* Normalize a statement of the form h |= P, which can appear as
   either fact or goal. Assume P itself is normalized.
 *)
fun normalize_mod_cv' ctxt ct =
    let
      val t = Thm.term_of ct
      val (_, P) = dest_mod t
    in
      if is_pure_assn P then
        rewr_obj_eq @{thm mod_pure'} ct
      else if UtilArith.is_times P andalso is_pure_assn (dest_arg P) then
        Conv.every_conv [rewr_obj_eq @{thm mod_pure_star_dist},
                         Conv.arg1_conv (normalize_mod_cv' ctxt)] ct
      else if is_ex_assn P then
        Conv.every_conv [rewr_obj_eq @{thm mod_ex_dist},
                         Conv.binder_conv (normalize_mod_cv' o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

(* Full normalization of a statement of the form h |= P. *)
fun normalize_mod_cv ctxt ct =
    Conv.every_conv [mod_assn_conv (AssnNorm.normalize_assn_cv ctxt),
                     normalize_mod_cv' ctxt] ct

fun normalize_pure_cv ct =
    let
      val t = Thm.term_of ct
      val (_, P) = dest_mod t
    in
      if is_pure_assn P then
        Conv.every_conv [rewr_obj_eq @{thm mod_pure'}] ct
      else if UtilArith.is_times P andalso is_pure_assn (dest_arg P) then
        Conv.every_conv [rewr_obj_eq @{thm mod_pure_star_dist},
                         Conv.arg1_conv normalize_pure_cv] ct
      else
        Conv.all_conv ct
    end

fun normalize_ex_cv ctxt ct =
    let
      val t = Thm.term_of ct
      val (_, P) = dest_mod t
    in
      if is_ex_assn P then
        Conv.every_conv [rewr_obj_eq @{thm mod_ex_dist},
                         Conv.binder_conv (normalize_ex_cv o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

fun normalize_mod_ex_cv ctxt ct =
    Conv.every_conv [mod_assn_conv (AssnNorm.normalize_assn_cv ctxt),
                     normalize_ex_cv ctxt] ct

(* Normalize a Hoare triple goal. *)
fun normalize_hoare_goal_cv' ctxt ct =
    let
      val t = Thm.term_of ct
      val (P, _, _) = t |> dest_not |> dest_hoare_triple
    in
      if is_pure_assn P then
        rewr_obj_eq @{thm pre_pure_rule'} ct
      else if UtilArith.is_times P andalso is_pure_assn (dest_arg P) then
        Conv.every_conv [rewr_obj_eq @{thm pre_pure_rule},
                         Conv.arg1_conv (normalize_hoare_goal_cv' ctxt)] ct
      else if is_ex_assn P then
        Conv.every_conv [
          rewr_obj_eq @{thm pre_ex_rule},
          Conv.binder_conv (normalize_hoare_goal_cv' o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

fun normalize_hoare_goal_cv ctxt ct =
    if is_ex (Thm.term_of ct) then
      Conv.binder_conv (normalize_hoare_goal_cv o snd) ctxt ct
    else
      Conv.every_conv [
        Conv.arg_conv (Util.argn_conv 0 (AssnNorm.normalize_assn_cv ctxt)),
        normalize_hoare_goal_cv' ctxt] ct

(* Data maintained for each imperative command. *)
structure Data = Theory_Data (
  type T = proc_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (op pointer_eq)
)

val empty_proc_info = {proc_defs = [], hoare_triples = []}

(* Add imperative command with the given definitions. *)
fun add_proc_def th thy =
    let
      val th = if Util.is_meta_eq (Thm.prop_of th) then to_obj_eq th
               else th
      val nm = th |> prop_of' |> dest_arg1 |> name_of_sep_proc
      val {proc_defs, hoare_triples} =
          the_default empty_proc_info (Symtab.lookup (Data.get thy) nm)
      val new_info =
          {proc_defs = th :: proc_defs, hoare_triples = hoare_triples}
    in
      thy |> Data.map (Symtab.update (nm, new_info))
    end

fun get_proc_def thy nm =
    let
      val {hoare_triples, proc_defs, ...} =
          the_default empty_proc_info (Symtab.lookup (Data.get thy) nm)
    in
      if null hoare_triples then proc_defs else []
    end

(* Add the given theorem as a Hoare triple. Remove previous Hoare
   triples for this theorem.
 *)
fun update_hoare_triple hoare_th thy =
    let
      val (_, c, _) = dest_hoare_triple (prop_of' hoare_th)
      val nm = name_of_sep_proc c
      val {proc_defs, ...} =
          the_default empty_proc_info (Symtab.lookup (Data.get thy) nm)
      val new_info =
          {proc_defs = proc_defs, hoare_triples = [hoare_th]}
    in
      thy |> Data.map (Symtab.update (nm, new_info))
    end

(* Obtain list of Hoare triples for the given command *)
fun get_hoare_triples thy nm =
    let
      val {hoare_triples, ...} =
          the_default empty_proc_info (Symtab.lookup (Data.get thy) nm)
    in
      hoare_triples
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

fun forward_ent_prfstep_fn ent_th ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val (A, _) = dest_entail (prop_of' ent_th)
      val {id, prop, ...} = item
      val (_, P) = dest_mod (prop_of' prop)
      val cP = Thm.cterm_of ctxt P

      val insts = (AssnMatcher.assn_match_single ctxt (A, cP) (id, fo_init))
                      |> IncrContext.replace_id_for_type ictxt

      fun process_inst ((id', _), eq_th) =
          (* eq_th is P == pat(inst) * P' *)
          let
            val prop' = prop |> apply_to_thm' (
                  Conv.arg_conv (Conv.rewr_conv eq_th))
            val (ex_ritems, mod_th) =
                ([ent_th, prop'] MRS @{thm entailsD'})
                    |> mod_fact_ritems ctxt
            val ritems = ex_ritems @ [Update.thm_to_ritem mod_th]
          in
            [AddItems {id = id', sc = NONE, raw_items = ritems},
             ShadowItem {id = id', item = item}]
          end
    in
      if null insts then [] else process_inst (hd insts)
    end

fun forward_ent_prfstep ent_th =
    {name = Util.name_of_thm ent_th ^ "@ent",
     args = [TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_SHADOW,
     func = OneStep (forward_ent_prfstep_fn ent_th)}

fun backward_ent_prfstep_fn ent_th ictxt item =
    let
      val ctxt = IncrContext.context_of ictxt
      val (_, B) = dest_entail (prop_of' ent_th)
      val {id, prop, ...} = item
      val (_, P) = prop |> prop_of' |> dest_not |> dest_mod
      val cP = Thm.cterm_of ctxt P

      val insts = (AssnMatcher.assn_match_single ctxt (B, cP) (id, fo_init))
                      |> IncrContext.replace_id_for_type ictxt

      fun process_inst ((id', _), eq_th) =
          (* eq_th is P == pat(inst) * P' *)
          let
            val prop' = prop |> apply_to_thm' (
                  Conv.arg_conv (Conv.arg_conv (Conv.rewr_conv eq_th)))
            val res_th =
                ([ent_th, prop'] MRS @{thm entailsD_back})
                    |> apply_to_thm' (Conv.arg_conv (normalize_mod_ex_cv ctxt))
          in
            [Update.thm_update (id', res_th),
             ShadowItem {id = id', item = item}]
          end
    in
      if null insts then [] else process_inst (hd insts)
    end

fun backward_ent_prfstep ent_th =
    {name = (Util.name_of_thm ent_th) ^ "@entback",
     args = [TypedMatch (TY_PROP, @{term_pat "~(?h |= ?P)"})],
     priority = PRIORITY_SHADOW,
     func = OneStep (backward_ent_prfstep_fn ent_th)}

val entails_goal =
    ProofStep.prfstep_custom
        "sep.entails_goal"
        [WithProp @{term_pat "~(entails ?A ?B)"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn ctxt =>
            let
              val ex_th = ths MRS @{thm entailsE}
              val xs = map Name.internal ["h"]
              val (ex_ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th
              val (modP_th, goal_th) =
                  (conj_left_th res_th, conj_right_th res_th)
              val (ex_ritems', modP_th') = mod_fact_ritems ctxt modP_th
              val goal_th' = goal_th |> apply_to_thm' (
                    Conv.arg_conv (normalize_mod_ex_cv ctxt))
              val ritems = ex_ritems @ ex_ritems' @
                           map Update.thm_to_ritem [modP_th', goal_th']
            in
              [AddItems {id = id, sc = NONE, raw_items = ritems}]
            end)

(* item1 can be either PROP or DISJ. Use directly in the PROP case. *)
fun entails_match_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id1, prop = th1, ...} = item1
      val {id = id2, prop = th2, ...} = item2
      val (h, P) = dest_mod (dest_not (prop_of' th1))
      val P' = strip_pure_assn P
      val pat = mk_mod (h, P')
      val id = BoxID.merge_boxes ctxt (id1, id2)
      val insts = (AssnMatcher.mod_match_strict ctxt (pat, th2) (id, fo_init))
                      |> IncrContext.replace_id_for_type ictxt

      fun process_inst ((id', inst'), mod_th) =
          let
            val th1 = Util.subst_thm ctxt inst' th1
          in
            if P aconv P' then
              Update.thm_update (id', [th1, mod_th] MRS @{thm contra_triv})
            else let
              val cv = Conv.every_conv [Conv.arg_conv normalize_pure_cv,
                                        Logic_ProofSteps.norm_all_disj ctxt]
              val th1' = apply_to_thm' cv th1
              val res = [th1', mod_th] MRS @{thm Meson.make_refined_neg_rule}
            in
              Update.thm_update (id', res)
            end
          end
    in
      map process_inst insts
    end

val entails_match =
    {name = "sep.entails_match",
     args = [TypedMatch (TY_PROP, @{term_pat "~(?h |= ?P)"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?Q"})],
     priority = PRIORITY_ADD,
     func = TwoStep entails_match_fn}

fun entails_match_disj_fn ictxt item1 item2 =
    let
      val {tname, ...} = item1
      val (_, csubs) = Logic_ProofSteps.dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_neg (the_single subs)) orelse
              not (is_mod (dest_not (the_single subs))) then []
      else entails_match_fn ictxt item1 item2
    end

val entails_match_disj =
    {name = "sep.entails_match_disj",
     args = [TypedMatch (TY_DISJ, @{term_pat "?A::bool"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?Q"})],
     priority = PRIORITY_ADD,
     func = TwoStep entails_match_disj_fn}

fun is_bind_cmd c =
    case c of
        Const (@{const_name bind}, _) $ _ $ _ => true
      | _ => false

fun get_first_cmd c =
    case c of
        Const (@{const_name bind}, _) $ c1 $ _ => c1
      | _ => c

fun extract_return_name t =
    case t of
        Const (@{const_name bind}, _) $ _ $ Abs (x, _, _) =>
        if x = "uu_" then "u"  (* no assigned name *)
        else x  (* regular assigned name *)
      | _ => "r"  (* invalid input, return is a pair, etc. *)

(* CODE_POS item stores a Hoare triple goal, indicating the current
   position in the program.
 *)
val TY_CODE_POS = "CODE_POS"

(* ENTAIL item stores an entailment goal, usually indicating the end
   of the program.
 *)
val TY_ENTAIL = "ENTAIL"

fun is_neg_hoare_triple t =
    is_neg t andalso is_hoare_triple (dest_not t)

fun norm_precond ctxt ct =
    Util.argn_conv 0 (AssnNorm.normalize_assn_cv ctxt) ct

fun hoare_goal_ritems ctxt th =
    if Util.is_implies (Thm.prop_of th) then
      [Fact (TY_CODE_POS, [Thm.prop_of th], th)]
    else let
      val th' = th |> apply_to_thm' (normalize_hoare_goal_cv ctxt)
      val (vars, _) = (UtilLogic.strip_exists (prop_of' th'))
                          |> Util.replace_vars ctxt
                          |> Util.replace_internal_vars
      val xs = map (fst o Term.dest_Free) vars

      val (ex_ritems, res_th) =
          if length xs = 0 then ([], th')
          else Update.apply_exists_ritems ctxt xs th'

      val (res_th', rest) =
          res_th |> Logic_ProofSteps.split_conj_gen_th ctxt
                 |> filter_split (is_neg_hoare_triple o prop_of')
      val _ = assert (length res_th' = 1) "hoare_goal_ritems"

      val res_th' = res_th' |> the_single
                            |> apply_to_thm' (Conv.arg_conv (norm_precond ctxt))
    in
      ex_ritems @ map Update.thm_to_ritem rest @
      [Fact (TY_CODE_POS, [prop_of' res_th'], res_th')]
    end

fun hoare_goal_update ctxt (id, th) =
    AddItems {id = id, sc = SOME 1, raw_items = hoare_goal_ritems ctxt th}

fun entail_goal_update ctxt (id, th) =
    if Util.is_implies (Thm.prop_of th) then
      AddItems {id = id, sc = SOME 1,
                raw_items = [Fact (TY_ENTAIL, [Thm.prop_of th], th)]}
    else
      AddItems {id = id, sc = SOME 1,
                raw_items = [Update.thm_to_ritem th]}

(* Initialize CODE_POS item from a Hoare triple goal. *)
fun init_pos_fn ictxt item =
    let
      val {id, sc, prop, ...} = item
      val _ = assert (sc = 0) "init_pos"
      val ctxt = IncrContext.context_of ictxt
      val thy = Proof_Context.theory_of ctxt

      val (_, c, _) = dest_hoare_triple (get_neg (prop_of' prop))
      val nm = name_of_sep_proc c
      val proc_defs = get_proc_def thy nm

      fun process_proc_def proc_def =
          let
            val (lhs, _) = proc_def |> prop_of' |> dest_eq
            val cc = Thm.cterm_of ctxt c
            val insts = (Matcher.rewrite_match ctxt (lhs, cc) (id, fo_init))
                            |> IncrContext.replace_id_for_type ictxt

            fun process_inst ((id', _), eq_th) =
                let
                  val cv = Conv.every_conv [
                        Conv.rewr_conv (meta_sym eq_th), rewr_obj_eq proc_def]
                  val th = apply_to_thm' (Conv.arg_conv (Conv.arg1_conv cv)) prop
                in
                  hoare_goal_update ctxt (id', th)
                end
          in
            map process_inst insts
          end
    in
      if null proc_defs then
        [hoare_goal_update ctxt (id, prop)]
      else
        maps process_proc_def proc_defs
    end

val init_pos =
    {name = "sep.init_pos",
     args = [TypedMatch (TY_PROP, @{term_pat "~<?P> ?c <?Q>"})],
     priority = PRIORITY_ADD,
     func = OneStep init_pos_fn}

fun is_implies_code_pos item =
    Util.is_implies (Thm.prop_of (#prop item))

fun forward_hoare_prfstep_fn ent_th ictxt item =
    if is_implies_code_pos item then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val (A, _) = dest_entail (prop_of' ent_th)
      val {id, prop, ...} = item
      val (P, _, _) = prop |> prop_of' |> dest_not |> dest_hoare_triple
      val cP = Thm.cterm_of ctxt P

      val insts = (AssnMatcher.assn_match_single ctxt (A, cP) (id, fo_init))
                      |> IncrContext.replace_id_for_type ictxt

      fun process_inst ((id', _), eq_th) =
          let
            val prop' = prop |> apply_to_thm' (
                  Conv.arg_conv (Util.argn_conv 0 (Conv.rewr_conv eq_th)))
            val prop'' = [prop', ent_th] MRS @{thm pre_rule'}
          in
            [hoare_goal_update ctxt (id', prop''),
             ShadowItem {id = id', item = item}]
          end
    in
      if null insts then [] else process_inst (hd insts)
    end

fun forward_hoare_prfstep ent_th =
    {name = Util.name_of_thm ent_th ^ "@hoare_ent",
     args = [TypedMatch (TY_CODE_POS, Term.dummy)],
     priority = PRIORITY_SHADOW,
     func = OneStep (forward_hoare_prfstep_fn ent_th)}

fun add_forward_ent_prfstep ent_th thy =
    let
      val name = Util.name_of_thm ent_th
      val ctxt = Proof_Context.init_global thy
      val _ = writeln ("Add forward entailment " ^ name ^ "\n" ^
                       Syntax.string_of_term ctxt (prop_of' ent_th))
    in
      thy |> add_prfstep (forward_ent_prfstep ent_th)
          |> add_prfstep (forward_hoare_prfstep ent_th)
    end

fun add_backward_ent_prfstep ent_th thy =
    let
      val name = Util.name_of_thm ent_th
      val ctxt = Proof_Context.init_global thy
      val prfstep = backward_ent_prfstep ent_th
      val _ = writeln ("Add backward entailment " ^ name ^ "\n" ^
                       Syntax.string_of_term ctxt (prop_of' ent_th))
    in
      add_prfstep prfstep thy
    end

fun add_rewrite_ent_rule th thy =
    let
      val forward_th = (th RS @{thm entail_equiv_forward})
                           |> Drule.zero_var_indexes
                           |> Util.update_name_of_thm th "@forward"
      val backward_th = (th RS @{thm entail_equiv_backward})
                            |> Drule.zero_var_indexes
                            |> Util.update_name_of_thm th "@backward"
    in
      thy |> add_forward_ent_prfstep forward_th
          |> add_backward_ent_prfstep backward_th
    end

fun match_assn_props id ctxt hoare_th goal =
    let
      val (P1, c1, _) = dest_hoare_triple (concl_of' hoare_th)
      val (P2, c2, _) = dest_hoare_triple (dest_not (prop_of' goal))
      val c2' = get_first_cmd c2
      val _ = assert (c1 aconv c2' andalso P1 aconv P2) "match_assn_props"
    in
      if c2 aconv c2' then
        entail_goal_update ctxt (id, [hoare_th, goal] MRS @{thm post_rule'})
      else
        hoare_goal_update ctxt (id, [hoare_th, goal] MRS @{thm bind_rule'})
    end

(* Rewrite the first command of a Hoare triple. *)
fun rewr_first_cmd eq_th ct =
    let
      val (_, c, _) = ct |> Thm.term_of |> dest_hoare_triple
    in
      if is_bind_cmd c then
        Conv.arg1_conv (Conv.arg1_conv (rewr_obj_eq eq_th)) ct
      else
        Conv.arg1_conv (rewr_obj_eq eq_th) ct
    end

(* Apply rewrite to the first command in CODE_POS. *)
fun rewrite_pos_fn ictxt item1 item2 =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    if is_implies_code_pos item1 then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id1, prop = th, ...} = item1
      val {id = id2, prop = eq_th, ...} = item2
      val (_, c, _) = th |> prop_of' |> dest_not |> dest_hoare_triple
      val c' = get_first_cmd c
      val (c1, _) = eq_th |> prop_of' |> dest_eq
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      if c1 aconv c' then
        let
          val th' = th |> apply_to_thm' (Conv.arg_conv (rewr_first_cmd eq_th))
        in
          [hoare_goal_update ctxt (id, th'),
           ShadowItem {id = id, item = item1}]
        end
      else []
    end

val rewrite_pos =
    {name = "sep.rewrite_pos",
     args = [TypedMatch (TY_CODE_POS, Term.dummy),
             TypedMatch (TY_EQ, @{term_pat "(?c1::?'a Heap) = ?c2"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep rewrite_pos_fn}

fun normalize_hoare_cv ct =
    let
      val (P, _, _) = ct |> Thm.term_of |> dest_hoare_triple
    in
      if is_pure_assn P then
        rewr_obj_eq @{thm norm_pre_pure_iff2} ct
      else if UtilArith.is_times P andalso is_pure_assn (dest_arg P) then
        Conv.every_conv [rewr_obj_eq @{thm norm_pre_pure_iff},
                         Conv.arg_conv normalize_hoare_cv] ct
      else
        Conv.all_conv ct
    end

(* Contract a Hoare triple to <P> c <Q> form. *)
fun contract_hoare_cv' ct =
    if is_imp (Thm.term_of ct) then
      Conv.every_conv [Conv.arg_conv contract_hoare_cv',
                       rewr_obj_eq (obj_sym @{thm norm_pre_pure_iff})] ct
    else
      Conv.all_conv ct

fun contract_hoare_cv ctxt ct =
    Conv.every_conv [contract_hoare_cv', norm_precond ctxt] ct

fun match_hoare_th id ictxt hoare_th goal item =
    let
      val ctxt = IncrContext.context_of ictxt
      val (P, c, _) = goal |> prop_of' |> dest_not |> dest_hoare_triple
      val c' = get_first_cmd c

      val (P', pat, _) = dest_hoare_triple (prop_of' hoare_th)
      val cc = Thm.cterm_of ctxt c'
      val insts = Matcher.rewrite_match ctxt (pat, cc) (id, fo_init)

      fun process_inst ((id', inst), eq_th) =
          let
            val P'' = P' |> strip_pure_assn
                         |> Util.subst_term_norm inst
            val cP = Thm.cterm_of ctxt P
            val insts' =
                (AssnMatcher.assn_match_all ctxt (P'', cP) (id', inst))
                    |> IncrContext.replace_id_for_type ictxt

            fun process_inst' ((id'', inst''), ent_th) =
                let
                  val hoare_th =
                      (Util.subst_thm ctxt inst'' hoare_th)
                          |> apply_to_thm' (Conv.arg1_conv (Conv.rewr_conv eq_th))
                          |> apply_to_thm' normalize_hoare_cv
                          |> apply_to_thm (UtilLogic.to_meta_conv ctxt)
                  val hoare_th' =
                      [hoare_th, ent_th] MRS @{thm pre_rule''}
                in
                  [match_assn_props id'' ctxt hoare_th' goal,
                   ShadowItem {id = id'', item = item}]
                end
          in
            if null insts' then [] else process_inst' (hd insts')
          end
    in
      if null insts then [] else process_inst (hd insts)
    end

(* Match with PROP or DISJ items that are Hoare triples. In this
   function, we assume item1 is a Hoare triple (and item2 is the
   CODE_POS item).
 *)
fun match_hoare_prop_fn ictxt item1 item2 =
    if is_implies_code_pos item2 then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val {id = id1, prop = hoare_th, ...} = item1
      val {id = id2, prop = goal, ...} = item2
      val id = BoxID.merge_boxes ctxt (id1, id2)
    in
      match_hoare_th id ictxt hoare_th goal item2
    end

val match_hoare_prop =
    {name = "sep.match_hoare_prop",
     args = [TypedMatch (TY_PROP, @{term_pat "<?P> ?c <?Q>"}),
             TypedMatch (TY_CODE_POS, Term.dummy)],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_hoare_prop_fn}

(* For DISJ items, check that it is a Hoare triple. *)
fun match_hoare_disj_fn ictxt item1 item2 =
    if is_implies_code_pos item2 then [] else
    let
      val {tname, ...} = item1
      val (_, csubs) = Logic_ProofSteps.dest_tname_of_disj tname
      val subs = map Thm.term_of csubs
    in
      if length subs > 1 then []
      else if not (is_hoare_triple (the_single subs)) then []
      else match_hoare_prop_fn ictxt item1 item2
    end

val match_hoare_disj =
    {name = "sep.match_hoare_disj",
     args = [TypedMatch (TY_DISJ, Term.dummy),
             TypedMatch (TY_CODE_POS, Term.dummy)],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_hoare_disj_fn}

(* Match a MATCH_POS item with hoare triple <P * \<up>(b)> c <Q> with
   proposition b, resulting in a new MATCH_POS item (shadowing the
   original one) with hoare triple <P> c <Q>. Only work in the case
   where there are no schematic variables in b.
 *)
fun match_assn_pure_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, prop, ...} = item1
    in
      if Util.is_implies (Thm.prop_of prop) then
        let
          val (A, _) = Logic.dest_implies (Thm.prop_of prop)
          val pat = PropMatch (dest_Trueprop A)
          val insts = ItemIO.get_insts pat item2 ictxt (id, fo_init)

          fun process_inst ((id', _), th) =
              [hoare_goal_update ctxt (id', th RS prop),
               ShadowItem {id = id', item = item1}]
        in
          maps process_inst insts
        end
      else []
    end

val match_assn_pure =
    {name = "sep.match_assn_pure",
     args = [TypedMatch (TY_CODE_POS, Term.dummy),
             PropMatch (@{term_pat "?b::bool"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_assn_pure_fn}

fun hoare_create_case_fn ictxt item =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    let
      val {id, prop, ...} = item
    in
      if Util.is_implies (Thm.prop_of prop) then
        let
          val (A, _) = Logic.dest_implies (Thm.prop_of prop)
          val assum = get_neg' A
        in
          [AddBoxes {id = id, sc = SOME 1, inits = [InitAssum assum]}]
        end
      else []
    end

val hoare_create_case =
    {name = "sep.hoare_create_case",
     args = [TypedMatch (TY_CODE_POS, Term.dummy)],
     priority = PRIORITY_ADD,
     func = OneStep hoare_create_case_fn}

fun entail_pure_fn ictxt item1 item2 =
    let
      val ctxt = IncrContext.context_of ictxt
      val {id, prop, ...} = item1
    in
      if Util.is_implies (Thm.prop_of prop) then
        let
          val (A, _) = Logic.dest_implies (Thm.prop_of prop)
          val pat = PropMatch (dest_Trueprop A)
          val insts = ItemIO.get_insts pat item2 ictxt (id, fo_init)

          fun process_inst ((id', _), th) =
              [entail_goal_update ctxt (id', th RS prop),
               ShadowItem {id = id', item = item1}]
        in
          maps process_inst insts
        end
      else []
    end

val entail_pure =
    {name = "sep.entail_pure",
     args = [TypedMatch (TY_ENTAIL, Term.dummy),
             PropMatch (@{term_pat "?b::bool"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep entail_pure_fn}

fun entail_create_case_fn ictxt item =
    if not (IncrContext.is_single_ictxt ictxt) then [] else
    let
      val {id, prop, ...} = item
    in
      if Util.is_implies (Thm.prop_of prop) then
        let
          val (A, _) = Logic.dest_implies (Thm.prop_of prop)
          val assum = get_neg' A
        in
          [AddBoxes {id = id, sc = SOME 1, inits = [InitAssum assum]}]
        end
      else []
    end

val entail_create_case =
    {name = "sep.entail_create_case",
     args = [TypedMatch (TY_ENTAIL, Term.dummy)],
     priority = PRIORITY_ADD,
     func = OneStep entail_create_case_fn}

(* Matching CODE_POS with an existing Hoare triple. *)
fun hoare_triple_fn ictxt item =
    if is_implies_code_pos item then [] else
    let
      val ctxt = IncrContext.context_of ictxt
      val thy = Proof_Context.theory_of ctxt

      val {id, prop = goal, ...} = item
      val (_, c, _) = goal |> prop_of' |> dest_not |> dest_hoare_triple
      val hoare_ths = c |> get_first_cmd |> name_of_sep_proc
                        |> get_hoare_triples thy
    in
      maps (fn hoare_th => match_hoare_th id ictxt hoare_th goal item) hoare_ths
    end

val hoare_triple =
    {name = "sep.hoare_triple",
     args = [TypedMatch (TY_CODE_POS, Term.dummy)],
     priority = PRIORITY_SHADOW,
     func = OneStep hoare_triple_fn}

(* Given hoare_th of the form <?P> ?c <?Q>, produce proofstep matching
   item1 with CODE_POS (?h, ?c) and item2 with proposition ?h |= ?P *
   ?Ru.
 *)
fun add_hoare_triple_prfstep hoare_th thy =
    let
      val name = Util.name_of_thm hoare_th
      val ctxt = Proof_Context.init_global thy
      val hoare_th' =
          hoare_th |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                   |> apply_to_thm' (contract_hoare_cv ctxt)
                   |> Util.update_name_of_thm hoare_th ""
      val _ = writeln ("Add Hoare triple " ^ name ^ "\n" ^
                       Syntax.string_of_term ctxt (prop_of' hoare_th'))
    in
      thy |> update_hoare_triple hoare_th'
    end

fun code_pos_terms ts =
    let
      val t = the_single ts
    in
      if fastype_of t = propT then []
      else let
        val (P, c, _) = t |> dest_not |> dest_hoare_triple
      in
        [P, get_first_cmd c]
      end
    end

val add_sep_logic_proofsteps =
    fold ItemIO.add_item_type [
      (TY_CODE_POS, SOME code_pos_terms, NONE),
      (TY_ENTAIL, SOME (K []), NONE)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_CODE_POS, ItemIO.univ_matcher),
      (TY_ENTAIL, ItemIO.univ_matcher)

    ] #> fold add_prfstep [
      entails_goal, entails_match, entails_match_disj,
      init_pos, rewrite_pos, match_assn_pure, hoare_triple,
      match_hoare_disj, match_hoare_prop, hoare_create_case,
      entail_pure, entail_create_case
    ]

end  (* structure SepLogic *)

val _ = Theory.setup SepLogic.add_sep_logic_proofsteps
val add_proc_def = SepLogic.add_proc_def
val add_forward_ent_prfstep = SepLogic.add_forward_ent_prfstep
val add_rewrite_ent_rule = SepLogic.add_rewrite_ent_rule
val add_hoare_triple_prfstep = SepLogic.add_hoare_triple_prfstep
