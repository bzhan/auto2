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
  val normalize_hoare_cv: Proof.context -> conv

  val empty_proc_info: proc_info
  val add_proc_def: thm -> theory -> theory
  val get_proc_def: theory -> string -> thm list
  val update_hoare_triple: thm -> theory -> theory
  val get_hoare_triples: theory -> string -> thm list

  val add_forward_ent_prfstep: thm -> theory -> theory
  val add_forward_ent_shadowing_prfstep: thm -> theory -> theory
  val add_backward_ent_prfstep: thm -> theory -> theory
  val entail_equiv_forward_th: thm -> thm
  val entail_equiv_backward_th: thm -> thm
  val add_rewrite_ent_rule: thm -> theory -> theory

  val TY_CODE_POS: string
  val TY_MATCH_POS: string
  val output_code_pos_fn: item_output
  val output_code_pos_match_fn: item_output
  val code_pos_typed_matcher: item_matcher

  val find_proc_def: Proof.context -> term -> thm option
  val init_pos: proofstep
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

(* Normalize a statement of the form h |= P, which can appear as
   either fact or goal. Assume P itself is normalized.
 *)
fun normalize_mod_cv' ctxt ct =
    let
      val t = Thm.term_of ct
      val (_, P) = dest_mod t
    in
      if is_pure_assn P then
        Conv.every_conv [rewr_obj_eq @{thm mod_pure'}] ct
      else if UtilArith.is_times P andalso is_pure_assn (dest_arg P) then
        Conv.every_conv [
          rewr_obj_eq @{thm mod_pure_star_dist},
          Conv.arg1_conv (normalize_mod_cv' ctxt)] ct
      else if is_ex_assn P then
        Conv.every_conv [
          rewr_obj_eq @{thm mod_ex_dist},
          Conv.binder_conv (normalize_mod_cv' o snd) ctxt] ct
      else
        Conv.all_conv ct
    end

(* Full normalization of a statement of the form h |= P. *)
fun normalize_mod_cv ctxt ct =
    Conv.every_conv [mod_assn_conv (AssnNorm.normalize_assn_cv ctxt),
                     normalize_mod_cv' ctxt] ct

(* Normalize a Hoare triple *)
fun normalize_hoare_cv' ct =
    let
      val t = Thm.term_of ct
    in
      if is_imp t then
        Conv.every_conv [Conv.arg_conv normalize_hoare_cv',
                         rewr_obj_eq (obj_sym @{thm norm_pre_pure_iff})] ct
      else
        Conv.all_conv ct
    end

fun normalize_hoare_cv ctxt ct =
    Conv.every_conv [normalize_hoare_cv',
                     Util.argn_conv 0 (AssnNorm.normalize_assn_cv ctxt)] ct

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
      val {proc_defs, ...} =
          the_default empty_proc_info (Symtab.lookup (Data.get thy) nm)
    in
      proc_defs
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

fun forward_ent_prfstep_fn shadowing ent_th ictxt item =
    let
      val (A, _) = dest_entail (prop_of' ent_th)
      val ctxt = IncrContext.context_of ictxt
      val {id, tname, ...} = item
      val h_t = tname |> the_single |> Thm.term_of |> dest_mod |> fst
      val pat = mk_mod (h_t, A)
      val insts = mod_match_item ictxt (pat, item) (id, fo_init)

      fun process_inst ((id', _), th) =
          let
            val (ex_ritems, mod_th) =
                ([ent_th, th] MRS @{thm entailsD'})
                    |> mod_fact_ritems ctxt
            val ritems = ex_ritems @ [Update.thm_to_ritem mod_th]
          in
            [AddItems {id = id', sc = NONE, raw_items = ritems}] @
            (if shadowing then [ShadowItem {id = id', item = item}] else [])
          end
    in
      if null insts then [] else process_inst (hd insts)
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
      fun match pat {tname, prop, ...} ctxt (id, inst) =
          let
            val pats = HOLogic.strip_tuple pat
            val pairs = map (pair false)
                            (pats ~~ (take (length pats) tname))

            val insts = Matcher.rewrite_match_list ctxt pairs (id, inst)
            fun process_inst (inst, ths) =
                let
                  val obj_eqs = map (obj_sym o to_obj_eq) ths
                  val cv =
                      Conv.every_conv (map (rewr_obj_eq_bottom ctxt) obj_eqs)
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
   sep_proc. Return NONE or SOME (c == c').
 *)
fun find_proc_def ctxt c =
    let
      val thy = Proof_Context.theory_of ctxt
      val nm = name_of_sep_proc c
      val hoare_ths = get_hoare_triples thy nm
    in
      if null hoare_ths then
        let
          val ths = get_proc_def thy nm
        in
          SOME (Conv.first_conv (map rewr_obj_eq ths) (Thm.cterm_of ctxt c))
          handle CTERM _ => NONE
        end
      else NONE
    end

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
                             Fact (TY_CODE_POS, [h_t, c1, c], code_pos_th)]
            in
              [AddItems {id = id, sc = SOME 1, raw_items = ritems'}]
            end)

(* Produce the next CODE_POS item, as well as new variables and facts. *)
fun next_code_pos_ritems ctxt code_pos_th mod_th hoare_th =
    let
      val (run_th, all_th) =
          (conj_left_th code_pos_th, conj_right_th code_pos_th)

      (* Find current command, decompose into c1 or c1 ; c2 ... ; cn. *)
      val cur_cmd = run_th |> prop_of' |> Util.dest_args |> hd
      val is_bind = is_bind_cmd cur_cmd

      val (P, _, _) = dest_hoare_triple (prop_of' hoare_th)

      val mod_th' = if P aconv emp then
                      apply_to_thm' (mod_assn_conv mult_emp_left) mod_th
                    else mod_th
    in
      (* Case where the CODE_POS item has a composite command do { c1;
         c2 ; ... ; cn } (intermediate step).
       *)
      if is_bind then let
        val ex_th = [hoare_th, mod_th', run_th] MRS @{thm hoare_tripleE''}

        (* Below we will use r_ and h_ to denote the new variables. *)
        val x_r = extract_return_name cur_cmd
        val xs = map Name.internal [x_r, "h"]
        val (ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th

        (* Output res_th has three parts:

           - run_rest_th: run (c2 ; ... ; cn) (Some (fst h_)) \sigma r

           - modQ_th: h_ |= Q * P'

           - success_th: success c1 h h_ r_

         *)
        val (run_rest_th, modQ_th, success_th) =
            the_triple (UtilLogic.split_conj_th res_th)

        (* Extract c2 ; ... ; cn *)
        val rest_c = run_rest_th |> prop_of' |> Util.dest_args |> hd
        val next_is_bind = is_bind_cmd rest_c
        val rest_c1 = if next_is_bind then fst (dest_bind rest_c) else rest_c

        (* Extract h_ (or just h if heap preserving). *)
        val next_h_t = heap_of_mod_th modQ_th

        (* Use success_th to update all_th. *)
        val next_all_th = [success_th, all_th] MRS @{thm success_run_next}

        (* Form tname and prop of the new CODE_POS item. *)
        val tname = [next_h_t, rest_c1, rest_c]
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

        (* Below we will use h_ to denote the new variables. *)
        val xs = [Name.internal "h"]
        val (ritems, res_th) = Update.apply_exists_ritems ctxt xs ex_th

        (* The pair is:

           - modQ_th: h_ |= Q * P'

           - rest_th: \sigma = Some (fst h_) & success_run c h h_ r

         *)
        val (modQ_th, rest_th) = (conj_left_th res_th, conj_right_th res_th)

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
        val mod_pat = mk_mod (h_t, P)
        val insts = mod_match_item ictxt (mod_pat, item2) (id, fo_init)
        fun inst_to_updt ((id', _), mod_th) =
            let
              val ritems = next_code_pos_ritems ctxt code_pos_th mod_th hoare_th
            in
              [AddItems {id = id', sc = SOME 1, raw_items = ritems},
               ShadowItem {id = id', item = item2}]
            end
      in
        maps inst_to_updt insts
      end
    end

val match_assn =
    {name = "sep.match_assn",
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "?h"}),
             TypedMatch (TY_PROP, @{term_pat "?h |= ?P"})],
     priority = PRIORITY_SHADOW,
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
              val run_th = conj_left_th th
              val fullc' = Util.dest_argn 0 (prop_of' run_th)
              val (h, c) = apply2 (lookup_inst inst) ("h", "c")
              val tname = [h, c, fullc']
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
fun match_hoare_disj_fn ictxt item1 item2 =
    let
      val {id, tname, prop = th1, ...} = item1
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
        val (h_t, c1, _) = the_triple (map Thm.term_of tname2)
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

              val shadow = Config.get ctxt hoare_shadowing
            in
              [AddItems {id = id''', sc = NONE, raw_items = [ritem]}] @
              (if shadow then
                 [ShadowItem {id = id''', item = item2}]
               else [])
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
             TypedMatch (TY_CODE_POS, @{term_pat "(?h, ?c)"})],
     priority = PRIORITY_SHADOW,
     func = TwoStep match_hoare_disj_fn}

(* Match a proposition <P> c <Q> (without schematic variables) with a
   CODE_POS item (h, c). Produce MATCH_POS item of form (h, P)
   (similar to match_hoare_disj).
 *)
val match_hoare_prop =
    ProofStep.prfstep_custom
        "sep.match_hoare_prop"
        [WithFact @{term_pat "<?P> ?c::?'a Heap <?Q>"},
         WithItem (TY_CODE_POS, @{term_pat "(?h, ?c::?'a Heap)"}),
         ShadowSecond]
        PRIORITY_SHADOW
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
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "?h"}),
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
        val mod_pat = mk_mod (h, P')
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
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "?h"}),
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
     args = [TypedMatch (TY_MATCH_POS, @{term_pat "?h"})],
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
      val mod_pat = mk_mod (h_pat, P')

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
                     ShadowItem {id = id'', item = item1},
                     ShadowItem {id = id'', item = item2}]
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
      val ctxt = Proof_Context.init_global thy
      val hoare_th' =
          hoare_th |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
                   |> apply_to_thm' (normalize_hoare_cv ctxt)
                   |> Util.update_name_of_thm hoare_th ""
      val (_, c, _) = dest_hoare_triple (prop_of' hoare_th')
      val prev_ths = get_hoare_triples thy (name_of_sep_proc c)
      val prev_nms = map (fn th => Util.name_of_thm th ^ "@hoare") prev_ths
      val _ = writeln ("Add Hoare triple " ^ name ^ "\n" ^
                       Syntax.string_of_term ctxt (prop_of' hoare_th'))
    in
      thy |> fold del_prfstep prev_nms
          |> add_prfstep (hoare_triple_prfstep hoare_th')
          |> update_hoare_triple hoare_th'
    end

val add_sep_logic_proofsteps =
    fold ItemIO.add_item_type [
      (TY_CODE_POS, SOME (take 2), SOME output_code_pos_fn),
      (TY_MATCH_POS, SOME (take 2), SOME output_code_pos_match_fn)

    ] #> fold ItemIO.add_typed_matcher [
      (TY_CODE_POS, code_pos_typed_matcher),
      (TY_MATCH_POS, code_pos_typed_matcher)

    ] #> fold add_prfstep (
      normalize_mod_cv_prfsteps @ [
      init_pos, rewrite_pos, match_assn, match_assn_pure, match_assn_spatial,
      match_hoare_disj, match_hoare_prop, hoare_create_case
    ])

end  (* structure SepLogic *)

val _ = Theory.setup SepLogic.add_sep_logic_proofsteps
val add_proc_def = SepLogic.add_proc_def
val add_forward_ent_prfstep = SepLogic.add_forward_ent_prfstep
val add_rewrite_ent_rule = SepLogic.add_rewrite_ent_rule
val add_forward_ent_shadowing_prfstep = SepLogic.add_forward_ent_shadowing_prfstep
val add_hoare_triple_prfstep = SepLogic.add_hoare_triple_prfstep
