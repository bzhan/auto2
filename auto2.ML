(* Main file defining inference algorithm and tactic. *)

signature SCORES =
sig
  val item_score: raw_item -> int
  val items_score: raw_item list -> int
  val get_score: Update.raw_update -> int
  val get_id_score: status -> Update.raw_update -> int
end;

structure Scores : SCORES =
struct

open Box

fun item_score ritem =
    case ritem of
        Handler _ => 0
      | Fact (ty_str, tname, _) =>
        (case ty_str of
             "VAR" => 10  (* cost of introducing a variable. *)
           | _ => size_of_term tname)

fun init_score init =
    case init of
        Update.InitVar _ => 0
      | Update.InitAssum t => size_of_term t

fun items_score raw_items = max int_ord (map item_score raw_items)

fun get_score raw_updt =
    case raw_updt of
        Update.AddItems {raw_items, ...} => items_score raw_items
      | Update.AddBoxes {inits, ...} =>
        20 + 5 * Integer.sum (map init_score inits)
      | Update.ResolveBox _ => ~1
      | Update.ShadowItem _ => ~1

fun get_id_score {lat, ...} raw_updt =
    let
      val id = Update.target_of_update raw_updt
    in
      length (BoxID.get_extras_prim lat id) + 1
    end

end  (* structure SCORES. *)

(* Flags specifying output options. *)
val print_intended =
    Attrib.setup_config_bool @{binding "print_intended"} (K false)
val print_term =
    Attrib.setup_config_bool @{binding "print_term"} (K false)
val print_shadow =
    Attrib.setup_config_bool @{binding "print_shadow"} (K false)

(* Proof status. Manages changes to proof status, and main loop
   carrying out proof steps and adding new proof steps to the queue.
 *)
signature PROOFSTATUS =
sig
  val reserved_prfstep_names: string list
  val check_hyps: box_id -> raw_item -> status -> unit
  val is_rtype_resolved: status -> rewrite_type -> bool
  val discharge_assums: status -> box_id -> thm -> thm
  val reduce_raw_item: status -> box_id -> raw_item -> raw_item
  val reduce_raw_updt: status -> Update.raw_update -> Update.raw_update
  val scoring: proofstep -> int -> box_item list -> rewrite_type -> status ->
               (box_item -> Update.raw_update list) -> Update.update list
  val apply_callback:
      box_id * thm -> int -> Update.resolve_callback list -> status -> status
  val process_shadow: Update.update -> status -> status
  val process_resolve: Update.update -> status -> status
  val apply_update_instant: Update.update -> status -> status
  val process_fact_prfsteps:
      int -> rewrite_type -> box_item list -> status -> status
  val process_fact_rewrite: box_item -> status -> status
  val process_fact_all: box_item -> status -> status
  val process_add_items: Update.update -> status -> status
  val process_add_boxes: Update.update -> bool -> status -> status
  val apply_update: Update.update -> status -> status
  val init_status: Proof.context -> term -> status
  val step_until: (status -> bool) -> int * status -> int * status
  val solve_focus: int * status -> int * status
  val run_script: script -> int * status -> int * status
  val solve_root: int -> scripts * status -> thm * status
end;

structure ProofStatus : PROOFSTATUS =
struct

open Status
open Script

val reserved_prfstep_names =
    ["TERM", "RESOLVE", "INIT_BOX", "INIT", "SCRIPT", "CALLBACK"]

fun check_hyps id ritem (st as {ctxt, ...}) =
    let
      val th = get_thm_raw ritem
      val hyps = Thm.hyps_of th
      val inits = get_all_init_assums st id
      val handlers = map fst (get_all_handlers st id)
      val extra = subtract (op aconv) (inits @ handlers) hyps
    in
      if length extra = 0 then ()
      else raise AUTO2CT ("illegal hyp", map (cert ctxt) extra)
    end

fun is_rtype_resolved {lat, ...} rtype =
    case rtype of
        RewriteTable.SINGLE _ => false
      | RewriteTable.LAST (_, id) => BoxID.is_box_resolved lat id

(* Given a theorem th in disjunction form (in the general sense),
   reduce the disjunction using facts available in the state. This
   includes in particular discharging assumptions in implications,
   reducing A --> B to B if A is available in the state. Currently we
   only discharge the first several assumptions.
 *)
fun discharge_assums st id th =
    if not (is_Trueprop (Thm.prop_of th)) then th else
    case prop_of' th of
        Const ("HOL.implies", _) $ A $ _ =>
        (case find_fact st id (HOLogic.mk_Trueprop A) of
             NONE => th
           | SOME ({prop = th1, ...}, eq_th) =>
             let
               val th1' = Thm.equal_elim eq_th th1
             in
               discharge_assums st id ([th, th1'] MRS @{thm mp})
             end)
      | Const ("HOL.disj", _) $ A $ _ =>
        (case find_fact st id (HOLogic.mk_Trueprop (get_neg A)) of
             NONE => th
           | SOME ({prop = th1, ...}, eq_th) =>
             let
               val th1' = Thm.equal_elim eq_th th1
               val th' =
                   if is_neg A then [th, th1'] MRS @{thm Meson.make_neg_rule'}
                   else [th, th1'] MRS @{thm Meson.make_pos_rule'}
             in
               discharge_assums st id th'
             end)
      | Const ("HOL.Not", _) $ (Const ("HOL.conj", _) $ A $ _) =>
        (case find_fact st id (HOLogic.mk_Trueprop A) of
             NONE => th
           | SOME ({prop = th1, ...}, eq_th) =>
             let
               val th1' = Thm.equal_elim eq_th th1
             in
               discharge_assums
                   st id ([th, th1'] MRS @{thm discharge_conj_goal})
             end)
      | _ => th

(* Reductions that do not make the item redundant or contradictory. To
   be used in process_add_items.
 *)
fun reduce_raw_item st id raw_item =
    case raw_item of
        Fact ("PROP", _, th) => Update.thm_to_ritem (discharge_assums st id th)
      | _ => raw_item

(* Further reductions, to be used in scoring. *)
fun reduce_raw_item' (st as {tbl, ...}) id raw_item =
    let
      val raw_item' = reduce_raw_item st id raw_item
    in
      case raw_item' of
          Fact ("PROP", _, th) =>
          (if not (is_Trueprop (Thm.prop_of th)) then [raw_item']
           else let
             val (_, concl) = strip_obj_imp (prop_of' th)
           in
             if is_eq_term concl andalso
                RewriteTable.is_equiv id tbl (HOLogic.dest_eq concl) then []
             else [raw_item']
           end)
        | Fact ("EQ", tname, _) =>
          (if RewriteTable.is_equiv id tbl (HOLogic.dest_prod tname) then []
           else [raw_item'])
        | _ => [raw_item']
    end

fun reduce_raw_updt st raw_updt =
    case raw_updt of
        Update.AddItems {id, raw_items} =>
        Update.AddItems {
          id = id, raw_items = maps (reduce_raw_item' st id) raw_items}
      | _ => raw_updt

(* Perform preliminary checks before matching the last item of a
   proofstep, and process the resulting updates.
 *)
fun scoring {name, ...} sc items rtype (st as {ctxt, ...}) func =
    let
      val {lat, ...} = RewriteTable.table_of_rtype rtype
      val merged_id = merged_id lat items
    in
      if is_box_resolved st merged_id orelse
         is_rtype_resolved st rtype orelse
         exists (query_shadowed st merged_id) items then []
      else
        let
          val scs = map score_of_item items
          val max_sc = fold (curry Int.max) scs sc
          val raw_updts = func (List.last items)
          fun process_raw_updt raw_updt =
              let
                val id = Update.target_of_update raw_updt
              in
                (* Perform resolved and shadowed tests again since id
                   may be descendent of merged_id.
                 *)
                if is_box_resolved st id then []
                else if exists (query_shadowed st id) items then []
                else let
                  val raw_updt' = reduce_raw_updt st raw_updt
                in
                  case raw_updt' of
                      Update.AddItems {raw_items = [], ...} => []
                    | _ =>
                      let
                        val add_sc =
                            case get_fixed_sc ctxt name of
                                NONE => Scores.get_score raw_updt' *
                                        Scores.get_id_score st raw_updt'
                              | SOME v => v
                      in
                        [{sc = add_sc + max_sc, prfstep_name = name,
                          source = items, raw_updt = raw_updt'}]
                      end
                end
              end
        in
          maps process_raw_updt raw_updts
        end
    end

fun process_shadow (updt as {raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.ShadowItem {id = shadow_id, item} =>
        let
          val _ = if not (Config.get ctxt print_shadow) then ()
                  else if get_ty_str item = TY_TERM andalso
                          not (Config.get ctxt print_term) then ()
                  else tracing ("Shadowing " ^ string_of_item ctxt item ^
                                " at box " ^ string_of_box_id shadow_id ^
                                " (" ^ Update.source_info updt ^ ")")
        in
          st |> add_shadowed (shadow_id, item)
        end
      | _ => raise AUTO2 "process_shadow: wrong type of update"

fun apply_callback (id, th) sc cbs st =
    let
      fun eval_cb cb = cb (id, th)
      fun form_cb_updts raw_updt =
          {sc = sc, prfstep_name = "CALLBACK", source = [], raw_updt = raw_updt}
      val cb_updts = map form_cb_updts (maps eval_cb cbs)
    in
      st |> fold apply_update_instant cb_updts
    end

(* When a box, whether primitive or composite, is resolved, perform
   the following two actions: 1. Resolve current and all descendent
   boxes. 2. Add the appropriate fact to each of the immediate parent
   boxes (or invoke callback if available).
 *)
and process_resolve (updt as {sc, raw_updt, ...}) (st as {lat, ...}) =
    case raw_updt of
        Update.ResolveBox {id, th} =>
        let
          val _ = tracing ("Finished box " ^ string_of_box_id id ^
                           " (" ^ Update.source_info updt ^ ")")
          val sc' = (if id = get_focus st then 0 else sc)
          val box = get_box st id
          fun update_one i st =
              let
                val cur_parent = BoxID.get_parent_at_i lat id i
                val ritem = get_on_resolve st id i th
                val _ = check_hyps cur_parent ritem st
                val resolve_updt =
                    {sc = sc', prfstep_name = "RESOLVE", source = [],
                     raw_updt = Update.AddItems
                                    {id = cur_parent, raw_items = [ritem]}}
                (* If id is primitive, invoke any callbacks (with
                   parent id) and add the updates, omitting
                   resolve_updt from output.
                 *)
                val (cbs, st') = if length id > 1 then ([], st) else
                                 (Box.get_callbacks box,
                                  st |> set_resolve_th id (get_thm_raw ritem))
              in
                if length cbs = 0 then
                  st' |> apply_update_instant resolve_updt
                else
                  st' |> apply_callback (cur_parent, get_thm_raw ritem) sc' cbs
              end
        in
          if is_box_resolved st id then st
          else st |> fold update_one (0 upto (length id) - 1)
                  |> add_resolved id
        end
      | _ => raise AUTO2 "process_resolve: wrong type of update"

(* Directly apply Shadow and Resolve updates. Put the remaining
   updates in queue.
*)
and apply_update_instant (updt as {raw_updt, ...}) st =
    let
      val id = Update.target_of_update raw_updt
      val st' = if exist_box st id then st else Status.add_composite_box id st
    in
      if is_box_resolved st id then st else
      case raw_updt of
          Update.ResolveBox _ => st' |> process_resolve updt
        | Update.ShadowItem _ => st' |> process_shadow updt
        |_ => st' |> add_to_queue updt
    end

fun process_step_single sc rtype items (prfstep as {args, func, ...}) st =
    if is_rtype_resolved st rtype then st else
    let
      val arg = the_single (filter_out is_property_match args)
      val tbl = RewriteTable.table_of_rtype rtype
      val items' = filter (ItemIO_Data.pre_match_arg tbl arg) items
      val f = case func of
                  OneStep f => f
                | TwoStep _ =>
                  raise AUTO2 "process_step_single: wrong type of func."

      fun process_one_item item st =
          let
            val updts = scoring prfstep sc [item] rtype st (f rtype st)
          in
            st |> fold apply_update_instant updts
          end
    in
      st |> fold process_one_item items'
    end

fun process_step_pair sc rtype items (prfstep as {args, func, ...}) st =
    if is_rtype_resolved st rtype then st else
    if forall (query_removed st) items then st else
    let
      val items' = maps (get_items st) (get_unresolved st)
      val inters = inter pointer_eq items items'
      val tbl = RewriteTable.table_of_rtype rtype
      val (arg1, arg2) = the_pair (filter_out is_property_match args)
      val pre_match_arg = ItemIO_Data.pre_match_arg
      val f = case func of
                  OneStep _ =>
                  raise AUTO2 "process_step_pair: wrong type of func."
                | TwoStep f => f

      fun process_pairs (left, right) no_int st =
          let
            val (left', right') =
                if length left < length right then
                  let
                    val left' = filter (pre_match_arg tbl arg1) left
                  in
                    if length left' = 0 then ([], [])
                    else (left', filter (pre_match_arg tbl arg2) right)
                  end
                else
                  let
                    val right' = filter (pre_match_arg tbl arg2) right
                  in
                    if length right' = 0 then ([], [])
                    else (filter (pre_match_arg tbl arg1) left, right')
                  end

            (* One step in the iteration, fixing both left and right
               items. Do not match item with itself.
             *)
            fun process_pair left_item func right_item st =
                if pointer_eq (left_item, right_item) then st else
                let
                  val updts =
                      scoring prfstep sc [left_item, right_item] rtype st func
                in
                  st |> fold apply_update_instant updts
                end

            (* Iterate over the right items, fixing left item. *)
            fun loop_right left_item st =
                let
                  (* If no_int holds, do not iterate over the intersection
                     of left and right.
                   *)
                  val right'' =
                      if no_int andalso member pointer_eq inters left_item then
                        subtract pointer_eq inters right'
                      else right'
                  val func = f rtype st left_item
                in
                  st |> fold (process_pair left_item func) right''
                end
          in
            st |> fold loop_right left'
          end
    in
      st |> process_pairs (items, items') false
         |> process_pairs (items', items) true
    end

fun process_prfstep sc rtype items (prfstep as {args, ...}) st =
    if length (filter_out is_property_match args) = 1 then
      st |> process_step_single sc rtype items prfstep
    else
      st |> process_step_pair sc rtype items prfstep

(* Matches given fact with proofsteps, in the context of box with the
   given ID. Given fact should belong either to that box or to an
   ancestor box.
 *)
fun process_fact_prfsteps sc rtype items (st as {ctxt, ...}) =
    st |> fold (process_prfstep sc rtype items) (get_prfsteps ctxt)

(* Process the given rewrite fact, located in the box with the given
   ID. For each fact or conclusion in any of the current, ancestor, or
   descendent boxes, check if it contains a subterm matching the left
   side of the rewrite. If so, re-process that fact or conclusion
   under the modified chain of rewrite tables.
 *)
fun process_fact_rewrite (item as {id, sc, ...}) (st as {tbl, ...}) =
    let
      val eq_th = get_thm item
      val rtype = get_incr_type st id eq_th
      val (lhs, rhs) = HOLogic.dest_prod (get_tname item)
      val updated_trms = RewriteTable.get_reachable_terms true tbl [lhs, rhs]
      fun to_visit_item {tname, ...} = has_subterm updated_trms tname

      val all_ids = get_unresolved st |> filter (
            fn id' => is_box_unresolved st (merge_boxes st (id, id')))
      val items = maps (get_items st) all_ids |> filter to_visit_item
    in
      st |> map_rewrites (RewriteTable.add_rewrite id eq_th)
         |> process_fact_prfsteps sc rtype items
    end

(* Process the new property. Find all properties that are derived as
   the result of the new property. Invoke all relevant proofsteps on
   all relevant terms.
 *)
fun process_property (item as {id, sc, ...}) (st as {tbl, ctxt, ...}) =
    let
      val th = get_thm item
      val rtype = get_incr_type st id th
      val new_properties = (RewriteTable.get_new_properties rtype)
                               |> map (prop_of' o snd)
      val thy = Proof_Context.theory_of ctxt

      (* List of relevant proofsteps. *)
      val new_property_nms = get_property_names new_properties
      val prfsteps =
          (get_prfsteps ctxt)
              |> filter (is_relevant_to_properties thy new_property_nms)

      (* List of relevant items. *)
      val updated_trms = (get_property_args new_properties)
                             |> RewriteTable.get_reachable_terms true tbl
      fun to_visit_item {tname, ...} = has_subterm updated_trms tname

      val all_ids = get_unresolved st |> filter (
            fn id' => is_box_unresolved st (merge_boxes st (id, id')))
      val items = maps (get_items st) all_ids |> filter to_visit_item
    in
      st |> map_rewrites (RewriteTable.add_property (id, th))
         |> fold (process_prfstep sc rtype items) prfsteps
    end

fun process_add_terms (item as {id, sc, tname, ...}) (st as {tbl, ...}) =
    if match_ty_str "TERM" item then st else
    let
      (* Add terms to the rewrite table. *)
      val terms = map (pair id) (HOLogic.strip_tuple tname)
      val tbl' = if has_vars tname then tbl
                 else tbl |> fold RewriteTable.add_term terms

      (* Add new terms as updates. *)
      fun qualify_term t =
          if has_vars t then false
          else case t of Abs _ => false | _ => true

      fun exist_item t =
          length (lookup_item_all st id (TY_TERM, t)) > 0

      val ts = tname |> HOLogic.strip_tuple
                     |> maps (Subterms.get_all_subterms true)
                     |> distinct (op aconv)
                     |> filter qualify_term
                     |> filter_out exist_item

      (* New terms have the same score as the source item. *)
      val updt = {sc = sc, prfstep_name = "TERM", source = [item],
                  raw_updt = Update.AddItems {
                    id = id, raw_items = map term_to_fact ts}}
    in
      st |> add_to_queue updt
         |> map_rewrites (K tbl')
    end

fun process_fact_all item st =
    let
      val st' = st |> process_add_terms item
    in
      if match_ty_str TY_EQ item then
        st' |> process_fact_prfsteps 0 (get_init_type st') [item]
            |> process_fact_rewrite item
      else if match_ty_str TY_PROPERTY item then
        st' |> process_property item
      else
        st' |> process_fact_prfsteps 0 (get_init_type st') [item]
    end

fun is_shadowing_prfstep prfstep_name {ctxt, ...} =
    if is_reserved_name ctxt prfstep_name then false
    else let
      val {priority, ...} = get_prfstep_by_name ctxt prfstep_name
    in
      priority <= PRIORITY_SHADOW
    end

fun process_add_items (updt as {sc, prfstep_name, raw_updt, source, ...})
                      (st as {uid_next, tbl as {ctxt, ...}, ...}) =
    case raw_updt of
        Update.AddItems {id, raw_items = ritems} =>
        if not (is_shadowing_prfstep prfstep_name tbl) andalso
           exists (query_shadowed st id) source then st
        else let
          val (ctxt', subst) = obtain_variant_frees (ctxt, ritems)
          val ritems' = ritems |> map (instantiate subst)
                               |> map (reduce_raw_item st id)
                               |> maps (normalize ctxt')
                               |> distinct eq_ritem
          val (dup_items, items) =
              ritems' |> filter_split (
                (is_triv_eq st id) orf (is_some o (find_ritem_exact st id)))

          val _ = if length dup_items = 0 orelse
                     not (Config.get ctxt print_intended) then () else
                  if prfstep_name = "TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Intend to add " ^
                                Update.update_info ctxt' id dup_items ^
                                " (" ^ Update.source_info updt ^ ")")

          val uid_incr = length (items |> filter_out is_handler_raw)
          val uid_string =
              if uid_incr = 1 then string_of_int uid_next
              else string_of_int uid_next ^ "-" ^
                   string_of_int (uid_next + uid_incr - 1)

          val _ = if length items = 0 then () else
                  if prfstep_name = "TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Add " ^ Update.update_info ctxt' id items ^
                                " (" ^ uid_string ^ ", " ^
                                Update.source_info updt ^ ")")

          fun process_add_one_item ritem st =
              case ritem of
                  Handler (t, handler) => st |> add_handler id (t, handler)
                | Fact _ =>
                  let
                    val item = mk_box_item (uid_next, id, sc, ritem)
                  in
                    st |> add_item item |> incr_uid_next
                       |> process_fact_all item
                  end
        in
          st |> map_context (K ctxt')
             |> fold process_add_one_item items
        end
      | _ => raise AUTO2 "process_add_items: wrong type of update"

fun process_add_boxes (updt as {sc, prfstep_name, raw_updt, source, ...})
                      update_focus (st as {tbl as {ctxt, ...}, ...}) =
    case raw_updt of
        Update.AddBoxes {id, inits, cbs} =>
        if not (is_shadowing_prfstep prfstep_name tbl) andalso
           exists (query_shadowed st id) source then st
        else let
          (* First form the raw items, possibly containing internal
             schematic variables.
           *)
          val vars = maps Update.dest_init_var inits
          val assums = maps Update.dest_init_assum inits
          val ritems = map var_to_fact vars @
                       map (Update.thm_to_ritem o Thm.assume o cert ctxt)
                           assums
          val _ = assert (forall (fn t => fastype_of t = propT) assums)
                         "process_add_boxes: assumption is not of type prop."

          (* Obtain the fresh variables, and replace into both the raw
             items and the initial facts.
           *)
          val (ctxt', subst) = obtain_variant_frees (ctxt, ritems)
          val ritems' = ritems |> map (instantiate subst)
                               |> maps (normalize ctxt')

          val subst_fun = Term.subst_atomic (map (apply2 Thm.term_of) subst)
          fun subst_init init =
              case init of
                  Update.InitVar v => Update.InitVar (subst_fun v)
                | Update.InitAssum assum => Update.InitAssum (subst_fun assum)
          val inits' = map subst_init inits

          (* Find neg_form and check if already present. *)
          val neg_form = Update.get_neg_form ctxt' inits'
          val neg_form_opt = find_fact st id neg_form
        in
          (* Do nothing if there is already a box with the same
             assumptions and conclusions.
           *)
          if is_some (find_prim_box st id inits') then st

          (* If the conclusion already exists, apply callback. *)
          else if is_some neg_form_opt then
            let
              val ({id = id', prop, ...}, eq_th) = the neg_form_opt
              val th' = Thm.equal_elim eq_th prop
            in
              st |> apply_callback (id', th') sc cbs
            end

          (* Otherwise, proceed to create the box. *)
          else let
            val _ = tracing ("Add box under " ^ string_of_box_id id ^ " (" ^
                             Update.source_info updt ^ ")")
            val init_box = (Box.init_box inits')
                               |> fold Box.add_callback cbs
            val (prim_id, st') = add_prim_box id init_box st
            val new_id = [prim_id]
            val _ = tracing (
                  (string_of_box_id new_id) ^ ": " ^
                  (Box.short_string_of_box ctxt' (get_box st' new_id)))

            val item_updt = {
              sc = sc, prfstep_name = "INIT_BOX", source = [],
              raw_updt = Update.AddItems {id = new_id, raw_items = ritems'}}
          in
            st' |> map_context (K ctxt')
                |> update_focus ? set_focus new_id
                |> process_add_items item_updt
          end
        end
      | _ => raise AUTO2 "process_add_boxes: wrong type of update"

fun remove_extra_terms (st as {tbl, ...}) =
    let
      val ts = (RewriteTable.get_all_terms tbl)
                   |> filter_out (is_term_present st)
    in
      st |> map_rewrites (RewriteTable.remove_terms ts)
    end

fun apply_update (updt as {raw_updt, ...}) st =
    let
      val id = Update.target_of_update raw_updt
    in
      if is_box_resolved st id then st else
      st |> not (exist_box st id) ? Status.add_composite_box id
         |> (case raw_updt of
                 Update.AddItems _ => process_add_items updt
               | Update.AddBoxes _ => process_add_boxes updt false
               | Update.ResolveBox _ => process_resolve updt
               | Update.ShadowItem _ => process_shadow updt)
    end

fun init_status ctxt obj_goal =
    let
      val (assums, concl) =
          obj_goal |> HOLogic.dest_Trueprop |> strip_obj_imp
                   |> apfst (map HOLogic.mk_Trueprop)
                   |> apsnd HOLogic.mk_Trueprop
      val vars = map Free (Term.add_frees obj_goal [])
      val inits = map Update.InitVar vars @
                  map Update.InitAssum (assums @ [get_neg' concl])
      val raw_updt = Update.AddBoxes {id = [], inits = inits, cbs = []}
      val updt = {sc = 0, prfstep_name = "INIT", source = [],
                  raw_updt = raw_updt}
    in
      (empty_status ctxt) |> add_composite_box [] |> add_item null_item
                          |> set_focus [0] |> apply_update updt
    end

fun show_current_focus (st as {ctxt, ...}) =
    warning ("Resolving box " ^ (string_of_box_id (get_focus st)) ^ ": " ^
             (Box.short_string_of_box ctxt (get_box st (get_focus st))))

(* Given a condition status -> bool, step until the condition is
   satisfied. Return steps remaining as well as updated status.
 *)
fun step_until cond (steps, (st as {queue, ...})) =
    if cond st then
      (steps, st)
    else if steps = 0 then
      let val _ = show_current_focus st in
        raise AUTO2 "Maximum number of steps reached"
      end
    else let
      val updt = Updates_Heap.min queue
                 handle List.Empty => let val _ = show_current_focus st in
                                        raise AUTO2 "No more moves"
                                      end
      val st' = st |> delmin_from_queue |> apply_update updt
                   |> (if steps mod 10 = 0 then remove_extra_terms else I)
    in
      step_until cond (steps - 1, st')
    end

(* Solve for the ID given by focus id. *)
val solve_focus = step_until (fn st => is_box_resolved st (get_focus st))

(* Run the given script at focus id. Returns the new count of steps
   remaining, and the updated status.
 *)
fun run_script (Script_Task {inits, subs, cb, ...})
               (steps, (st as {ctxt, queue, ...})) =
    let
      fun get_min_score queue =
          #sc (Updates_Heap.min queue) handle List.Empty => 0
      val sc = get_min_score queue
      val id = get_focus st
      val neg_form = Update.get_neg_form ctxt inits

      val (steps', st', th) =
          case find_fact st id neg_form of
              NONE =>
              let
                val updt = {sc = sc, prfstep_name = "SCRIPT", source = [],
                            raw_updt = Update.AddBoxes {
                              id = id, inits = inits,
                              cbs = [Update.null_callback]}}
                val st' = process_add_boxes updt true st
                val id' = the (find_prim_box st' id inits)
                          handle Option.Option =>
                                 raise AUTO2 "run_script: failed to add box."

                (* There are several possibilities: the conclusion of
                   the box is already present in the state, the new
                   box is resolved at the same time as it is created,
                   and finally more steps are needed to resolve the
                   box. In the latter two cases, focus is set to id'
                   during the call to process_add_boxes.
                 *)
                val (steps', st'') =
                    if is_box_resolved st' id' then
                      (steps, st') |> apsnd (set_focus id)
                    else
                      (steps, st') |> fold run_script subs
                                   |> solve_focus
                                   |> apsnd (set_focus id)
              in
                (steps', st'', get_resolve_th st'' id')
              end
            | SOME ({prop, ...}, eq_th) =>
              (steps, st, Thm.equal_elim eq_th prop)
    in
      let
        val raw_updts = cb ((id, th), st')
        val updts = map (fn raw_updt =>
                            {sc = 0, prfstep_name = "SCRIPT", source = [],
                             raw_updt = raw_updt}) raw_updts
      in
        (steps', st' |> fold add_to_queue updts)
      end
    end

fun solve_root steps (scrpts, st) =
    let
      val (steps', st') = (steps, st) |> fold run_script scrpts |> solve_focus
      val _ = writeln (
            "Finished in " ^ (string_of_int (steps - steps')) ^ " steps.")
    in
      (get_resolve_th st' [0], st')
    end

end  (* structure ProofStatus. *)

(* Definition of AUTO2. *)
fun auto2_gen ctxt steps pre_scrpts state =
    let
      val prop = Thm.prop_of state
      val subgoals = prop |> Logic.strip_imp_prems
    in
      if length subgoals = 0 then Seq.empty else
      let
        val subgoal = hd subgoals
        val _ = tracing (
              "Subgoal 1 of " ^ (string_of_int (length subgoals)) ^ ":\n" ^
              (subgoal |> pretty_term ctxt |> str) ^ "\n")
        val to_obj_eq = (cert ctxt subgoal) |> to_obj_conv ctxt
        val obj_goal = rhs_of to_obj_eq
        val scrpts = pre_scrpts ctxt
        val ctxt' = ctxt |> fold declare_free_term (get_all_vars scrpts)
        val st = ProofStatus.init_status ctxt' obj_goal
        val (obj_th, _) =
            timer ("Total time: ",
                   fn _ => ProofStatus.solve_root steps (scrpts, st))
        val th = Thm.equal_elim (meta_sym to_obj_eq) obj_th
      in
        Seq.single (Thm.implies_elim state th)
      end
    end

fun auto2_tac ctxt = PRIMSEQ (auto2_gen ctxt 2000 no_script)
fun auto2l_tac ctxt steps = PRIMSEQ (auto2_gen ctxt steps no_script)
fun auto2s_tac ctxt pre_scrpts = PRIMSEQ (auto2_gen ctxt 2000 pre_scrpts)
fun auto2ls_tac ctxt steps pre_scrpts =
    PRIMSEQ (auto2_gen ctxt steps pre_scrpts)

val _ = Theory.setup (fold add_reserved_name ProofStatus.reserved_prfstep_names)
