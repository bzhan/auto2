(* Main file defining inference algorithm and tactic. *)

signature SCORES =
sig
  val item_score: raw_item -> int
  val items_score: raw_item list -> int
  val get_score: raw_update -> int
  val get_id_score: status -> raw_update -> int
end;

functor Scores(Base:UTIL_BASE) : SCORES =
struct

structure Box = Box(Base)

fun item_score ritem =
    case ritem of
        Handler _ => 0
      | Fact (ty_str, tname, _) =>
        if ty_str = TY_VAR then 10  (* cost of introducing a variable. *)
        else Integer.sum (map size_of_term tname)

fun init_score init =
    case init of
        InitVar _ => 0
      | InitAssum t => size_of_term t

fun items_score raw_items = max int_ord (map item_score raw_items)

fun get_score raw_updt =
    case raw_updt of
        AddItems {raw_items, sc, ...} =>
        (case sc of NONE => items_score raw_items | SOME n => n)
      | AddBoxes {inits, sc, ...} =>
        (case sc of NONE => 20 + 5 * Integer.sum (map init_score inits)
                  | SOME n => n)
      | ResolveBox _ => ~1
      | ShadowItem _ => ~1

fun get_id_score {lat, ...} raw_updt =
    let
      val id = target_of_update raw_updt
    in
      length (BoxID.get_ancestors_prim lat id) + 1
    end

end  (* structure SCORES. *)

(* Flags specifying output options. *)
val print_trace =
    Attrib.setup_config_bool @{binding "print_trace"} (K true)
val print_intended =
    Attrib.setup_config_bool @{binding "print_intended"} (K false)
val print_term =
    Attrib.setup_config_bool @{binding "print_term"} (K false)
val print_shadow =
    Attrib.setup_config_bool @{binding "print_shadow"} (K false)
val print_score =
    Attrib.setup_config_bool @{binding "print_score"} (K false)

(* Flag specifying the maximum number of steps. *)
val max_steps =
    Attrib.setup_config_int @{binding "max_steps"} (K 2000)

(* Proof status. Manages changes to proof status, and main loop
   carrying out proof steps and adding new proof steps to the queue.
 *)
signature PROOFSTATUS =
sig
  val check_hyps: box_id -> thm -> status -> unit
  val is_rtype_resolved: status -> rewrite_type -> bool
  val scoring: proofstep -> int -> box_item list -> rewrite_type -> status ->
               (box_item -> raw_update list) -> update list
  val process_shadow: update -> status -> status
  val process_resolve: update -> status -> status
  val apply_update_instant: update -> status -> status
  val process_fact_all: box_item list -> status -> status
  val process_add_items: update -> status -> status
  val process_add_boxes: update -> status -> status
  val apply_update: update -> status -> status
  val init_status: Proof.context -> term -> status
  val step_until: (status -> bool) -> int * status -> int * status
  val solve_root: int * status -> int * status
end;

functor ProofStatus(Base:UTIL_BASE) : PROOFSTATUS =
struct

structure UtilLogic = UtilLogic(Base)
structure Subterms = Subterms(Base)
structure RewriteTable = RewriteTable(Base)
structure BoxItem = BoxItem(Base)
structure ItemIO = ItemIO(Base)
structure Update = Update(Base)
structure Box = Box(Base)
structure Status = Status(Base)
structure Normalizer = Normalizer(Base)
structure ProofStep_Data = ProofStep_Data(Base)
structure Scores = Scores(Base)
structure Logic_ProofSteps = Logic_ProofSteps(Base)
open Base
open UtilLogic
open BoxItem
open ItemIO
open Status

fun check_hyps id th (st as {ctxt, ...}) =
    let
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
        SINGLE _ => false
      | LAST (_, id, _) => BoxID.is_box_resolved lat id

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
          val scs = map #sc items
          val max_sc = fold (curry Int.max) scs sc
          val raw_updts = func (List.last items)
          fun process_raw_updt raw_updt =
              let
                val id = target_of_update raw_updt
              in
                (* Perform resolved and shadowed tests again since id
                   may be descendent of merged_id.
                 *)
                if is_box_resolved st id then []
                else if exists (query_shadowed st id) items then []
                else
                  let
                    val add_sc =
                        case ProofStep_Data.get_fixed_sc ctxt name of
                            NONE => Scores.get_score raw_updt *
                                    Scores.get_id_score st raw_updt
                          | SOME v => v
                  in
                    [{sc = add_sc + max_sc, prfstep_name = name,
                      source = items, raw_updt = raw_updt}]
                  end
              end
        in
          maps process_raw_updt raw_updts
        end
    end

fun process_shadow (updt as {raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        ShadowItem {id = shadow_id, item as {ty_str, ...}} =>
        let
          val _ = if not (Config.get ctxt print_trace) orelse
                     not (Config.get ctxt print_shadow) then ()
                  else if ty_str = TY_TERM andalso
                          not (Config.get ctxt print_term) then ()
                  else tracing ("Shadowing " ^ string_of_item ctxt item ^
                                " at box " ^ string_of_box_id shadow_id ^
                                " (" ^ Update.source_info updt ^ ")")
        in
          st |> add_shadowed (shadow_id, item)
        end
      | _ => raise AUTO2 "process_shadow: wrong type of update"

(* When a box, whether primitive or composite, is resolved, perform
   the following two actions: 1. Resolve current and all descendent
   boxes. 2. Add the appropriate fact to each of the immediate parent
   boxes.
 *)
and process_resolve (updt as {sc, raw_updt, ...}) (st as {lat, ctxt, ...}) =
    case raw_updt of
        ResolveBox {id, th} =>
        let
          val _ = if Config.get ctxt print_trace then
                    tracing ("Finished box " ^ string_of_box_id id ^
                             " (" ^ Update.source_info updt ^ ")")
                  else ()

          fun update_one i st =
              let
                val cur_parent = BoxID.get_parent_at_i lat id i
                val res_th = get_on_resolve st id i th
                val _ = check_hyps cur_parent res_th st

                val res_obj_th = apply_to_thm (to_obj_conv ctxt) res_th
                val updt = {sc = sc, prfstep_name = "$RESOLVE", source = [],
                            raw_updt = Logic_ProofSteps.logic_thm_update
                                           ctxt (cur_parent, res_obj_th)}
              in
                st |> set_resolve_th id res_th
                   |> apply_update_instant updt
              end
        in
          if is_box_resolved st id then st
          else if id = [0] then
            st |> set_resolve_th id (get_on_resolve st id 0 th)
               |> add_resolved id
          else
            st |> fold update_one (0 upto (length id) - 1)
               |> add_resolved id
        end
      | _ => raise AUTO2 "process_resolve: wrong type of update"

(* Directly apply Shadow and Resolve updates. Put the remaining
   updates in queue.
*)
and apply_update_instant (updt as {raw_updt, ...}) st =
    let
      val id = target_of_update raw_updt
      val st' = if exist_box st id then st else Status.add_composite_box id st
    in
      if is_box_resolved st id then st else
      case raw_updt of
          ResolveBox _ => st' |> process_resolve updt
        | ShadowItem _ => st' |> process_shadow updt
        | _ => st' |> add_to_queue updt
    end

fun process_step_single sc rtype items (prfstep as {args, func, ...}) st =
    if is_rtype_resolved st rtype then st else
    let
      val arg = the_single (filter_out is_side_match args)
      val tbl = RewriteTable.table_of_rtype rtype
      val items' = filter (pre_match_arg tbl arg) items
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

fun process_step_pair sc rtype items items' (prfstep as {args, func, ...}) st =
    let
      val tbl = RewriteTable.table_of_rtype rtype
      val (arg1, arg2) = the_pair (filter_out is_side_match args)
      val f = case func of
                  TwoStep f => f
                | _ => raise AUTO2 "process_step_pair: wrong type of func."

      (* Filter the two lists of items using pre_match_arg. *)
      fun filter_pairs (left, right) =
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

      fun process_pairs (left, right) st =
          let
            val (left', right') = filter_pairs (left, right)

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
                  val func = f rtype st left_item
                in
                  st |> fold (process_pair left_item func) right'
                end
          in
            st |> fold loop_right left'
          end
    in
      (* We know items is a subset of items'. On the second round,
         match with the extra elements in items' on the left.
       *)
      st |> process_pairs (items, items')
         |> process_pairs (subtract pointer_eq items items', items)
    end

fun process_prfstep sc rtype items items' (prfstep as {args, ...}) st =
    let
      val items = filter_out (fn item => is_box_resolved st (#id item) orelse
                                         query_removed st item) items
    in
      if length items = 0 then st
      else if is_rtype_resolved st rtype then st
      else if length (filter_out is_side_match args) = 1 then
        st |> process_step_single sc rtype items prfstep
      else
        st |> process_step_pair sc rtype items items' prfstep
    end

fun process_add_terms item (st as {tbl, ctxt, ...}) =
    let
      (* Add terms to the rewrite table. *)
      val {id, sc, ty_str, tname, ...} = item
      val ts = map Thm.term_of tname

      fun qualify_term t =
          case t of Abs _ => false | _ => not (has_vars t)

      val rewr_terms = rewr_terms_of_item ctxt (ty_str, ts)
      val terms = rewr_terms |> map (cert ctxt)
                             |> maps Subterms.get_all_subterms
                             |> map Thm.term_of
                             |> distinct (op aconv)
                             |> filter qualify_term
      val headt = if ty_str = TY_PROP then
                    if is_neg (the_single ts) then
                      [dest_not (the_single ts)]
                    else ts
                  else []
      val tbl' =
          tbl |> fold RewriteTable.add_term
              (map (pair id o cert ctxt) (headt @ terms))

      val new_ts = map (Thm.term_of o snd)
                       (RewriteTable.get_new_terms (tbl, tbl'))
      val all_items = (maps (get_items false st) (get_unresolved st))
                          |> remove pointer_eq item
      val infos = map (fn {id, prop, ...} => (id, prop)) all_items
      val tbl'' =
          tbl' |> RewriteTable.complete_wellform_data_for_terms infos new_ts

      (* Add new terms as updates. *)
      fun exists_item t =
          find_ritem_exact st id (Fact (TY_TERM, [t], true_th))

      val terms2 = rewr_terms |> map (cert ctxt)
                              |> maps Subterms.get_all_subterms_skip_if
                              |> map Thm.term_of
                              |> distinct (op aconv)
                              |> filter qualify_term
                              |> filter_out exists_item

      (* New terms have the same score as the source item. *)
      val updt =
          {sc = sc, prfstep_name = "$TERM", source = [item],
           raw_updt = AddItems {id = id, sc = NONE,
                                raw_items = map term_to_fact terms2}}
    in
      st |> (if length terms2 > 0 then add_to_queue updt else I)
         |> map_rewrites (K tbl'')
    end

(* Process the given item. This has two parts: first, if the item is
   added to a box, process that fact with initial rtype. Second, if
   the rewrite table is changed (due to either EQ, PROPERTY, or
   WELLFORM), process relevant items with incremental rtype.
 *)
fun process_fact_all items st =
    if length items = 0 then st else
    let
      val {tbl, ctxt, ...} = st
      val id = #id (hd items)
      val sc = #sc (hd items)

      (* Obtain initial and incremental rtype, and the list of
         relevant terms for that increment.
       *)
      val items' = maps (get_items false st) (get_unresolved st)
      val infos = (subtract pointer_eq items items')
                      |> map (fn {id, prop, ...} => (id, prop))
                      |> filter (is_Trueprop o Thm.prop_of o snd)
      val props = items |> filter (match_ty_strs [TY_PROP, TY_EQ, TY_PROPERTY])
                        |> map #prop
      val tbl' = RewriteTable.add_infos infos (id, props) tbl
      val init_type = SINGLE tbl'
      val incr_type = RewriteTable.get_incr_type tbl infos (id, props)
      val ts = case incr_type of
                   LAST (_, _, ts) => map Thm.term_of ts
                 | _ => raise AUTO2 "process_fact_all"

      (* List of items to consider for init and incr rounds. *)
      val init_items = filter_out (match_ty_str TY_PROPERTY) items

      val incr_ids = get_unresolved st |> filter (
            fn id' => is_box_unresolved st (merge_boxes st (id, id')))
      val incr_items =
          if length ts = 0 then []
          else (maps (get_items false st) incr_ids)
                   |> subtract pointer_eq items
                   |> filter (fn {tname, ...} =>
                                 exists (has_subterm ts)
                                        (map Thm.term_of tname))
                   |> cons null_item

      (* List of proofsteps to consider for init and incr rounds. *)
      val prfsteps = ProofStep_Data.get_prfsteps ctxt
    in
      st |> map_rewrites (K tbl')
         |> fold (process_prfstep sc init_type init_items items') prfsteps
         |> fold (process_prfstep sc incr_type incr_items items') prfsteps
    end

fun is_shadowing_prfstep prfstep_name {ctxt, ...} =
    if is_prefix_str "$" prfstep_name then false
    else let
      val {priority, ...} = ProofStep_Data.get_prfstep_by_name ctxt prfstep_name
    in
      priority <= PRIORITY_SHADOW
    end

fun process_add_items (updt as {sc, prfstep_name, raw_updt, source, ...})
                      (st as {uid_next, tbl as {ctxt, ...}, ...}) =
    case raw_updt of
        AddItems {id, raw_items = ritems, ...} =>
        if not (is_shadowing_prfstep prfstep_name tbl) andalso
           exists (query_shadowed st id) source then st
        else let
          val (ctxt', subst) = obtain_variant_frees (ctxt, ritems)
          val ritems' =
              ritems |> map (instantiate subst)
                     |> (if is_prefix_str "$" prfstep_name then
                           maps (Normalizer.normalize_keep ctxt')
                         else
                           maps (Normalizer.normalize ctxt'))
                     |> distinct eq_ritem
          val (dup_ritems, new_ritems) =
              if prfstep_name = "$SCRIPT" orelse sc = 0 then ([], ritems')
              else find_ritems_exact st id ritems'

          val _ = if length dup_ritems = 0 orelse
                     not (Config.get ctxt print_trace) orelse
                     not (Config.get ctxt print_intended) then () else
                  if prfstep_name = "$TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Intend to add " ^
                                Update.update_info ctxt' id dup_ritems ^
                                " (" ^ Update.source_info updt ^ ")")

          val (handlers, ritems') = filter_split is_handler_raw new_ritems

          val uid_incr = length ritems'
          val uid_string = if uid_incr = 1 then string_of_int uid_next
                           else string_of_int uid_next ^ "-" ^
                                string_of_int (uid_next + uid_incr - 1)
          val sc_string = if Config.get ctxt print_score then
                            (string_of_int sc) ^ ", "
                          else ""

          val _ = if length new_ritems = 0 orelse
                     not (Config.get ctxt print_trace) then () else
                  if prfstep_name = "$TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Add " ^ Update.update_info ctxt' id ritems' ^
                                " (" ^ uid_string ^ ", " ^ sc_string ^
                                Update.source_info updt ^ ")")

          (* Produce the actual items. *)
          val items =
              map (fn i => mk_box_item
                               ctxt' (uid_next + i, id, sc, nth ritems' i))
                  (0 upto (length ritems' - 1))
        in
          st |> map_context (K ctxt')
             |> fold (add_handler id) (map dest_handler_raw handlers)
             |> fold process_add_terms items
             |> fold add_item items
             |> process_fact_all items
             |> incr_uid (length ritems')
        end
      | _ => raise AUTO2 "process_add_items: wrong type of update"

fun process_add_boxes (updt as {sc, prfstep_name, raw_updt, source, ...})
                      (st as {tbl as {ctxt, ...}, ...}) =
    case raw_updt of
        AddBoxes {id, inits, ...} =>
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
                               |> maps (Normalizer.normalize_keep ctxt')

          val subst_fun = Term.subst_atomic (map (apply2 Thm.term_of) subst)
          fun subst_init init =
              case init of
                  InitVar v => InitVar (subst_fun v)
                | InitAssum assum => InitAssum (subst_fun assum)
          val inits' = map subst_init inits

          (* Find neg_form and check if already present. *)
          val neg_form_opt = find_neg_form st id inits'

          val prev_prim_box = find_prim_box st id inits'
        in
          (* Do nothing if there is already a box with the same
             assumptions and conclusions.
           *)
          if is_some prev_prim_box then st
          else if is_some neg_form_opt then st

          (* Otherwise, proceed to create the box. *)
          else let
            val _ = if Config.get ctxt print_trace then
                      tracing ("Add box under " ^ string_of_box_id id ^ " (" ^
                               Update.source_info updt ^ ")")
                    else ()
            val init_box = Box.init_box inits'
            val (prim_id, st') = add_prim_box id init_box st
            val new_id = [prim_id]
            val _ = if Config.get ctxt print_trace then
                      tracing (
                        (string_of_box_id new_id) ^ ": " ^
                        (Box.short_string_of_box ctxt' (get_box st' new_id)))
                    else ()

            val item_updt = {
              sc = sc, prfstep_name = "$INIT_BOX", source = [],
              raw_updt = AddItems {id = new_id, sc = NONE, raw_items = ritems'}}
          in
            st' |> map_context (K ctxt')
                |> process_add_items item_updt
          end
        end
      | _ => raise AUTO2 "process_add_boxes: wrong type of update"

fun apply_update (updt as {raw_updt, ...}) st =
    let
      val id = target_of_update raw_updt
    in
      if is_box_resolved st id then st else
      st |> not (exist_box st id) ? Status.add_composite_box id
         |> (case raw_updt of
                 AddItems _ => process_add_items updt
               | AddBoxes _ => process_add_boxes updt
               | ResolveBox _ => process_resolve updt
               | ShadowItem _ => process_shadow updt)
    end

(* Initialize status, given the subgoal in pure logic form. *)
fun init_status ctxt subgoal =
    let
      (* Free variables are implicitly quantified over at the front. *)
      val vars = map Free (Term.add_frees subgoal [])

      val (assums, concl) = strip_pure_goal ctxt subgoal
      val assum_inits =
          map (fn (is_var, t) => if is_var then InitVar t else InitAssum t)
              assums
      val new_vars =
          maps (fn init => case init of InitVar t => [t] | _ => [])
               assum_inits
      val inits = map InitVar vars @ assum_inits @ [InitAssum (get_neg' concl)]
      val raw_updt = AddBoxes {id = [], sc = NONE, inits = inits}
      val updt = {sc = 0, prfstep_name = "$INIT", source = [],
                  raw_updt = raw_updt}
    in
      ctxt |> fold declare_free_term new_vars
           |> empty_status
           |> add_composite_box [] |> add_item null_item
           |> apply_update updt
    end

(* Given a condition status -> bool, step until the condition is
   satisfied. Return steps remaining as well as updated status.
 *)
fun step_until cond (steps, (st as {queue, ...})) =
    if cond st then
      (steps, st)
    else if steps = 0 then
      raise AUTO2 "Maximum number of steps reached"
    else let
      val updt = Updates_Heap.min queue
                 handle List.Empty => raise AUTO2 "No more moves"
      val st' = st |> delmin_from_queue |> apply_update updt
    in
      step_until cond (steps - 1, st')
    end

val solve_root = step_until (fn st => is_box_resolved st [0])

end  (* structure ProofStatus. *)

(* Definition of AUTO2. *)

signature AUTO2 =
sig
  val auto2_tac: Proof.context -> tactic
end

functor Auto2(Base:UTIL_BASE) : AUTO2 =
struct

structure UtilLogic = UtilLogic(Base)
structure Status = Status(Base)
structure ProofStatus = ProofStatus(Base)
open UtilLogic

fun auto2_tac ctxt state =
    let
      val prop = Thm.prop_of state
      val subgoals = prop |> Logic.strip_imp_prems
      val steps = Config.get ctxt max_steps
    in
      if length subgoals = 0 then Seq.empty else
      let
        val subgoal = hd subgoals
        val _ = tracing (
              "Subgoal 1 of " ^ (string_of_int (length subgoals)) ^ ":\n" ^
              (subgoal |> pretty_term ctxt |> str) ^ "\n")
        val subgoal_eq = subgoal |> cert ctxt |> to_obj_conv_on_horn ctxt
        val st = ProofStatus.init_status ctxt (rhs_of subgoal_eq)
        val (_, st') =
            timer ("Total time: ",
                   fn _ => ProofStatus.solve_root (steps, st))
        val th = Status.get_resolve_th st' [0]
        val vars = map Free (Term.add_frees subgoal [])
        val th' = th |> fold Thm.forall_elim (map (cert ctxt) vars)
                     |> Thm.equal_elim (meta_sym subgoal_eq)
      in
        Seq.single (Thm.implies_elim state th')
      end
    end

end  (* structure Auto2 *)
