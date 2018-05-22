(* Main file defining inference algorithm and tactic. *)

signature SCORES =
sig
  val item_score: raw_item -> int
  val items_score: raw_item list -> int
  val get_score: raw_update -> int
end;

structure Scores : SCORES =
struct

fun item_score ritem =
    case ritem of
        Handler _ => 0
      | Fact (ty_str, tname, _) =>
        if ty_str = TY_VAR then 10  (* cost of introducing a variable. *)
        else Integer.sum (map size_of_term tname)

fun items_score raw_items = Util.max int_ord (map item_score raw_items)

fun get_score raw_updt =
    case raw_updt of
        AddItems {raw_items, sc, ...} =>
        (case sc of NONE => items_score raw_items | SOME n => n)
      | AddBoxes {init_assum, sc, ...} =>
        (case sc of NONE => 20 + 5 * size_of_term init_assum
                  | SOME n => n)
      | ResolveBox _ => ~1
      | ShadowItem _ => ~1

end  (* structure SCORES. *)

(* Flags specifying output options. *)
val print_trace =
    Attrib.setup_config_bool @{binding "print_trace"} (K false)
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
  val scoring: proofstep -> int -> box_item list -> status ->
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

structure ProofStatus : PROOFSTATUS =
struct

fun check_hyps id th (st as {ctxt, ...}) =
    let
      val hyps = Thm.hyps_of th
      val inits = Status.get_all_init_assums st id
      val handlers = map (fn (_, t, _) => t) (Status.get_all_handlers st id)
      val extra = subtract (op aconv) (inits @ handlers) hyps
    in
      if null extra then ()
      else let
        val _ = trace_tlist ctxt "extra:" extra
      in
        raise Fail "illegal hyp"
      end
    end

(* Perform preliminary checks before matching the last item of a
   proofstep, and process the resulting updates.
 *)
fun scoring {name, ...} sc items (st as {ctxt, ...}) func =
    let
      val merged_id = BoxItem.merged_id ctxt items
    in
      if BoxID.is_box_resolved ctxt merged_id orelse
         exists (Status.query_shadowed st merged_id) items then []
      else
        let
          val scs = map #sc items
          val max_sc = fold (curry Int.max) scs sc
          val raw_updts = func (List.last items)
          fun process_raw_updt raw_updt =
              let
                val id = Update.target_of_update raw_updt
              in
                (* Perform resolved and shadowed tests again since id
                   may be descendent of merged_id.
                 *)
                if BoxID.is_box_resolved ctxt id then []
                else if exists (Status.query_shadowed st id) items then []
                else
                  let
                    val thy = Proof_Context.theory_of ctxt
                    val add_sc =
                        case ProofStepData.get_fixed_sc thy name of
                            NONE => Scores.get_score raw_updt
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
                  else tracing ("Shadowing " ^
                                ItemIO.string_of_item ctxt item ^
                                " at box " ^ BoxID.string_of_box_id shadow_id ^
                                " (" ^ Update.source_info updt ^ ")")
        in
          st |> Status.add_shadowed (shadow_id, item)
        end
      | _ => raise Fail "process_shadow: wrong type of update"

(* When a box, whether primitive or composite, is resolved, perform
   the following two actions: 1. Resolve current and all descendent
   boxes. 2. Add the appropriate fact to each of the immediate parent
   boxes.
 *)
and process_resolve (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        ResolveBox {id, th} =>
        let
          val _ = if Config.get ctxt print_trace then
                    tracing ("Finished box " ^ BoxID.string_of_box_id id ^
                             " (" ^ Update.source_info updt ^ ")")
                  else ()

          fun update_one i st =
              let
                val cur_parent = BoxID.get_parent_at_i ctxt id i
                val res_th = Status.get_on_resolve st id i th
                val _ = check_hyps cur_parent res_th st

                val res_obj_th = apply_to_thm (UtilLogic.to_obj_conv ctxt) res_th
                val updt = {sc = sc, prfstep_name = "$RESOLVE", source = [],
                            raw_updt = Logic_ProofSteps.logic_thm_update
                                           ctxt (cur_parent, res_obj_th)}
              in
                st |> apply_update_instant updt
              end
        in
          if BoxID.is_box_resolved ctxt id then st
          else if id = [0] then
            st |> Status.set_resolve_th (Status.get_on_resolve st id 0 th)
               |> Status.add_resolved id
          else
            st |> fold update_one (0 upto (length id) - 1)
               |> Status.add_resolved id
        end
      | _ => raise Fail "process_resolve: wrong type of update"

(* Directly apply Shadow and Resolve updates. Put the remaining
   updates in queue.
*)
and apply_update_instant (updt as {raw_updt, ...}) (st as {ctxt, ...})=
    let
      val id = Update.target_of_update raw_updt
      val st' = if Status.exist_box st id then st
                else Status.add_composite_box id st
    in
      if BoxID.is_box_resolved ctxt id then st else
      case raw_updt of
          ResolveBox _ => st' |> process_resolve updt
        | ShadowItem _ => st' |> process_shadow updt
        | _ => st' |> Status.add_to_queue updt
    end

fun process_step_single sc ictxt items (prfstep as {args, func, ...}) st =
    let
      val arg = the_single (filter_out ItemIO.is_side_match args)
      val ctxt = IncrContext.context_of ictxt
      val items' = filter (ItemIO.pre_match_arg ctxt arg) items
      val f = case func of
                  OneStep f => f
                | TwoStep _ =>
                  raise Fail "process_step_single: wrong type of func."

      fun process_one_item item st =
          let
            val updts = scoring prfstep sc [item] st (f ictxt)
          in
            st |> fold apply_update_instant updts
          end
    in
      st |> fold process_one_item items'
    end

fun process_step_pair sc ictxt items items' (prfstep as {args, func, ...}) st =
    let
      val ctxt = IncrContext.context_of ictxt
      val (arg1, arg2) = the_pair (filter_out ItemIO.is_side_match args)
      val f = case func of
                  TwoStep f => f
                | _ => raise Fail "process_step_pair: wrong type of func."

      (* Filter the two lists of items using pre_match_arg. *)
      fun filter_pairs (left, right) =
          if length left < length right then
            let
              val left' = filter (ItemIO.pre_match_arg ctxt arg1) left
            in
              if null left' then ([], [])
              else (left', filter (ItemIO.pre_match_arg ctxt arg2) right)
            end
          else
            let
              val right' = filter (ItemIO.pre_match_arg ctxt arg2) right
            in
              if null right' then ([], [])
              else (filter (ItemIO.pre_match_arg ctxt arg1) left, right')
            end

      fun process_pairs (left, right) st =
          let
            val (left', right') = filter_pairs (left, right)

            (* One step in the iteration, fixing both left and right
               items. Do not match item with itself.
             *)
            fun process_pair left_item func right_item st =
                if BoxItem.eq_item (left_item, right_item) then st else
                let
                  val updts =
                      scoring prfstep sc [left_item, right_item] st func
                in
                  st |> fold apply_update_instant updts
                end

            (* Iterate over the right items, fixing left item. *)
            fun loop_right left_item st =
                let
                  val func = f ictxt left_item
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
         |> process_pairs (subtract BoxItem.eq_item items items', items)
    end

fun process_prfstep sc ictxt items items' (prfstep as {args, ...}) (st as {ctxt, ...}) =
    let
      val items = filter_out (
          fn item => BoxID.is_box_resolved ctxt (#id item) orelse
                     Status.query_removed st item) items
    in
      if null items then st
      else if length (filter_out ItemIO.is_side_match args) = 1 then
        st |> process_step_single sc ictxt items prfstep
      else
        st |> process_step_pair sc ictxt items items' prfstep
    end

fun process_add_terms item (st as {ctxt, ...}) =
    let
      (* Add terms to the rewrite table. *)
      val {id, sc, ty_str, tname, ...} = item
      val ts = map Thm.term_of tname

      fun qualify_term t =
          case t of Abs _ => false | _ => not (Util.has_vars t)

      val rewr_terms = ItemIO.rewr_terms_of_item ctxt (ty_str, ts)
      val terms = rewr_terms |> map (Thm.cterm_of ctxt)
                             |> maps Subterms.get_all_subterms
                             |> map Thm.term_of
                             |> distinct (op aconv)
                             |> filter qualify_term
      val headt = if ty_str = TY_PROP then
                    if is_neg (the_single ts) then
                      [dest_not (the_single ts)]
                    else ts
                  else []

      val term_infos = map (pair id o Thm.cterm_of ctxt) (headt @ terms)

      val old_items =
          (maps (Status.get_items false st) (Status.get_unresolved st))
              |> remove BoxItem.eq_item item

      val ctxt' = ctxt |> Auto2Data.add_terms old_items term_infos

      (* Add new terms as updates. *)
      fun exists_item t =
          Status.find_ritem_exact st id (Fact (TY_TERM, [t], true_th))

      val terms2 = rewr_terms |> map (Thm.cterm_of ctxt)
                              |> maps Subterms.get_all_subterms_skip_if
                              |> map Thm.term_of
                              |> distinct (op aconv)
                              |> filter qualify_term
                              |> filter_out exists_item
                              |> filter_out (fn t => fastype_of t = boolT)

      (* New terms have score of the source item plus 1. *)
      val updt =
          {sc = sc + 1, prfstep_name = "$TERM", source = [item],
           raw_updt = AddItems {id = id, sc = NONE,
                                raw_items = map BoxItem.term_to_fact terms2}}
    in
      st |> (if length terms2 > 0 then Status.add_to_queue updt else I)
         |> Status.map_context (K ctxt')
    end

(* Process the given item. This has two parts: first, if the item is
   added to a box, process that fact with initial ictxt. Second, if
   the rewrite table is changed (due to either EQ, PROPERTY, or
   WELLFORM), process relevant items with incremental ictxt.
 *)
fun process_fact_all items (st as {ctxt, ...}) =
    if null items then st else
    let
      val id = #id (hd items)
      val sc = #sc (hd items)

      (* Obtain initial and incremental ictxt, and the list of
         relevant terms for that increment.
       *)
      val items' = maps (Status.get_items false st) (Status.get_unresolved st)
      val old_items = subtract BoxItem.eq_item items items'

      val incr_ctxt = Auto2Data.get_incr_type old_items items ctxt
      val (ctxt', ts) =
          case incr_ctxt of
              LAST (ctxt', ts) => (Auto2Data.get_single_type ctxt',
                                   map Thm.term_of ts)
            | _ => raise Fail "process_fact_all"
      val init_ctxt = SINGLE ctxt'

      (* List of items to consider for init and incr rounds. *)
      val init_items = filter_out (BoxItem.match_ty_str TY_PROPERTY) items

      val incr_ids = Status.get_unresolved st |> filter (
            fn id' => BoxID.is_box_unresolved ctxt (BoxID.merge_boxes ctxt (id, id')))
      val incr_items =
          if null ts then []
          else (maps (Status.get_items false st) incr_ids)
                   |> subtract BoxItem.eq_item items
                   |> filter (fn {tname, ...} =>
                                 exists (Util.has_subterm ts)
                                        (map Thm.term_of tname))
                   |> cons BoxItem.null_item

      (* List of proofsteps to consider for init and incr rounds. *)
      val thy = Proof_Context.theory_of ctxt
      val prfsteps = ProofStepData.get_prfsteps thy
    in
      st |> Status.map_context (K ctxt')
         |> fold (process_prfstep sc init_ctxt init_items items') prfsteps
         |> fold (process_prfstep sc incr_ctxt incr_items items') prfsteps
    end

fun process_add_items (updt as {sc, prfstep_name, raw_updt, ...})
                      (st as {uid_next, ctxt, ...}) =
    case raw_updt of
        AddItems {id, raw_items = ritems, ...} =>
        let
          val (ctxt', subst) = BoxItem.obtain_variant_frees (ctxt, ritems)
          val ritems' =
              ritems |> map (BoxItem.instantiate subst)
                     |> (if prfstep_name = "$RESOLVE" orelse
                            prfstep_name = "$INIT_BOX" then
                           maps (Normalizer.normalize_keep ctxt')
                         else
                           maps (Normalizer.normalize ctxt'))
                     |> distinct BoxItem.eq_ritem
          val (dup_ritems, new_ritems) =
              if sc = 0 then ([], ritems')
              else filter_split (Status.find_ritem_exact st id) ritems'

          val _ = if null dup_ritems orelse
                     not (Config.get ctxt print_trace) orelse
                     not (Config.get ctxt print_intended) then () else
                  if prfstep_name = "$TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Intend to add " ^
                                Update.update_info ctxt' id dup_ritems ^
                                " (" ^ Update.source_info updt ^ ")")

          val (handlers, ritems') = filter_split BoxItem.is_handler_raw new_ritems

          val uid_incr = length ritems'
          val uid_string = if uid_incr = 1 then string_of_int uid_next
                           else string_of_int uid_next ^ "-" ^
                                string_of_int (uid_next + uid_incr - 1)
          val sc_string = if Config.get ctxt print_score then
                            (string_of_int sc) ^ ", "
                          else ""

          val _ = if null new_ritems orelse
                     not (Config.get ctxt print_trace) then () else
                  if prfstep_name = "$TERM" andalso
                     not (Config.get ctxt print_term) then ()
                  else tracing ("Add " ^ Update.update_info ctxt' id ritems' ^
                                " (" ^ uid_string ^ ", " ^ sc_string ^
                                Update.source_info updt ^ ")")

          (* Produce the actual items. *)
          val items =
              map (fn i => BoxItem.mk_box_item
                               ctxt' (uid_next + i, id, sc, nth ritems' i))
                  (0 upto (length ritems' - 1))
        in
          st |> Status.map_context (K ctxt')
             |> fold (Status.add_handler id) (map BoxItem.dest_handler_raw handlers)
             |> fold process_add_terms items
             |> fold Status.add_item items
             |> process_fact_all items
             |> Status.incr_uid (length ritems')
        end
      | _ => raise Fail "process_add_items: wrong type of update"

fun process_add_boxes (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        AddBoxes {id, init_assum, ...} =>
        let
          val ritem = init_assum |> Thm.cterm_of ctxt
                                  |> Thm.assume |> Update.thm_to_ritem
          val _ = assert (fastype_of init_assum = propT)
                         "process_add_boxes: assumption is not of type prop."

          (* Find neg_form and check if already present. *)
          val neg_form_opt = if id = [] then NONE else
                             init_assum |> dest_Trueprop |> get_neg
                                        |> Status.find_fact st id

          val prev_prim_box = Status.find_prim_box st id init_assum
        in
          (* Do nothing if there is already a box with the same
             assumptions and conclusions.
           *)
          if is_some prev_prim_box then st
          else if is_some neg_form_opt then st

          (* Otherwise, proceed to create the box. *)
          else let
            val _ = if Config.get ctxt print_trace then
                      tracing ("Add box under " ^ BoxID.string_of_box_id id ^ " (" ^
                               Update.source_info updt ^ ")")
                    else ()
            val init_box = Box.init_box init_assum
            val (prim_id, st') = st |> Status.map_context (K ctxt)
                                    |> Status.add_prim_box id init_box
            val new_id = [prim_id]
            val _ = if Config.get ctxt print_trace then
                      tracing (
                        (BoxID.string_of_box_id new_id) ^ ": " ^
                        (Box.short_string_of_box
                             ctxt (Status.get_box st' new_id)))
                    else ()

            val ritems' =
                case ritem of
                    Handler _ => [ritem]
                  | Fact (ty_str, _, th) =>
                    if ty_str = TY_PROP then
                      map Update.thm_to_ritem (
                        Logic_ProofSteps.split_not_imp_th th)
                    else [ritem]

            val item_updt = {
              sc = sc, prfstep_name = "$INIT_BOX", source = [],
              raw_updt = AddItems {id = new_id, sc = NONE, raw_items = ritems'}}
          in
            st' |> process_add_items item_updt
          end
        end
      | _ => raise Fail "process_add_boxes: wrong type of update"

fun apply_update (updt as {raw_updt, ...}) (st as {ctxt, ...}) =
    let
      val id = Update.target_of_update raw_updt
    in
      if BoxID.is_box_resolved ctxt id then st else
      st |> not (Status.exist_box st id) ? Status.add_composite_box id
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
      val raw_updt = AddBoxes {id = [], sc = NONE, init_assum = get_neg' subgoal}
      val updt = {sc = 0, prfstep_name = "$INIT", source = [],
                  raw_updt = raw_updt}
    in
      ctxt |> Status.empty_status
           |> Status.add_composite_box [] |> Status.add_item BoxItem.null_item
           |> apply_update updt
    end

(* Given a condition status -> bool, step until the condition is
   satisfied. Return steps remaining as well as updated status.
 *)
fun step_until cond (steps, (st as {queue, ...})) =
    if cond st then
      (steps, st)
    else if steps = 0 then
      error "Maximum number of steps reached"
    else let
      val updt = Updates_Heap.min queue
                 handle List.Empty => error "No more moves"
      val st' = st |> Status.delmin_from_queue |> apply_update updt
    in
      step_until cond (steps - 1, st')
    end

val solve_root = step_until (fn st => BoxID.is_box_resolved (#ctxt st) [0])

end  (* structure ProofStatus. *)

(* Definition of auto2. *)

signature AUTO2 =
sig
  val auto2_tac: Proof.context -> tactic
end

structure Auto2 : AUTO2 =
struct

fun auto2_tac ctxt state =
    let
      val subgoals = state |> Thm.cprop_of |> Drule.strip_imp_prems
      val steps = Config.get ctxt max_steps
    in
      if null subgoals then Seq.empty else
      let
        val c_subgoal = hd subgoals
        val subgoal = Thm.term_of c_subgoal
        val _ = tracing (
              "Subgoal 1 of " ^ (string_of_int (length subgoals)) ^ ":\n" ^
              (Syntax.string_of_term ctxt subgoal) ^ "\n")
        val subgoal_norm = Conv.every_conv [
            Util.normalize_meta_horn ctxt,
            UtilLogic.to_obj_conv ctxt] c_subgoal
        val st = ProofStatus.init_status ctxt (Util.rhs_of subgoal_norm)
        val (steps', st') =
            Util.timer ("Total time: ",
                        fn _ => ProofStatus.solve_root (steps, st))
        val _ = writeln ("Finished in " ^
                         (string_of_int (steps - steps')) ^ " steps.")
        val th = st' |> Status.get_resolve_th
                     |> Thm.equal_elim (meta_sym subgoal_norm)
      in
        Seq.single (Thm.implies_elim state th)
      end
    end

end  (* structure Auto2 *)
