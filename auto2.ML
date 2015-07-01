(* Main file defining inference algorithm and tactic. *)

signature SCORES =
sig
  val item_score: raw_item -> int
  val items_score: raw_item list -> int
  val get_score: Update.raw_update -> int
  val get_id_score: Status.status -> Update.raw_update -> int
end;

structure Scores : SCORES =
struct

open Box

fun item_score ritem =
    case ritem of
        Init _ => 0
      | FreeVar _ => 10  (* cost for introducing a variable. *)
      | Handler _ => 0
      | Fact _ => if has_vars (get_fact_raw ritem) then 0
                  else size_of_term (get_fact_raw ritem)
      | MutState _ => raise AUTO2 "should not directly score MutState."

fun items_score raw_items = max int_ord (map item_score raw_items)

fun get_score raw_updt =
    case raw_updt of
        Update.AddItems {raw_items, ...} => items_score raw_items
      | Update.AddMutState _ => 10
      | Update.AddBoxes {assums, concls, ...} =>
        20 + 10 * Integer.sum (map size_of_term (assums @ concls))
      | Update.ResolveBox _ => ~1

fun get_id_score {lat, ...} raw_updt =
    let
      val id = Update.target_of_update raw_updt
      val prim_len = length (BoxID.get_extras_prim lat id)
    in
      case raw_updt of
          Update.AddItems _ => 20 * prim_len
        | Update.AddMutState _ => 20 * prim_len
        | Update.AddBoxes _ => 20 * prim_len
        | Update.ResolveBox _ => prim_len
    end

end  (* structure SCORES. *)

(* Proof status. Manages changes to proof status, and main loop
   carrying out proof steps and adding new proof steps to the queue.
 *)
signature PROOFSTATUS =
sig
  val check_hyps: box_id -> raw_item -> Status.status -> unit
  val scoring: proofstep -> int -> box_item list ->
               RewriteTable.rewrite_type -> Status.status -> Update.update list
  val process_mut_state_concls:
      string -> box_item -> Status.status -> Status.status
  val process_mut_state_steps:
      RewriteTable.rewrite_type -> box_item list -> string ->
      box_item list -> Status.status -> Status.status
  val process_fact_prfsteps: int -> RewriteTable.rewrite_type ->
                             box_item list -> Status.status -> Status.status
  val process_fact_rewrite: box_item -> Status.status -> Status.status
  val process_fact_all: box_item -> Status.status -> Status.status
  val process_add_items: Update.update -> Status.status -> Status.status
  val process_add_mut_state: Update.update -> Status.status -> Status.status
  val apply_callback: box_id * thm -> int -> Update.resolve_callback ->
                      Status.status -> Status.status
  val process_add_boxes: Update.update -> Status.status -> Status.status
  val resolve_box: Update.update -> Status.status -> Status.status
  val apply_update: Update.update -> Status.status -> Status.status
  val init_status: Proof.context -> term -> Status.status
  val step: Status.status -> Status.status
  val step_until:
      (Status.status -> bool) -> int * Status.status -> int * Status.status
  val solve_focus: int * Status.status -> int * Status.status
  val wait_for_facts:
      box_id -> term list -> int * Status.status -> int * Status.status
  val run_script: script -> int * Status.status -> int * Status.status
  val solve_root: int -> term * scripts * Status.status -> thm * Status.status
end;

structure ProofStatus : PROOFSTATUS =
struct

open Status
open Script

fun check_hyps id ritem (st as {ctxt, ...}) =
    let
      val th = get_thm_raw ritem
      val hyps = Thm.hyps_of th
      val inits = map fst (get_all_init_facts st id)
      val handlers = map fst (get_all_handlers st id)
      val extra = subtract (op aconv) (inits @ handlers) hyps
    in
      if length extra = 0 then ()
      else raise AUTO2CT ("illegal hyp", map (cert ctxt) extra)
    end

fun scoring {name, func, ...} sc items rtype st =
    let
      val merged_id = ProofStep.merged_id rtype items
      fun item_shadowed item =
          is_fact item andalso query_shadowed st (merged_id, get_fact item)
    in
      if is_box_resolved st merged_id orelse exists item_shadowed items then []
      else
        let
          val scs = map score_of_item items
          val max_sc = fold (curry Int.max) scs sc
          val raw_updts = func items rtype st
          fun process_raw_updt raw_updt =
              let
                val add_sc =
                    case get_fixed_sc (theory_of st) name of
                        NONE => Scores.get_score raw_updt
                      | SOME v => v
                val id_sc = Scores.get_id_score st raw_updt
              in
                {sc = add_sc + id_sc + max_sc, prfstep_name = name,
                 source = items, raw_updt = raw_updt}
              end
        in
          map process_raw_updt raw_updts
        end
    end

(* Using concl_fn for the given mut_type to produce updates from
   new mutable states.
 *)
fun process_mut_state_concls mut_type (mut_item as {id, sc, ...}) st =
    let
      val sval = dest_mut_state mut_item
      val thy = theory_of st
      val concl_fn = get_mut_concl thy mut_type
      fun process_raw_updt raw_updt =
          {sc = sc + (Scores.get_id_score st raw_updt) + 5,
           prfstep_name = mut_type, source = [mut_item], raw_updt = raw_updt}
      val updts = map process_raw_updt (concl_fn (id, sval) st)
    in
      st |> fold add_to_queue updts
    end

fun mut_state_eq_better st eq_better_fn (mut_item1 as {id = id1, ...})
                        (mut_item2 as {id = id2, ...}) =
    compare_eq_better st eq_better_fn (id1, dest_mut_state mut_item1)
                      (id2, dest_mut_state mut_item2)

fun mut_state_is_dominated_by st eq_better_fn mut_items mut_item =
    exists (fn mut_item' =>
               mut_state_eq_better st eq_better_fn mut_item' mut_item)
           mut_items

(* Match the given items against the given mut_states. For any new
   mut_states produced, apply mut_concl. All the given mut_states are
   of the given mut_type.
 *)
fun process_mut_state_steps rtype items mut_type mut_items st =
    let
      val thy = theory_of st
      val updt_fn = get_mut_update thy mut_type
      val eq_better_fn = get_mut_eq_better thy mut_type
      val is_dominated_by = mut_state_is_dominated_by st eq_better_fn

      fun match_item (mut_item as {id, sc, ...}) (item as {sc = sc', ...}) =
          let
            val sval = dest_mut_state mut_item
            val max_sc = Int.max (sc, sc')
            fun mut_state_to_item (id, sval) =
                mk_box_item (id, max_sc, MutState sval)
          in
            map mut_state_to_item (updt_fn (id, sval) rtype item st)
          end
    in
      case mut_items of
          [] => st
        | mut_item :: rest =>
          let
            (* Match the first mut_item against the items. If there
               are matches, append the new states and call
               recursively.
             *)
            val succ_items =
                (maps (match_item mut_item) items)
                    |> max_partial (mut_state_eq_better st eq_better_fn)
          in
            case succ_items of
                [] => process_mut_state_steps rtype items mut_type rest st
              | new_items =>
                (* Check whether the new states are actually new. If
                   yes, add them to mut_states and to st. Remove any
                   states in mut_states and st that are repetitive.
                 *)
                let
                  val all_mut_items = get_mut_states st mut_type
                  val new_items' =
                      filter_out (is_dominated_by all_mut_items) new_items
                  val del_items =
                      filter (is_dominated_by new_items') all_mut_items
                  val rest_items =
                      new_items' @
                      (rest |> filter_out (is_dominated_by new_items'))
                in
                  st |> fold (add_mut_state mut_type) new_items'
                     |> fold (del_mut_state mut_type) del_items
                     |> fold (process_mut_state_concls mut_type) new_items'
                     |> process_mut_state_steps rtype items mut_type rest_items
                end
          end
    end

(* Matches given fact with proofsteps, in the context of box with the
   given ID. Given fact should belong either to that box or to an
   ancestor box.
 *)
fun process_fact_prfsteps sc rtype items st =
    let
      val thy = theory_of st
      val step_a = get_step_a thy
      val step_aa = get_step_aa thy

      fun process_step_aa all_ids =
          let
            val items' = maps (get_facts st) all_ids
                              |> filter_out (is_all_eq_term' o get_fact)
            val inters = inter aconvi items items'
            fun process_pair (left, right) (prfstep as {filt, ...}) no_int =
                let
                  val (filt1, filt2) = the_pair filt
                  val left' = left |> filter (filt1 rtype)
                  val right' = right |> filter (filt2 rtype)
                  fun loop_right itm' =
                      maps (fn itm => (scoring prfstep sc) [itm, itm'] rtype st)
                           (if no_int andalso member aconvi inters itm' then
                              subtract aconvi inters left' else left')
                in
                  maps loop_right right'
                end

            fun process_one prfstep =
                process_pair (items, items') prfstep false @
                process_pair (items', items) prfstep true
          in
            maps process_one step_aa
          end

      fun process_step_a item =
          maps (fn prfstep => (scoring prfstep sc) [item] rtype st) step_a

      fun process_mut_states st =
          let
            val mut_types = get_mut_state_types st
            fun process_mut_type mut_type st =
                let
                  val mut_states = get_mut_states st mut_type
                in
                  st |> process_mut_state_steps rtype items mut_type mut_states
                end
          in
            fold process_mut_type mut_types st
          end

      val cur_id = ProofStep.merged_id rtype items
      val all_ids = get_unresolved st
      val all_updts =
          if cur_id = [] then
            process_step_aa (remove (op =) [] all_ids)
          else
            process_step_aa all_ids @ maps process_step_a items
    in
      st |> fold add_to_queue all_updts
         |> process_mut_states
    end

(* Process the given rewrite fact, located in the box with the given
   ID. For each fact or conclusion in any of the current, ancestor, or
   descendent boxes, check if it contains a subterm matching the left
   side of the rewrite. If so, re-process that fact or conclusion
   under the modified chain of rewrite tables.
 *)
fun process_fact_rewrite (item as {id, sc, ...}) st =
    let
      val eq_th = get_thm item
      val rtype = get_incr_type st id eq_th
      val tbl = get_rewrite_table st
      val (lhs, rhs) = Thm.prop_of eq_th |> HOLogic.dest_Trueprop |> dest_all_eq
      val updated_trms = RewriteTable.get_reachable_terms true tbl [lhs, rhs]
      fun to_visit_term t = has_subterm updated_trms t
      fun to_visit_item itm =
          let val t = get_fact itm in
            if is_Term t then to_visit_term (Logic.dest_term t)
            else if has_vars t then false
            else to_visit_term (HOLogic.dest_Trueprop t)
          end

      val all_ids = get_unresolved st |> filter (
            fn id' => is_box_unresolved st (merge_boxes st (id, id')))
      val items = maps (get_facts st) all_ids |> filter to_visit_item
                       |> filter_out (is_all_eq_term' o get_fact)
    in
      st |> map_rewrites (RewriteTable.add_rewrite_thm id eq_th)
         |> process_fact_prfsteps sc rtype items
    end

fun process_fact_all (item as {id, sc, ...}) (st as {ctxt, ...}) =
    let
      val fact = get_fact item
      fun qualify_term t = case t of Abs _ => false | _ => true
      val st' =
          if is_Term fact then st
          else if has_vars fact then st else
          let
            val tbl = get_rewrite_table st
            val fact' = HOLogic.dest_Trueprop fact
            val tbl' = if is_all_eq_term fact' then
                         let val (lhs, rhs) = dest_all_eq fact' in
                           tbl |> RewriteTable.add_term (id, lhs)
                               |> RewriteTable.add_term (id, rhs) end
                       else
                         tbl |> RewriteTable.add_term (id, fact')
            val new_trms = (RewriteTable.get_new_terms (tbl, tbl'))
                               |> map snd |> filter qualify_term
            fun raw_updt t = Update.thm_update (id, make_term_th ctxt t)
            (* New terms have the same score as the source item. *)
            fun term_to_updt t =
                {sc = sc, prfstep_name = "TERM", source = [item],
                 raw_updt = raw_updt t}
            val updts = map term_to_updt new_trms
          in
            st |> fold add_to_queue updts
               |> map_rewrites (K tbl')
          end
    in
      st' |> (if is_all_eq_term' fact then process_fact_rewrite item
              else process_fact_prfsteps 0 (get_init_type st') [item])
    end

fun process_shadow (item, id) (st as {ctxt, ...}) =
    if not (is_fact item) then raise AUTO2 "process_shadow: not a fact"
    else if id_of_item item = id then
      let
        val _ = tracing ("Removed " ^ (string_of_item ctxt item) ^
                         " from box " ^ (string_of_box_id id))
      in
        st |> map_box id (Box.remove_item item)
      end
    else
      let
        val _ = tracing ("Shadowed " ^ (string_of_item ctxt item) ^
                         " in box " ^ (string_of_box_id id))
      in
        st |> add_shadowed (id, get_fact item)
      end

fun process_add_items (updt as {sc, prfstep_name, raw_updt, ...})
                      (st as {ctxt, ...}) =
    case raw_updt of
        Update.AddItems {id, raw_items = ritems} =>
        let
          val all_facts = maps (get_facts st) (get_unresolved st)
                               |> filter_out (is_all_eq_term' o get_fact)
          val (ctxt', ritems') =
              (replace_internals_items (ctxt, ritems))
                  |> apsnd (maps (Status.normalize_ritem ctxt))
          val items = map (fn ritem' => mk_box_item (id, sc, ritem')) ritems'
                          |> filter_out (is_item_shadowed st all_facts)
                          |> filter_out (is_triv_eq st id)
        in
          if length items = 0 then
            let
              val _ = if prfstep_name = "TERM" then () else
                      tracing ("Intend to add " ^
                               (Update.update_info ctxt' id ritems') ^
                               " (" ^ (Update.source_info ctxt' updt) ^ ")")
            in st end
          else
            let
              fun shadow_list items item =
                  map (pair item) (shadow_list_ids st items item)
              val shadow_lists = maps (shadow_list all_facts) items @
                                 maps (shadow_list items) all_facts
              val _ = if prfstep_name = "TERM" then () else
                      tracing ("Add " ^ (Update.update_info ctxt' id ritems') ^
                               " (" ^ (Update.source_info ctxt' updt) ^ ")")
              fun process_add_one_item item st =
                  st |> map_box id (Box.add_item item)
                     |> (is_fact item) ? process_fact_all item
            in
              st |> map_context (K ctxt')
                 |> fold process_shadow shadow_lists
                 |> fold process_add_one_item items
            end
        end
      | _ => raise AUTO2 "process_add_items: wrong type of update"

fun process_add_mut_state (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.AddMutState {id, mut_type, sval} =>
        let
          val thy = theory_of st
          val all_mut_state = get_mut_states st mut_type
          val eq_better_fn = get_mut_eq_better thy mut_type
          val mut_item = mk_box_item (id, sc, MutState sval)
        in
          if mut_state_is_dominated_by st eq_better_fn all_mut_state mut_item
          then st else
          let
            val _ = tracing ("Add mut-state (" ^ mut_type ^ ", " ^
                             (sval |> prop_of' |> pretty_term ctxt |> str) ^ ")"
                             ^ " at box " ^ (string_of_box_id id) ^
                             " (" ^ (Update.source_info ctxt updt) ^ ")")
            val all_facts = maps (get_all_facts st) (get_unresolved st)
          in
            st |> add_mut_state mut_type mut_item
               |> process_mut_state_concls mut_type mut_item
               |> process_mut_state_steps (get_init_type st) all_facts
               mut_type [mut_item]
          end
        end
      | _ => raise AUTO2 "process_add_mut_state: wrong type of update"

fun apply_callback (id, th) sc cb st =
    let
      val eval_cb = cb (id, th)
      fun form_cb_updts raw_updt =
          {sc = sc, prfstep_name = "CALLBACK", source = [],raw_updt = raw_updt}
      val cb_updts = map form_cb_updts eval_cb
    in
      st |> fold add_to_queue cb_updts
    end

fun process_add_boxes (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.AddBoxes {id, freevars, assums, concls, cb} =>
        let
          (* The initial items. *)
          val init_assums = map (fn t => Init (t, InitAssum)) assums
          val init_concls = map (fn t => Init (get_neg' t, InitConcl)) concls
          val init_vars = map (fn var => Init (var, InitVar)) freevars
          val init_ritems = init_assums @ init_concls @ init_vars
          val init_box = Box.init_box |> Box.add_callback cb
          val (prim_id, st') = add_prim_box id init_box st
          val new_id = [prim_id]

          val trms = assums @ (map get_neg' concls)
          val dep_ritems = map (Fact o Thm.trivial o (cert ctxt)) trms @
                           map FreeVar freevars
          val ritems = init_ritems @ dep_ritems
          val (ctxt', ritems') =
              if prim_id = 0 then (ctxt, ritems) else
              (replace_internals_items (ctxt, ritems))
                  |> apsnd (maps (Status.normalize_ritem ctxt))

          val neg_form = get_neg_form ctxt' (
                ritems' |> filter is_init_raw |> map dest_init_raw)
          val neg_form_opt = find_fact st id neg_form
        in
          if is_some (find_prim_box st' id trms) then st else
          if is_some neg_form_opt then
            let
              val ({id = id', sc = _, ritem}, eq_th) = the neg_form_opt
              val th' = Thm.equal_elim eq_th (get_thm_raw ritem)
            in
              st |> apply_callback (id', th') sc cb
            end else
          let
            (* Create box with Init facts. *)
            val _ = tracing ("Add box under " ^ (string_of_box_id id) ^ " (" ^
                             (Update.source_info ctxt' updt) ^ ")")

            (* All Init ritems, as well as dependent variables at this step. *)
            val init_items =
                ritems' |> filter (is_init_raw orf is_freevar_raw)
                        |> map (fn ritem => mk_box_item (new_id, sc, ritem))
            val st'' = st' |> map_box new_id (fold Box.add_item init_items)
            val _ = tracing ((string_of_box_id new_id) ^ ": " ^
                             (Box.short_string_of_box
                                  ctxt' (get_box st'' new_id)))

            (* Add dependent facts at this step. *)
            val dep_ritems' = ritems' |> filter is_fact_raw
            val item_updt = {sc = sc, prfstep_name = "INIT_BOX", source = [],
                             raw_updt = Update.AddItems {
                               id = new_id, raw_items = dep_ritems'}}
          in
            st'' |> map_context (K ctxt')
                 |> process_add_items item_updt
          end
        end
      | _ => raise AUTO2 "process_add_boxes: wrong type of update"

(* When a box, whether primitive or composite, is resolved, perform
   the following two actions: 1. Resolve current and all descendent
   boxes. 2. Add the appropriate fact to each of the immediate parent
   boxes (or invoke callback if available).
 *)
fun resolve_box (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.ResolveBox {id, th} =>
        let
          val _ = tracing ("Finished box " ^ (string_of_box_id id) ^
                           " (" ^ (Update.source_info ctxt updt) ^ ")")
          val sc' = (if id = get_focus st then 0 else sc)
          val box = get_box st id
          fun update_one i st =
              let
                val cur_parent = get_parent_at_i st id i
                val ritem = get_on_resolve st id (nth id i) th
                val _ = check_hyps cur_parent ritem st
                val resolve_updt =
                    {sc = sc', prfstep_name = "RESOLVE", source = [],
                     raw_updt = Update.AddItems
                                    {id = cur_parent, raw_items = [ritem]}}
                (* If id is primitive, invoke any callbacks (with
                   parent id) and add the updates, omitting
                   resolve_updt from output.
                 *)
                val cbs = if length id > 1 then [] else Box.get_callbacks box
              in
                if length cbs = 0 then st |> add_to_queue resolve_updt
                else st |> fold (
                    apply_callback (cur_parent, get_thm_raw ritem) sc') cbs
              end
        in
          if is_box_resolved st id then st
          else st |> fold update_one (0 upto (length id) - 1)
                  |> add_resolved id
        end
      | _ => raise AUTO2 "resolve_box: wrong type of update"

fun apply_update (updt as {source, raw_updt, ...}) (st as {lat, ...}) =
    let
      val id = Update.target_of_update raw_updt
      fun item_shadowed item =
          is_fact item andalso query_shadowed st (id, get_fact item)
      val prim_ids = BoxID.get_ancestors_prim lat id
      fun is_root prim_id = (length (BoxID.get_parent_prim lat prim_id) = 0)
      val root_prim_ids = filter is_root prim_ids
    in
      if length root_prim_ids > 1 then st
      else if is_box_resolved st id then st
      else if exists (is_item_removed st) source then st
      else if exists item_shadowed source then st
      else
        st |> not (exist_box st id) ? Status.add_composite_box id
           |> (case raw_updt of
                   Update.AddItems _ => process_add_items updt
                 | Update.AddMutState _ => process_add_mut_state updt
                 | Update.AddBoxes _ => process_add_boxes updt
                 | Update.ResolveBox _ => resolve_box updt)
    end

fun init_status ctxt subgoal =
    let
      val (assums, concl) = Logic.strip_horn subgoal
      val vars = map Free (all_frees (concl :: assums))
      val raw_updt = Update.AddBoxes {
            id = [], freevars = vars, assums = assums, concls = [concl],
            cb = Update.null_callback}
      val updt = {sc = 0, prfstep_name = "INIT", source = [],
                  raw_updt = raw_updt}
    in
      empty_status ctxt |> apply_update updt |> set_focus [0]
    end

fun step (st as {queue, ...}) =
    let
      val updt = Updates_Heap.min queue
                 handle List.Empty => raise AUTO2 "No more moves"
    in
      st |> delmin_from_queue |> apply_update updt
    end

(* Given a condition status -> bool, step until the condition is
   satisfied. Return steps remaining as well as updated status.
 *)
fun step_until cond (steps, st) =
    if cond st then
      (steps, st)
    else if steps = 0 then
      raise AUTO2 ("Maximum number of steps reached when resolving box " ^
                   (string_of_box_id (get_focus st)))
    else
      step_until cond (steps - 1, step st)
      handle AUTO2 "No more moves" =>
             raise AUTO2 ("No more moves when resolving box " ^
                          (string_of_box_id (get_focus st)) ^ " (" ^
                          (string_of_int steps) ^ " steps remain.")

(* Solve for the ID given by focus id. *)
val solve_focus = step_until (fn st => is_box_resolved st (get_focus st))

(* Wait for certain facts to be present at given id. *)
fun wait_for_facts id facts =
    let
      fun cond st = forall (fn fact => is_some (find_fact st id fact)) facts
    in
      step_until cond
    end

(* Run the given script at focus id. Returns the new count of steps
   remaining, and the updated status.
 *)
fun run_script scrpt (steps, (st as {ctxt, queue, ...})) =
    let
      fun get_min_score queue =
          #sc (Updates_Heap.min queue) handle List.Empty => 0
      val sc = get_min_score queue
      val id = get_focus st
    in
      case scrpt of
          Script_Task {assums, concls, subs, cb} =>
          let
            val raw_updt =
                Update.AddBoxes {id = id, freevars = [], assums = assums,
                                 concls = concls, cb = cb}
            val updt = {sc = sc, prfstep_name = "SCRIPT", source = [],
                        raw_updt = raw_updt}
            val trms = assums @ (map get_neg' concls)
            val inits = map (fn t => (t, InitAssum)) assums @
                        map (fn t => (get_neg' t, InitConcl)) concls
            val neg_form = get_neg_form ctxt inits
          in
            case find_fact st id neg_form of
                SOME ({id = id', sc = _, ritem}, eq_th) =>
                (steps, st |> apply_callback (
                   id', Thm.equal_elim eq_th (get_thm_raw ritem)) sc cb)
              | NONE =>
                let
                  val st' = process_add_boxes updt st
                  val id' =
                      the (find_prim_box st' id trms)
                      handle Option.Option =>
                             raise AUTO2 "run_script (task): failed to add box."
                in
                  (steps, st') |> apsnd (set_focus id')
                               |> fold run_script subs
                               |> solve_focus
                               |> apsnd (set_focus id)
                end
          end
        | Script_Info {prfstep = {name, func, ...}, source} =>
          let
            (* Make sure the source statements exist. *)
            val (steps', st') = (steps, st) |> wait_for_facts id source
            val items =
                map (fst o the o find_fact st' id) source
                handle Option.Option =>
                       raise AUTO2 "run_script (info): cannot find sources."
            fun process_raw_updt raw_updt =
                {sc = sc, prfstep_name = name, source = items,
                 raw_updt = raw_updt}
            val updts = (func items (get_init_type st) st)
                            |> map process_raw_updt
            val _ = assert (length updts > 0)
                           "run_script (info): failed to apply proofstep."
          in
            (steps', st' |> fold apply_update updts)
          end
    end

fun solve_root steps (subgoal, scrpts, (st as {ctxt, ...})) =
    let
      val nprems = length (Logic.strip_imp_prems subgoal)
      val obj_goal = (cert ctxt subgoal) |> to_obj_conv ctxt |> rhs_of
      fun find_obj_goal queue =
          let
            val ({raw_updt, ...}, queue') =
                Updates_Heap.min_elem queue
                handle List.Empty => raise AUTO2 "solve_root: goal not found"
          in
            case raw_updt of
                Update.AddItems {id = [], raw_items = [raw_item]} =>
                if get_fact_raw raw_item aconv obj_goal then
                  apply_to_thm (to_meta_imp_conv_n nprems)
                               (get_thm_raw raw_item)
                else find_obj_goal queue'
              | _ => find_obj_goal queue'
          end

      val (steps', st' as {queue, ...}) =
          (steps, st) |> fold run_script scrpts |> solve_focus
      val _ = writeln ("Finished in " ^ (string_of_int (steps - steps')) ^
                       " steps.")
    in
      (find_obj_goal queue, st')
    end

end  (* structure ProofStatus. *)

(* Definition of AUTO2. *)
fun auto2_gen ctxt steps pre_scrpts state =
    let
      val prop = Thm.prop_of state
      val subgoals = prop |> Logic.strip_imp_prems
    in if length subgoals = 0 then state else
       let
         val subgoal = hd subgoals
         val _ = tracing (
               "Subgoal 1 of " ^ (string_of_int (length subgoals)) ^ ":\n" ^
               (subgoal |> pretty_term ctxt |> str) ^ "\n")
         val (scrpts, ctxt') = pre_scrpts ctxt
         val st = ProofStatus.init_status ctxt' subgoal
         val (th, _) =
             timer ("Total time: ",
                    fn _ => ProofStatus.solve_root steps (subgoal, scrpts, st))
       in
         Thm.implies_elim state th
       end
    end

fun auto2_tac ctxt = PRIMITIVE (auto2_gen ctxt 2000 no_script)
fun auto2l_tac ctxt steps = PRIMITIVE (auto2_gen ctxt steps no_script)
fun auto2s_tac ctxt pre_scrpts = PRIMITIVE (auto2_gen ctxt 2000 pre_scrpts)
fun auto2ls_tac ctxt steps pre_scrpts =
    PRIMITIVE (auto2_gen ctxt steps pre_scrpts)
