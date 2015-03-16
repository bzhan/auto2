(* Main file defining inference algorithm and tactic. *)

(* Definition of main data structures. *)

type box_id = BoxID.box_id
val string_of_box_id = BoxID.string_of_box_id
val string_of_box_ids = string_of_list string_of_box_id

signature BOXITEM =
sig
  type retro_handler
  datatype raw_item = Init of term * bool  (* (t, is_concl) *)
                    | FreeVar of term
                    | Handler of term * retro_handler
                    | Fact of thm
  val is_fact_raw: raw_item -> bool
  val get_thm_raw: raw_item -> thm
  val get_fact_raw: raw_item -> term
  val is_freevar_raw: raw_item -> bool
  val dest_freevar_raw: raw_item -> term
  val is_init_raw: raw_item -> bool
  val dest_init_raw: raw_item -> term * bool
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term * retro_handler
  val handler_ritems: Proof.context -> term -> retro_handler -> raw_item list
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val string_of_raw_item: Proof.context -> raw_item -> string
  val replace_internals_items:
      Proof.context * raw_item list -> Proof.context * raw_item list

  type box_item
  val mk_box_item: box_id * int * raw_item -> box_item
  val id_of_item: box_item -> box_id
  val is_fact: box_item -> bool
  val get_thm: box_item -> thm
  val get_fact: box_item -> term
  val aconvi: box_item * box_item -> bool
  val is_freevar: box_item -> bool
  val dest_freevar: box_item -> term
  val score_of_item: box_item -> int
  val string_of_item: Proof.context -> box_item -> string
  val is_init: box_item -> bool
  val dest_init: box_item -> term * bool
  val is_handler: box_item -> bool
  val dest_handler: box_item -> term * retro_handler
end;

structure BoxItem : BOXITEM =
struct

type retro_handler = (term * term list -> bool) * (term * thm -> thm)
datatype raw_item = Init of term * bool
                  | FreeVar of term
                  | Handler of term * retro_handler
                  | Fact of thm

fun is_fact_raw ritem =
    case ritem of Fact _ => true | _ => false
fun get_thm_raw ritem =
    case ritem of Fact th => th | _ => raise AUTO2 "get_thm_raw: wrong type"
fun get_fact_raw ritem = Thm.prop_of (get_thm_raw ritem)
fun is_freevar_raw ritem =
    case ritem of FreeVar _ => true | _ => false
fun dest_freevar_raw ritem =
    case ritem of FreeVar t => t
                | _ => raise AUTO2 "dest_freevar_raw: wrong type"
fun is_init_raw ritem =
    case ritem of Init _ => true | _ => false
fun dest_init_raw ritem =
    case ritem of Init (t, b) => (t, b)
                | _ => raise AUTO2 "dest_init_raw: wrong type"
fun is_handler_raw ritem =
    case ritem of Handler _ => true | _ => false
fun dest_handler_raw ritem =
    case ritem of Handler (t, handler) => (t, handler)
                | _ => raise AUTO2 "dest_handler_raw: wrong type"
fun handler_ritems ctxt t handler =
    [Fact (assume_thm ctxt t), Handler (t, handler)]
fun instantiate inst ritem =
    let
      val subst = subst_atomic (map (apply2 Thm.term_of) inst)
    in
      case ritem of Init (t, b) => Init (subst t, b)
                  | FreeVar t => FreeVar (subst t)
                  | Handler (t, handler) => Handler (subst t, handler)
                  | Fact th => Fact (th |> Thm.instantiate ([], inst)
                                        |> send_concrete_to_hyps)
    end
fun string_of_raw_item ctxt ritem =
    let val trm = case ritem of
                      Init (t, _) => t
                    | FreeVar t => t
                    | Handler (t, _) => t
                    | Fact _ => get_fact_raw ritem
    in trm |> pretty_term ctxt |> str end

(* Given a context and list of raw items, replace internal variables
   declared in the list and used in the terms in the list by fresh
   variables from context, and declare those variables in context.
 *)
fun replace_internals_items (ctxt, ritems) =
    let
      (* Original internal variables. *)
      val all_vars =
          ritems |> filter is_freevar_raw
                 |> map (dest_Var o dest_freevar_raw)
          handle TERM _ =>
                 raise AUTO2 "replace_internals_items: dest_Var"
      (* New names for these variables. *)
      val all_vars' =
          all_vars |> map (fn ((nm,_), T) => (Name.dest_internal nm, T))
                   |> Variable.variant_frees ctxt []
          handle Fail "unsuffix" =>
                 raise AUTO2 "replace_internals_items: dest_internal"
      val subst = (map Var all_vars) ~~ (map Free all_vars')
      val csubst = map (apply2 (cert ctxt)) subst
      (* Use direct version, since this is called when ctxt is in body. *)
      val ctxt' = Variable.add_fixes_direct (map fst all_vars') ctxt
    in
      (ctxt', map (instantiate csubst) ritems)
    end

type box_item = {id: box_id, sc: int, ritem: raw_item}
fun mk_box_item (id, sc, ritem) = {id = id, sc = sc, ritem = ritem}
fun id_of_item {id, ...} = id
fun is_fact {ritem, ...} = is_fact_raw ritem
fun get_thm {ritem, ...} = get_thm_raw ritem
fun get_fact {ritem, ...} = get_fact_raw ritem
fun aconvi (item1, item2) = get_fact item1 aconv get_fact item2
fun is_freevar {ritem, ...} = is_freevar_raw ritem
fun dest_freevar {ritem, ...} = dest_freevar_raw ritem
fun score_of_item {sc, ...} = sc
fun string_of_item ctxt {ritem, ...} = string_of_raw_item ctxt ritem
fun is_init {ritem, ...} = is_init_raw ritem
fun dest_init {ritem, ...} = dest_init_raw ritem
fun is_handler {ritem, ...} = is_handler_raw ritem
fun dest_handler {ritem, ...} = dest_handler_raw ritem

end  (* structure BoxItem. *)

open BoxItem

signature BOX =
sig 
  type box
  val init_box: box
  val add_item: box_item -> box -> box
  val remove_item: box_item -> box -> box
  val get_facts: box -> box_item list
  val get_init_facts: box -> (term * bool) list
  val get_freevars: box -> term list
  val get_init_vars: box -> term list
  val get_dep_vars: box -> term list
  val get_handlers: box -> (term * retro_handler) list
  val string_of_box: Proof.context -> box -> string
  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct 

type box = box_item list
val init_box = []
fun add_item item = cons item
fun remove_item item = remove pointer_eq item

val get_facts = filter is_fact
val get_init_facts = map dest_init o filter is_init
val get_freevars = map dest_freevar o filter is_freevar
fun get_init_vars items =
    let
      val inits = get_init_facts items |> map fst
      val freevars = get_freevars items
      val init_vars = map Free (all_frees inits)
    in
      inter (op aconv) init_vars freevars
    end
fun get_dep_vars items =
    subtract (op aconv) (get_init_vars items) (get_freevars items)
val get_handlers = map dest_handler o filter is_handler

fun string_of_box ctxt box =
    let
      val init_vars = get_init_vars box
      val dep_vars = get_dep_vars box
      val init_facts = get_init_facts box |> map fst
      val dep_all = map get_fact (get_facts box)
      val dep_facts = dep_all |> filter (not o is_Term)
      val terms = dep_all |> filter is_Term |> map Logic.dest_term
    in
      cat_lines [
        "vars: " ^ (pretty_terms ctxt init_vars |> str) ^
        (if length dep_vars = 0 then "" else
         " (" ^ (pretty_terms ctxt dep_vars |> str) ^ ")"),
        "init: " ^ (pretty_terms ctxt init_facts |> str),
        "derived: " ^ (pretty_terms ctxt dep_facts |> str),
        "terms: " ^ (pretty_terms ctxt terms |> str)]
    end

fun short_string_of_box ctxt box =
    get_init_facts box |> map fst |> pretty_terms ctxt |> str

end  (* structure Box. *)

signature UPDATE =
sig
  datatype raw_update
    = AddItems of {id: box_id, raw_items: raw_item list}
    | AddBoxes of {id: box_id, freevars: term list, assums: term list,
                   concls: term list}
    | ResolveBox of {id: box_id, th: thm}
  type update
  val thm_update: box_id * thm -> raw_update
  val target_of_update: raw_update -> box_id
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: Proof.context -> update -> string
end;

structure Update : UPDATE =
struct

datatype raw_update
  = AddItems of {id: box_id, raw_items: raw_item list}
  | AddBoxes of {id: box_id, freevars: term list, assums: term list,
                 concls: term list}
  | ResolveBox of {id: box_id, th: thm}
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

fun thm_update (id, th) =
    if Thm.prop_of th aconv @{prop "False"} then ResolveBox {id = id, th = th}
    else AddItems {id = id, raw_items = [Fact th]}

fun target_of_update raw_updt =
    case raw_updt of
        AddItems {id, ...} => id
      | AddBoxes {id, ...} => id
      | ResolveBox {id, ...} => id

fun update_info ctxt id ritems =
    (string_of_list' (string_of_raw_item ctxt)
                     (filter (not o is_handler_raw) ritems)) ^
    " at box " ^ (string_of_box_id id)
fun source_info ctxt {sc, prfstep_name, source, ...} =
    (string_of_int sc) ^ ", " ^ prfstep_name ^ " on " ^
    (string_of_list' (string_of_item ctxt) source)

end  (* structure Update. *)

structure Updates_Heap =
Heap (
  type elem = Update.update
  fun ord ({sc = sc1, ...}, {sc = sc2, ...}) = int_ord (sc1, sc2)
)

signature STATUS =
sig
  type status
  val theory_of: status -> theory
  val normalize_ritem: theory -> raw_item -> raw_item
  val exist_box: status -> box_id -> bool
  val get_box: status -> box_id -> Box.box
  val get_rewrite_table: status -> RewriteTable.rewrite_table
  val get_init_type: status -> RewriteTable.rewrite_type
  val get_incr_type: status -> box_id -> thm -> RewriteTable.rewrite_type

  val get_lattice: status -> BoxID.box_lattice
  val get_parent_prim: status -> int -> box_id
  val get_parent_at_i: status -> box_id -> int -> box_id
  val merge_boxes: status -> box_id * box_id -> box_id
  val is_ancestor: status -> box_id -> box_id -> bool
  val is_descendent: status -> box_id -> box_id -> bool
  val is_eq_ancestor: status -> box_id -> box_id -> bool
  val is_eq_descendent: status -> box_id -> box_id -> bool
  val is_box_resolved: status -> box_id -> bool
  val is_box_unresolved: status -> box_id -> bool

  val map_box: box_id -> (Box.box -> Box.box) -> status -> status
  val map_context: (Proof.context -> Proof.context) -> status -> status
  val map_rewrites: (RewriteTable.rewrite_table -> RewriteTable.rewrite_table)
                    -> status -> status
  val add_prim_box: box_id -> Box.box -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_all_ids: status -> box_id list
  val get_resolved: status -> box_id list
  val get_unresolved: status -> box_id list
  val get_ancestors: status -> box_id -> box_id list
  val add_composite_box: box_id -> status -> status

  val get_facts: status -> box_id -> box_item list
  val get_init_facts: status -> box_id -> (term * bool) list
  val get_init_vars: status -> box_id -> term list
  val get_dep_vars: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term * retro_handler) list
  val get_all_facts: status -> box_id -> box_item list
  val get_all_init_facts: status -> box_id -> (term * bool) list
  val get_all_init_vars: status -> box_id -> term list
  val get_all_dep_vars: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term * retro_handler) list

  val can_shadow: status -> box_item -> box_item -> bool
  val can_shadow_list: status -> box_item list -> box_item -> bool
  val is_item_shadowed: status -> box_item -> bool
  val invoke_handler: term * retro_handler -> thm -> thm
  val invoke_handlers: (term * retro_handler) list -> thm -> thm
  val get_neg_form: Proof.context -> (term * bool) list -> term
  val get_neg_form_thm: Proof.context -> (term * bool) list * thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> raw_item
  val box_already_exists: status -> box_id -> raw_item list -> bool
  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: Update.update -> status -> status
  val delmin_from_queue: status -> status
  val string_of_status: status -> string
end;

structure Status : STATUS =
struct

type status = {
  lat: BoxID.box_lattice,
  boxes: Box.box Boxidtab.table,
  queue: Updates_Heap.T,
  rewrites: RewriteTable.rewrite_table,
  ctxt: Proof.context
}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun normalize_ritem thy ritem =
    case ritem of
        Fact th =>
        if (is_Term orf is_implies) (Thm.prop_of th) then Fact th
        else Fact (th |> apply_to_thm (Conv.arg_conv exists_split_conv)
                      |> apply_to_thm (ACUtil.rearrange_assoc_full thy)
                      |> ACUtil.rearrange_ac_thm thy
                      |> apply_to_thm (Conv.arg_conv normalize_pred_comm))
      | _ => ritem

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id = the (Boxidtab.lookup boxes id)
fun get_rewrite_table {rewrites, ...} = rewrites

(* Obtain rewrite table contained in st, but with (lhs, rhs) added at
   an additional primitive id.
 *)
fun get_init_type st = RewriteTable.SINGLE (get_rewrite_table st)
fun get_incr_type st id eq_th =
    RewriteTable.LAST
        (get_rewrite_table st |> RewriteTable.append_rewrite_thm eq_th, id)

fun get_lattice {lat, ...} = lat
val get_parent_prim = BoxID.get_parent_prim o get_lattice
val get_parent_at_i = BoxID.get_parent_at_i o get_lattice
val merge_boxes = BoxID.merge_boxes o get_lattice
val is_ancestor = BoxID.is_ancestor o get_lattice
val is_descendent = BoxID.is_descendent o get_lattice
val is_eq_ancestor = BoxID.is_eq_ancestor o get_lattice
val is_eq_descendent = BoxID.is_eq_descendent o get_lattice
val is_box_resolved = BoxID.is_box_resolved o get_lattice
val is_box_unresolved = BoxID.is_box_unresolved o get_lattice

fun map_box id f {lat, boxes, queue, rewrites, ctxt} =
    {lat = lat, boxes = Boxidtab.map_entry id f boxes, queue = queue,
     rewrites = rewrites, ctxt = ctxt}

fun map_context f {lat, boxes, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, queue = queue,
     rewrites = rewrites |> RewriteTable.map_context f, ctxt = f ctxt}

fun map_rewrites f {lat, boxes, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, queue = queue, rewrites = f rewrites,
     ctxt = ctxt}

fun add_prim_box parent_id new_box {lat, boxes, queue, rewrites, ctxt} =
    let
      val (id, lat') = BoxID.add_prim_id parent_id lat
    in
      (id, {lat = lat',
            boxes = Boxidtab.update_new ([id], new_box) boxes,
            queue = queue,
            rewrites = RewriteTable.map_lat (K lat') rewrites,
            ctxt = ctxt})
    end

fun add_resolved id {lat, boxes, queue, rewrites, ctxt} =
    let
      val lat' = BoxID.add_resolved id lat
    in
      {lat = lat', boxes = boxes, queue = queue,
       rewrites = RewriteTable.map_lat (K lat') rewrites, ctxt = ctxt}
    end

fun get_all_ids {boxes, ...} = Boxidtab.keys boxes
fun get_resolved st = filter (is_box_resolved st) (get_all_ids st)
fun get_unresolved st = filter_out (is_box_resolved st) (get_all_ids st)

(* Returns list of generalized boxes currently in st that are
   ancestors. Note if id is unresolved, then all ancestors of id must
   be unresolved.
 *)
fun get_ancestors st id = filter (is_descendent st id) (get_unresolved st)

(* Add box with the given composite id to status. Assuming this ID is
   not already present in status.
 *)
fun add_composite_box id (st as {lat, boxes, queue, rewrites, ctxt}) =
    let
      val new_box = []
    in
      if exist_box st id then
        raise AUTO2 "Try to add a composite box that already exists"
      else if length id = 1 then
        raise AUTO2 "Try to add a primitive box as a composite"
      else
        {lat = lat, boxes = Boxidtab.update_new (id, new_box) boxes,
         queue = queue, rewrites = rewrites, ctxt = ctxt}
    end

fun get_for_box f st id = if exist_box st id then f (get_box st id) else []
fun get_all_for_box f st id =
    maps (get_for_box f st) (id :: get_ancestors st id)

val get_facts       = get_for_box Box.get_facts
val get_init_facts  = get_for_box Box.get_init_facts
val get_init_vars   = get_for_box Box.get_init_vars
val get_dep_vars    = get_for_box Box.get_dep_vars
val get_handlers    = get_for_box Box.get_handlers
val get_all_facts       = get_all_for_box Box.get_facts
val get_all_init_facts  = get_all_for_box Box.get_init_facts
val get_all_init_vars   = get_all_for_box Box.get_init_vars
val get_all_dep_vars    = get_all_for_box Box.get_dep_vars
val get_all_handlers    = get_all_for_box Box.get_handlers

fun test_shadow_pattern id tbl pats trms =
    let
      val pairs = map (pair false) (map HOLogic.mk_Trueprop pats ~~ trms)
      val insts = (fo_table_match_list id tbl pairs)
                      |> filter (fn ((id', _), _) => id = id')
    in
      length insts <> 0
    end

(* Whether adding item1 will make item2 extraneous. *)
fun can_shadow st (item1 as {id = id1, ...}) (item2 as {id = id2, ...}) =
    if not (is_fact item1) orelse not (is_fact item2) then false else
    if not (is_eq_ancestor st id1 id2) then false else
    let
      val tbl = get_rewrite_table st
      val (fact1, fact2) = (get_fact item1, get_fact item2)
      val equiv = RewriteTable.is_equiv id2 tbl
    in
      if is_Term fact1 andalso is_Term fact2 then
        RewriteTable.is_subequiv id2 tbl (Logic.dest_term fact1,
                                          Logic.dest_term fact2)
      else if is_implies fact1 orelse is_implies fact2 then
        fact1 aconv fact2
      else equiv (fact1, fact2) orelse
           test_shadow_pattern id2 tbl [@{term_pat "?A::bool"},
                                        @{term_pat "?A | ?B"}] [fact1, fact2]
    end

(* Whether any of items shadow item. *)
fun can_shadow_list st items item =
    exists (fn item' => can_shadow st item' item) items

(* Determine whether the given item is already removed from st (due to
   an item with the same term in an ancestor box).
 *)
fun is_item_shadowed st (item as {id, ...}) =
    not (member pointer_eq (get_box st id) item)

(* Invoke a single handler (_, f) on a term t. *)
fun invoke_handler (t, (_, f)) th = f (t, th)

(* Invoke any handler given in the list handlers, whose term appear as
   a hypothesis of th.
 *)
fun invoke_handlers handlers th =
    let
      val all_hyps = Thm.hyps_of th
      val handlers' = handlers |> filter (member (op aconv) all_hyps o fst)
      val retro_hyps = map fst handlers'
    in
      if retro_hyps = [] then th
      else
        let
          val to_invoke =
              find_index (fn (t, (ready, _)) => ready (t, retro_hyps)) handlers'
          val _ = assert (to_invoke <> ~1)
                         "invoke_handlers: cannot find invokable handler."
          val th' = invoke_handler (nth handlers' to_invoke) th
        in
          invoke_handlers handlers th'
        end
    end

(* Return [trms] ==> False in a more human readable form. *)
fun get_neg_form ctxt inits =
    let
      val neg_concls = inits |> filter snd |> map fst
      val facts = inits |> filter (not o snd) |> map fst
      val mk_imp = curry Logic.mk_implies
      (* If there is a specified conclusion, take that. Otherwise take
         first fact as conclusion.
       *)
      val meta_prop = case neg_concls of
                          [] => fold mk_imp (tl facts) (get_neg' (hd facts))
                        | [neg_concl] => fold mk_imp facts (get_neg' neg_concl)
                        | _ => raise AUTO2 "get_neg_form: too many concls"
    in
      to_obj_conv ctxt (cert ctxt meta_prop) |> rhs_of
    end

(* Given a theorem th with trms in the hypothesis, return a new
   theorem with trms pulled into the proposition of th, which is
   rewritten into a more human readable form.
 *)
fun get_neg_form_thm ctxt (inits, th) =
    let
      val neg_concls = inits |> filter snd |> map fst |> map (cert ctxt)
      val facts = inits |> filter (not o snd) |> map fst |> map (cert ctxt)
      val th' = case neg_concls of
                    [] => th
                  | [neg_concl] => th |> Thm.implies_intr neg_concl
                  | _ => raise AUTO2 "get_neg_form_thm: too many concls"
    in
      th' |> fold Thm.implies_intr facts
          |> rewrite_thm_from_contra_form
          |> apply_to_thm (to_obj_conv ctxt)
    end

(* Derive the consequence if box full_id is resolved, to the parent id
   formed by getting parent at prim_id. Currently handles at most one
   initial fact and conclusion.
 *)
fun get_on_resolve (st as {ctxt, ...}) full_id prim_id th =
    let
      (* First get list of handlers to invoke. *)
      val retro_ids = (get_unresolved st)
                          |> filter (is_eq_ancestor st [prim_id])
                          |> filter (is_eq_descendent st full_id)
      val handlers = maps (get_handlers st) retro_ids
      val th' = invoke_handlers handlers th
      val init_facts = get_init_facts st [prim_id]
      val init_vars = get_init_vars st [prim_id]
      val ct_vars = map (cert ctxt) init_vars
      val th'' = (get_neg_form_thm ctxt (init_facts, th'))
                     |> (prim_id <> 0 ? fold Thm.forall_intr ct_vars)
                     |> apply_to_thm (to_obj_conv ctxt)
      val _ = if prim_id = 0 then
                assert (length (Thm.hyps_of th'') = 0)
                       "get_on_resolve: did not remove all hypothesis at box 0."
              else ()
      val _ = if length init_vars = 0 then
                assert (Thm.prop_of th'' aconv get_neg_form ctxt init_facts)
                       "get_on_resolve: wrong value from get_neg_form_thm."
              else ()
    in
      Fact th''
    end

(* Check whether the items to be added under a new child box already
   exists in the current box or in another box whose parent is an
   ancestor of the current box. If this is so then the items do not
   need to be added.
 *)
fun box_already_exists st id ritems =
    let
      fun exists_at_id id' =
          let
            val prev_facts = map get_fact (get_all_facts st id')
            fun already_exists ritem =
                if is_fact_raw ritem then
                  member (op aconv) prev_facts (get_fact_raw ritem)
                else false
          in
            forall already_exists ritems
          end

      fun can_test_id id' =
          case id' of
              [prim_id'] => is_eq_ancestor st (get_parent_prim st prim_id') id
            | _ => false

      val ids_to_test = get_unresolved st |> filter can_test_id
    in
      exists exists_at_id ids_to_test
    end

fun map_queue f {lat, boxes, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, queue = f queue, rewrites = rewrites,
     ctxt = ctxt}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

fun string_of_status (st as {rewrites, ctxt, ...}) =
    let
      val all_ids = get_all_ids st
      fun string_of_id_box id =
          "Box number " ^ (string_of_box_id id) ^
          (if length id = 1 then
             " under " ^ string_of_box_id (get_parent_prim st (the_single id))
           else "") ^
          ": " ^ Box.string_of_box ctxt (get_box st id)
    in
      "Number of boxes: " ^ (string_of_int (length all_ids)) ^ "\n" ^
      (enum_noindent "\n" "" "" (map (Pretty.str o string_of_id_box)
                                     all_ids) |> str) ^
      "\nRewrite table:\n" ^ (RewriteTable.to_string rewrites)
    end

end  (* structure Status *)

(* Definition of core proof steps (single-step change to proof
   state). Each proofstep is a function taking the index of the
   current box, known facts to consider (either in the current box or
   an ancestor box), and conclusion in the current box, and returns a
   list of updates to the proof status.
 *)
signature PROOFSTEP =
sig
  type pre_filter
  type proofstep_fn
  type proofstep
  type prfstep_filter
  datatype prfstep_descriptor = WithFact of term
                              | WithGoal of term
                              | WithTerm of term
                              | GetFact of term * thm
                              | GetGoal of term * thm
                              | GetResolve of thm
                              | CreateCase of term list * term list
                              | Filter of prfstep_filter
  val get_prfstep_fn: proofstep -> proofstep_fn
  val neqt_filter: string -> term -> prfstep_filter
  val neq_filter: string -> string -> prfstep_filter
  val order_filter: string -> string -> prfstep_filter
  val size1_filter: string -> prfstep_filter
  val canonical_split_filter: string -> string -> string -> prfstep_filter
  val ac_atomic_filter: string -> string -> prfstep_filter
  val term_neq_filter: string -> string -> string -> prfstep_filter
  val subset_var_filter: string -> string -> prfstep_filter
  type id_inst2
  val no_prereq: pre_filter
  val all_insts: prfstep_filter
  val merged_id: RewriteTable.rewrite_type -> box_item list -> box_id
  val get_insts_filt: term list -> box_item list -> RewriteTable.rewrite_type ->
                      prfstep_filter -> id_inst_ths list
  val get_insts: term list -> box_item list -> RewriteTable.rewrite_type ->
                 id_inst_ths list
  val pat_prereq: term -> pre_filter
  val gen_prfstep: string -> prfstep_descriptor list -> proofstep

  val preprocess_thm: term list -> term * thm -> term * thm
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_pats: prfstep_descriptor list -> term list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> (term list * term list) list
  val prfstep_thm: string -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_conv: string -> prfstep_descriptor list -> conv -> proofstep
  val prfstep_rrule: prfstep_descriptor list -> thm -> proofstep
  val prfstep_two_stage: string -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_thm_fn: string -> prfstep_descriptor list ->
                      (Proof.context -> id_inst_ths -> thm) -> proofstep
  val prfstep_custom:
      string -> prfstep_descriptor list ->
      (id_inst_ths -> Status.status -> Update.raw_update list) -> proofstep
end;

structure ProofStep : PROOFSTEP =
struct

open Box
open Update
open Status

type pre_filter = RewriteTable.rewrite_type -> box_item -> bool
type proofstep_fn = box_item list -> RewriteTable.rewrite_type ->
                    status -> raw_update list
type proofstep = {name: string, filt: pre_filter list, func: proofstep_fn}
type prfstep_filter = RewriteTable.rewrite_table -> id_inst -> bool
datatype prfstep_descriptor = WithFact of term
                            | WithGoal of term
                            | WithTerm of term
                            | GetFact of term * thm
                            | GetGoal of term * thm
                            | GetResolve of thm
                            | CreateCase of term list * term list
                            | Filter of prfstep_filter
fun get_prfstep_fn {func, ...} = func
fun neqt_filter s1 t2 tbl (id, inst) =
    not (RewriteTable.is_equiv id tbl (lookup_inst inst s1, t2))
fun neq_filter s1 s2 tbl (id, inst) =
    neqt_filter s1 (lookup_inst inst s2) tbl (id, inst)
fun order_filter s1 s2 _ (_, inst) =
    Term_Ord.termless (lookup_inst inst s1, lookup_inst inst s2)
fun size1_filter s1 tbl (id, inst) =
    size_of_term (RewriteTable.simp_val id tbl (lookup_inst inst s1)) = 1
fun canonical_split_filter fnm s1 s2 tbl (_, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "canonical_split_filter: ac_itm not found"
      | SOME ac_itm =>
        let
          val (A, B) = (lookup_inst inst s1, lookup_inst inst s2)
        in
          not (ACUtil.head_agrees ac_itm A) andalso
          forall (fn B => Term_Ord.termless (A, B)) (ACUtil.dest_ac ac_itm B)
        end
fun ac_atomic_filter fnm s tbl (_, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "ac_atomic_filter: ac_itm not found"
      | SOME ac_itm => not (ACUtil.head_agrees ac_itm (lookup_inst inst s))
fun term_neq_filter fnm s1 s2 tbl (id, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "term_neq_filter: ac_itm not found"
      | SOME ac_itm =>
        let
          val (A, B) = (lookup_inst inst s1, lookup_inst inst s2)
          val Bs = ACUtil.dest_ac ac_itm B
        in
          not (exists (fn B' => RewriteTable.is_equiv id tbl (A, B')) Bs)
        end
fun subset_var_filter s1 s2 _ (_, inst) =
    subset (op aconv) (map Var (Term.add_vars (lookup_inst inst s1) []),
                       map Var (Term.add_vars (lookup_inst inst s2) []))

type id_inst2 = (box_id * ((Type.tyenv * Envir.tenv) *
                           (Type.tyenv * Envir.tenv))) * (thm * thm)
val no_prereq = fn _ => fn _ => true
val all_insts = fn _ => fn _ => true

fun merged_id rtype items =
    let
      val {lat, ...} = RewriteTable.table_of_rewrite_type rtype
      fun merge items =
          case items of
              [] => []
            | {id, ...} :: items' => BoxID.merge_boxes lat (id, merge items')
    in
      merge items
    end

(* Get ordered matchings between "pats" and "trms". *)
fun get_insts_filt pats items rtype filt =
    if length pats <> length items then
      raise AUTO2 "get_insts_filt: wrong number of arguments"
    else if exists is_implies (map get_fact items) then [] else
    let
      val trms = map get_fact items
      val pairs = map (pair false) (pats ~~ trms)
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rewrite_type rtype
      val insts = (fo_table_match_list id tbl pairs)
                      |> filter (filt tbl o fst)
                      |> RewriteTable.replace_id_for_type rtype
      val items_th = map get_thm items
      fun get_prev_ths (inst, ths) =
          (inst, map elim_eq_thm (map meta_sym ths ~~ items_th))
    in
      map get_prev_ths insts
    end

fun get_insts pats items rtype =
    get_insts_filt pats items rtype (fn _ => fn _ => true)

fun pat_prereq pat rtype item =
    let
      val pat' = if is_eq_term' pat then @{term_pat "TERM ?x"} else pat
      val rtype' = RewriteTable.single_of_rewrite_type rtype
    in
      case get_insts [pat'] [item] rtype' of
          [] => false | _ => true
    end

(* Preprocessing a theorem: write theorem th into the form [hyps] ==>
   false, match pats @ [~ pat_r] (with prop type) with hyps. Finally
   convert the ending of theorem from hyp_n -> false to ~hyp_n. The
   result is a theorem [pats] ==> pat_r.
 *)
fun preprocess_thm pats (pat_r, th) =
    let
      val pat_r_false = pat_r aconv @{prop "False"}
      val pats' = filter_out is_Term pats
      val prop_pats = if pat_r_false then pats' else pats' @ [get_neg' pat_r]
      val th' = rewrite_thm_to_contra_form th
      val prems_th' = Thm.prems_of th'
    in
      if eq_set (op aconv) (prop_pats, prems_th') then
        (pat_r, th' |> rotate_prems_conv_thm prop_pats
                    |> not pat_r_false ? rewrite_thm_from_contra_form)
      else
        let
          val thy = Thm.theory_of_thm th
          val _ = tracing ("Given in proofstep: " ^
                           (prop_pats |> pretty_terms_thy thy |> str) ^
                           "\nIn theorem: " ^
                           (prems_th' |> pretty_terms_thy thy |> str))
        in
          raise AUTO2 "preprocess_thm: premises do not agree."
        end
    end

fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val inst_new = Envir.subst_term inst pat_r
      val ths' = ths |> filter_out (is_Term o Thm.prop_of)
      val th' = th |> subst_thm ctxt inst |> fold Thm.elim_implies ths'
      val _ = assert (inst_new aconv (Thm.prop_of th'))
                     "apply_pat_r: conclusion mismatch"
    in
      th'
    end

fun retrieve_pats descs =
    let
      fun retrieve_pat desc =
          case desc of
              WithFact pat => [HOLogic.mk_Trueprop pat]
            | WithGoal pat => [HOLogic.mk_Trueprop (get_neg pat)]
            | WithTerm t => [Logic.mk_term t]
            | _ => []
    in
      maps retrieve_pat descs
    end

fun retrieve_pats_r descs =
    let
      fun retrieve_pat_r desc =
          case desc of
              GetFact (pat_r, th) => [(HOLogic.mk_Trueprop pat_r, th)]
            | GetGoal (pat_r, th) => [(HOLogic.mk_Trueprop (get_neg pat_r), th)]
            | GetResolve th => [(@{prop "False"}, th)]
            | _ => []
    in
      maps retrieve_pat_r descs
    end

fun retrieve_filts descs =
    let
      fun retrieve_filt desc =
          case desc of Filter filt => [filt] | _ => []
    in
      fold (curry (op andf2)) (maps retrieve_filt descs) all_insts
    end

fun retrieve_cases descs =
    let
      fun retrieve_case desc =
          case desc of CreateCase (assums, concls) =>
                       [(map HOLogic.mk_Trueprop assums,
                         map HOLogic.mk_Trueprop concls)]
                     | _ => []
    in
      maps retrieve_case descs
    end

(* Parameters: patterns for facts, optional pattern for conclusion,
   patterns for list of new facts.
 *)
fun gen_prfstep name descs =
    let
      val pats = retrieve_pats descs
      val pats_r = retrieve_pats_r descs |> map (preprocess_thm pats)
      val filt = retrieve_filts descs
      val cases = retrieve_cases descs

      fun pats_r_to_update ctxt (inst_ths as ((id, _), _)) =
          let
            val ths = map (apply_pat_r ctxt inst_ths) pats_r
          in
            if length ths = 1 then thm_update (id, the_single ths)
            else AddItems {id = id, raw_items = map Fact ths}
          end

      fun pat_updts ctxt insts =
          if length pats_r = 0 then [] else map (pats_r_to_update ctxt) insts

      fun case_to_update ((id, inst), _) (assums, concls) =
          AddBoxes {id = id, freevars = [],
                    assums = map (Envir.subst_term inst) assums,
                    concls = map (Envir.subst_term inst) concls}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases
      fun case_updts insts = maps cases_to_update insts

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
          in
            pat_updts ctxt insts @ case_updts insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_thm name descs th =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype _ =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt ((id, _), ths) =
                thm_update (id, ths MRS th)
                handle THM (err, _, _) =>
                       raise AUTO2CT (name ^ ": MRS failed with message " ^
                                      err, map Thm.cprop_of ths)
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_conv name descs cv =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1 andalso is_Term (the_single pats))
                     "prfstep_conv: should have exactly one term pattern."
      val filt = retrieve_filts descs
      fun prfstep items rtype {ctxt, ...} =
          let
            val tbl = RewriteTable.table_of_rewrite_type rtype
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt ((id, _), ths) =
                let
                  val ct = ths |> the_single |> Thm.prop_of |> Logic.dest_term
                               |> cert ctxt
                  val eq_th = (Conv.try_conv cv) ct
                  val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
                in
                  if lhs aconv rhs then
                    raise AUTO2CT (name ^ ": cv failed.", [ct])
                  else if RewriteTable.is_equiv id tbl (lhs, rhs) then []
                  else [Update.thm_update (id, eq_th |> to_obj_eq)]
                end
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_rrule descs rrule =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1 andalso is_Term (the_single pats))
                     "prfstep_rrule: should have exactly one term pattern."
      val pat = Logic.dest_term (the_single pats)
      val (lhs, rhs) =
          HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of rrule))
      val name = name_of_thm rrule
    in
      if Term.aconv_untyped (pat, lhs) then
        prfstep_conv name descs (Conv.rewr_conv (to_meta_eq rrule))
      else if Term.aconv_untyped (pat, rhs) then
        prfstep_conv name descs (Conv.rewr_conv (to_meta_eq (obj_sym rrule)))
      else raise AUTO2CT (
          "prfstep_rrule: pattern does not equal either side of rrule.",
          [Thm.cprop_of rrule])
    end
        
(* pat_r produces a trivial statement, which together with the item
   matching the main pattern are matched with the hypotheses of th2 to
   produce the final result.
 *)
fun prfstep_two_stage name descs th2 =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1)
                     "prfstep_two_stage: should have one pattern."
      val pats_r = retrieve_pats_r descs |> map (preprocess_thm [])
      val _ = assert (length pats_r = 1)
                     "prfstep_two_stage: should have one result."
      val pat_r = the_single pats_r
      val filt = retrieve_filts descs

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt (instsp as (id, _), ths) =
                let
                  val th = apply_pat_r ctxt (instsp, []) pat_r
                in
                  thm_update (id, (ths @ [th]) MRS th2)
                end
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_thm_fn name descs thm_fn =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt (inst_th as ((id, _), _)) =
                thm_update (id, thm_fn ctxt inst_th)
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_custom name descs updt_fn =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype st =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt inst_th = updt_fn inst_th st
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

end  (* structure ProofStep *)

open ProofStep

(* Table of proofsteps, categorized by type. *)
datatype proofstep_table
  = ProofStepTable of {
    step_a: proofstep list,
    step_aa: proofstep list}

val empty_proofstep_table =
    ProofStepTable {step_a = [], step_aa = []}

fun merge_table (ProofStepTable {step_a = a1, step_aa = aa1},
                 ProofStepTable {step_a = a2, step_aa = aa2}) =
    ProofStepTable {step_a = merge pointer_eq (a1, a2),
                    step_aa = merge pointer_eq (aa1, aa2)}

(* Table associated to the current theory. *)
structure Data =
Theory_Data (
  type T = proofstep_table;
  val empty = empty_proofstep_table;
  val extend = I;
  val merge = merge_table
)

fun add_prfstep (prfstep as {filt, ...}) = Data.map (
      fn ProofStepTable {step_a, step_aa} =>
         case length filt of
             1 => ProofStepTable {step_a = prfstep :: step_a, step_aa = step_aa}
           | 2 => ProofStepTable {step_a = step_a, step_aa = prfstep :: step_aa}
           | _ => raise AUTO2 "add_proofstep: need 1 or 2 patterns.")

fun add_gen_prfstep (name, descs) = add_prfstep (gen_prfstep name descs)
fun add_prfstep_thm (name, descs, th) = add_prfstep (prfstep_thm name descs th)
fun add_prfstep_conv (name, descs, cv) =
    add_prfstep (prfstep_conv name descs cv)
fun add_prfstep_two_stage (name, descs, th2) =
    add_prfstep (prfstep_two_stage name descs th2)
fun add_prfstep_thm_fn (name, descs, thm_fn) =
    add_prfstep (prfstep_thm_fn name descs thm_fn)
fun add_rewrite_rule (descs, rrule) = add_prfstep (prfstep_rrule descs rrule)

fun get_step_a thy =
    let val ProofStepTable {step_a, ...} = Data.get thy in step_a end
fun get_step_aa thy =
    let val ProofStepTable {step_aa, ...} = Data.get thy in step_aa end

signature LOGIC_PROOFSTEPS =
sig
  val init_logic_proofsteps: theory -> theory
end;

structure Logic_ProofSteps : LOGIC_PROOFSTEPS =
struct

fun resolve_impl items rtype st =
    let
      val ((item1 as {id = id1, ...}), item2) = the_pair items
      val (fact1, fact2) = (get_fact item1, get_fact item2)
    in
      if not (is_implies fact1) orelse is_implies fact2 then [] else
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
                         fn _ => not o is_implies o get_fact]

(* Given an assumption of the form \exists x. A, we produce an
   assumption A with x in A replaced by a free variable. To avoid name
   collisions, when the update is produced x is replaced by an
   "internal" free variable, with suffix '_'. When the update is
   applied, that internal free variable is replaced by a fresh
   variable as determined by the context.
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
                  let
                    val freevar = extract_freevar t
                  in
                    forall (fn t' => t' aconv t orelse
                                     not (occurs_free freevar t')) ts
                  end

              fun handler (t, th) =
                  let
                    val freevar = extract_freevar t
                    val ct = cert ctxt t
                    val th' = th |> Thm.implies_intr ct
                                 |> Thm.forall_intr (cert ctxt freevar)
                    val prems_exE = Thm.prems_of @{thm exE}
                    val inst =
                        pattern_match ctxt (nth prems_exE 1, Thm.prop_of th')
                    val exE_inst = subst_thm ctxt inst @{thm exE}
                  in
                    fold Thm.elim_implies [prev_th, th'] exE_inst
                  end
            in
              if detect_trivial then [] else
              [Update.AddItems {id = id,
                                raw_items = [FreeVar var, Fact new_th,
                                             Handler (patA, (ready, handler))]}]
            end)

val init_logic_proofsteps =
    fold add_gen_prfstep [
      ("and_elim",
       [WithFact @{term_pat "?P & ?Q"},
        GetFact (@{term_pat "?P::bool"}, @{thm conjunct1}),
        GetFact (@{term_pat "?Q::bool"}, @{thm conjunct2}),
        Filter (canonical_split_filter @{const_name conj} "P" "Q")]),

      ("or_elim",
       [WithFact @{term_pat "?A | ?B"},
        CreateCase ([@{term_pat "?A::bool"}], []),
        Filter (canonical_split_filter @{const_name disj} "A" "B")]),

      ("or_elim1",
       [WithFact @{term_pat "~ ?A"},
        WithFact @{term_pat "?A | ?B"},
        GetFact (@{term_pat "?B::bool"}, @{thm or_elim})]),

      ("or_elim1'",
       [WithFact @{term_pat "?A::bool"},
        WithFact @{term_pat "~ ?A | ?B"},
        GetFact (@{term_pat "?B::bool"}, @{thm or_elim'})]),

      (* To prove iff statement, first show the forward direction. *)
      ("iff_intro1",
       [WithGoal @{term_pat "(?A::bool) = ?B"},
        CreateCase ([@{term_pat "?A::bool"}], [@{term_pat "?B::bool"}])]),

      (* Second, given the forward direction A --> B, suffices to show
         the backward direction B --> A, or B & ~A ==> False.
       *)
      ("iff_intro2",
       [WithFact @{term_pat "?A --> ?B"},
        WithGoal @{term_pat "(?A::bool) = ?B"},
        GetFact (@{term_pat "?B::bool"}, @{thm iff_intro2B}),
        GetGoal (@{term_pat "?A::bool"}, @{thm iff_intro2A})]),

      ("imp_intro",
       [WithGoal @{term_pat "?A --> ?B"},
        GetFact (@{term_pat "?A::bool"}, @{thm imp_introA}),
        GetGoal (@{term_pat "?B::bool"}, @{thm imp_introB})]),

      ("resolve_prems",
       [WithFact @{term_pat "?P --> ?Q"},
        WithFact @{term_pat "?P::bool"},
        GetFact (@{term_pat "?Q::bool"}, @{thm mp})]),

      ("contradiction",
       [WithFact @{term_pat "?A::bool"},
        WithFact @{term_pat "~ ?A"},
        GetResolve @{thm imp_triv}]),

      ("by_equality",
       [WithGoal @{term_pat "(?A::?'a) = ?A"},
        GetResolve @{thm eq_triv}])

    ] #> fold add_prfstep_thm [
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
       [WithGoal @{term_pat "EX x. ?P"}],
       @{thm exists_resolve}),

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
       @{thm forall_resolve2})

    ] #> fold add_rewrite_rule [
      ([WithTerm @{term_pat "~ ~ ?P"}], @{thm HOL.nnf_simps(6)}),
      ([WithTerm @{term_pat "~ (?P & ?Q)"},
        Filter (canonical_split_filter @{const_name conj} "P" "Q")],
       @{thm de_Morgan_conj}),
      ([WithTerm @{term_pat "~ (?P | ?Q)"},
        Filter (canonical_split_filter @{const_name disj} "P" "Q")],
       @{thm de_Morgan_disj})

    ] #> fold add_prfstep_conv [
      ("exists_split",
       [WithTerm @{term_pat "EX x y. ?P & ?Q"},
        Filter (fn _ => fn (_, inst) =>
                   let
                     val var_P = Term.add_vars (lookup_inst inst "P") []
                     val var_Q = Term.add_vars (lookup_inst inst "Q") []
                   in
                     if length var_P <> 1 orelse length var_Q <> 1 then false
                     else let val ((_, i), _) = the_single var_P
                              val ((_, j), _) = the_single var_Q
                          in i = 0 andalso j = 1 end
                   end)],
       (Conv.rewr_conv @{thm exists_split})),

      ("rewrite_not_forall",
       [WithTerm @{term_pat "~ (! x. ?A)"}],
       (Conv.rewr_conv (to_meta_eq @{thm HOL.not_all})))

    ] #> fold add_prfstep [
      {name = "resolve_impl", filt = resolve_impl_filt, func = resolve_impl},
      exists_elim
    ]

end  (* structure Logic_ProofSteps. *)

val _ = Theory.setup add_logic_ac_data
val _ = Theory.setup Logic_ProofSteps.init_logic_proofsteps

signature SCORES =
sig
  val item_score: raw_item -> int
  val items_score: raw_item list -> int
  val get_score: Update.raw_update -> int
end;

structure Scores : SCORES =
struct

open Box

fun item_score ritem =
    case ritem of
        Init _ => 0
      | FreeVar _ => 10  (* cost for introducing a variable. *)
      | Handler _ => 0
      | Fact _ => if is_implies (get_fact_raw ritem) then 0
                  else size_of_term (get_fact_raw ritem)

fun items_score raw_items = Integer.sum (map item_score raw_items)

fun get_score raw_updt =
    case raw_updt of
        Update.AddItems {id, raw_items} =>
        items_score raw_items + 5 * (length id - 1)
      | Update.AddBoxes {id, assums, concls, ...} =>
        20 + Integer.sum (map size_of_term (assums @ concls)) +
        5 * (length id - 1)
      | Update.ResolveBox {...} => ~1

end  (* structure SCORES. *)

(* Proof status. Manages changes to proof status, and main loop
   carrying out proof steps and adding new proof steps to the queue.
 *)
signature PROOFSTATUS =
sig
  val check_hyps: box_id -> raw_item -> Status.status -> unit
  val resolve_box: Update.update -> Status.status -> Status.status
  val scoring: proofstep -> int -> box_item list ->
               RewriteTable.rewrite_type -> Status.status -> Update.update list
  val process_fact_prfsteps: int -> RewriteTable.rewrite_type ->
                             box_item list -> Status.status -> Status.status
  val process_fact_rewrite: box_item -> Status.status -> Status.status
  val process_fact_all: box_item -> Status.status -> Status.status
  val process_add_items: Update.update -> Status.status -> Status.status
  val process_add_boxes: Update.update -> Status.status -> Status.status
  val apply_update: Update.update -> Status.status -> Status.status
  val empty_status: Proof.context -> Status.status
  val init_status: Proof.context -> term -> Status.status
  val step: Status.status -> Status.status
  val step_until: int -> term * Status.status -> thm * Status.status
end;

structure ProofStatus : PROOFSTATUS =
struct

open Status

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

(* When a box, whether primitive or composite, is resolved, perform
   the following two actions: 1. Resolve current and all descendent
   boxes. 2. Add the appropriate fact to each of the immediate parent
   boxes.
 *)
fun resolve_box (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.ResolveBox {id, th} =>
        let
          val _ = tracing ("Finished box " ^ (string_of_box_id id) ^
                           " (" ^ (Update.source_info ctxt updt) ^ ")")
          fun update_one i st =
              let
                val cur_parent = get_parent_at_i st id i
                val ritem = get_on_resolve st id (nth id i) th
                val _ = check_hyps cur_parent ritem st
              in
                st |> add_to_queue (
                  {sc = sc, prfstep_name = "RESOLVE", source = [],
                   raw_updt = Update.AddItems
                                  {id = cur_parent, raw_items = [ritem]}})
              end
        in
          if is_box_resolved st id then st
          else st |> fold update_one (0 upto (length id) - 1)
                  |> add_resolved id
        end
      | _ => raise AUTO2 "resolve_box: wrong type of update"

fun scoring {name, func, ...} sc items rtype st =
    if is_box_resolved st (ProofStep.merged_id rtype items) then [] else
    let
      val scs = map score_of_item items
      val max_sc = fold (curry Int.max) scs sc
      val raw_updts = func items rtype st
      fun process_raw_updt raw_updt =
          {sc = Scores.get_score raw_updt + max_sc, prfstep_name = name,
           source = items, raw_updt = raw_updt}
    in
      map process_raw_updt raw_updts
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

      val cur_id = ProofStep.merged_id rtype items
      val all_ids = get_unresolved st
      val all_updts =
          if cur_id = [] then
            process_step_aa (remove (op =) [] all_ids)
          else
            process_step_aa all_ids @ maps process_step_a items
    in
      fold add_to_queue all_updts st
    end

(* Process the given rewrite fact, located in the box with the given
   ID. For each fact or conclusion in any of the current, ancestor, or
   descendent boxes, check if it contains a subterm matching the left
   side of the rewrite. If so, re-process that fact or conclusion
   under the modified chain of rewrite tables.
 *)
fun process_fact_rewrite (item as {id, sc, ...}) st =
    let
      val eq_th = to_meta_eq (get_thm item)
      val (lhs, _) = Logic.dest_equals (Thm.prop_of eq_th)
      val rtype = get_incr_type st id eq_th
      val tbl' = RewriteTable.table_of_rewrite_type rtype
      val lhs_all = RewriteTable.get_all_contains tbl' lhs
      fun contains_lhs itm =
          let val t = get_fact itm in
            if is_Term t then member (op aconv) lhs_all (Logic.dest_term t)
            else if is_implies t then false
            else member (op aconv) lhs_all (HOLogic.dest_Trueprop t)
          end

      val all_ids = get_unresolved st |> filter (
            fn id' => is_box_unresolved st (merge_boxes st (id, id')))
      val items = maps (get_facts st) all_ids |> filter contains_lhs
    in
      st |> map_rewrites (RewriteTable.add_rewrite_thm id eq_th)
         |> process_fact_prfsteps sc rtype items
    end

fun process_fact_all (item as {id, sc, ...}) (st as {ctxt, ...}) =
    let
      val fact = get_fact item
      fun qualify_term t = case t of
                               Const ("HOL.eq", _) $ _ $ _ => false
                             | Abs _ => false
                             | _ => true
      val st' =
          if is_Term fact then st
          else if is_implies fact then st else
          let
            val tbl = get_rewrite_table st
            val tbl' = RewriteTable.add_term (HOLogic.dest_Trueprop fact) tbl
            val new_trms = (RewriteTable.get_new_terms (tbl, tbl'))
                               |> filter qualify_term
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
      st' |> (if is_eq_term' fact then process_fact_rewrite item
              else process_fact_prfsteps 0 (get_init_type st') [item])
    end

fun process_add_items (updt as {sc, prfstep_name, raw_updt, ...})
                      (st as {ctxt, ...}) =
    case raw_updt of
        Update.AddItems {id, raw_items = ritems} =>
        let
          val thy = theory_of st
          val all_facts = maps (get_facts st) (get_unresolved st)
          val (ctxt', ritems') = (replace_internals_items (ctxt, ritems))
                                     |> apsnd (map (Status.normalize_ritem thy))
          val items = map (fn ritem' => mk_box_item (id, sc, ritem')) ritems'
                          |> filter_out (can_shadow_list st all_facts)
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
              val shadowed_items =
                  all_facts |> filter (can_shadow_list st items)
              val _ = if prfstep_name = "TERM" then () else
                      tracing ("Add " ^ (Update.update_info ctxt' id ritems') ^
                               " (" ^ (Update.source_info ctxt' updt) ^ ")")
              fun print_removed item' =
                  tracing ("Removed " ^ (string_of_item ctxt item') ^
                           " from box " ^ (string_of_box_id (id_of_item item')))
              val _ = if length shadowed_items = 0 then [()]
                      else map print_removed shadowed_items
              fun remove_existing (item as {id = id', ...}) =
                  map_box id' (Box.remove_item item)
              fun process_add_one_item item st =
                  st |> map_box id (Box.add_item item)
                     |> (is_fact item) ? process_fact_all item
            in
              st |> map_context (K ctxt')
                 |> fold remove_existing shadowed_items
                 |> fold process_add_one_item items
            end
        end
      | _ => raise AUTO2 "process_add_items: wrong type of update"

fun process_add_boxes (updt as {sc, raw_updt, ...}) (st as {ctxt, ...}) =
    case raw_updt of
        Update.AddBoxes {id, freevars, assums, concls} =>
        let
          val trms = assums @ (map get_neg' concls)
          val dep_ritems = map (Fact o assume_thm ctxt) trms
        in
          if box_already_exists st id dep_ritems then st else
          let
            val _ = tracing ("Add box under " ^ (string_of_box_id id) ^ " (" ^
                             (Update.source_info ctxt updt) ^ ")")
            val (prim_id, st') = add_prim_box id Box.init_box st
            val new_id = [prim_id]
            val init_assums = map (fn t => Init (t, false)) assums
            val init_concls = map (fn t => Init (get_neg' t, true)) concls
            val init_vars = map FreeVar freevars
            val init_items = map (fn ritem => mk_box_item (new_id, sc, ritem))
                                 (init_assums @ init_concls @ init_vars)
            val st'' = st' |> map_box new_id (fold Box.add_item init_items)
            val _ = tracing ((string_of_box_id new_id) ^ ": " ^
                             (Box.short_string_of_box
                                  ctxt (get_box st'' new_id)))
            val item_updt = {sc = sc, prfstep_name = "INIT_BOX", source = [],
                             raw_updt = Update.AddItems {
                               id = new_id, raw_items = dep_ritems}}
          in
            st'' |> process_add_items item_updt
          end
        end
      | _ => raise AUTO2 "process_add_boxes: wrong type of update"

fun apply_update (updt as {source, raw_updt, ...}) st =
    let
      val id = Update.target_of_update raw_updt
    in
      if is_box_resolved st id then st
      else if exists (is_item_shadowed st) source then st
      else
        st |> not (exist_box st id) ? Status.add_composite_box id
           |> (case raw_updt of
                   Update.AddItems _ => process_add_items updt
                 | Update.AddBoxes _ => process_add_boxes updt
                 | Update.ResolveBox _ => resolve_box updt)
    end

fun empty_status ctxt =
    {lat = BoxID.empty, boxes = Boxidtab.empty, queue = Updates_Heap.empty,
     rewrites = RewriteTable.empty ctxt, ctxt = ctxt}

fun init_status ctxt subgoal =
    let
      val (assums, concl) = Logic.strip_horn subgoal
      val vars = map Free (all_frees (concl :: assums))
      val raw_updt = Update.AddBoxes {
            id = [], freevars = vars, assums = assums, concls = [concl]}
    in
      empty_status ctxt |> apply_update (
        {sc = 0, prfstep_name = "INIT", source = [], raw_updt = raw_updt})
    end

fun step (st as {queue, ...}) =
    let
      val updt = Updates_Heap.min queue
                 handle List.Empty => raise AUTO2 "No more moves"
    in
      st |> delmin_from_queue |> apply_update updt
    end

fun step_until steps_max (subgoal, (st as {ctxt, ...})) =
    let
      val obj_goal = (cert ctxt subgoal) |> to_obj_conv ctxt |> rhs_of
      fun find_obj_goal queue =
          let
            val ({raw_updt, ...}, queue') =
                Updates_Heap.min_elem queue
                handle List.Empty => raise AUTO2 "step_until: goal not found"
          in
            case raw_updt of
                Update.AddItems {id = [], raw_items = [raw_item]} =>
                if get_fact_raw raw_item aconv obj_goal then
                  apply_to_thm to_meta_imp_conv (get_thm_raw raw_item)
                else find_obj_goal queue'
              | _ => find_obj_goal queue'
          end

      fun helper steps_used steps_max (st as {queue, ...}) =
          if is_box_resolved st [0] then
            let
              val _ = tracing ("Finished in " ^ (string_of_int steps_used) ^
                               " steps.")
            in
              (find_obj_goal queue, st)
            end
          else if steps_used = steps_max then
            raise AUTO2 "Maximum number of steps reached."
          else
            helper (steps_used + 1) steps_max (step st)
            handle AUTO2 "No more moves" =>
                   raise AUTO2 (
                     "No more moves (" ^ (string_of_int steps_used) ^ " used)")
    in
      helper 0 steps_max st
    end

end  (* structure ProofStatus. *)

(* Definition of AUTO2. *)
fun auto2 ctxt state =
    let
      val prop = Thm.prop_of state
      val subgoals = prop |> Logic.strip_imp_prems
    in if length subgoals = 0 then state else
       let
         val subgoal = hd subgoals
         val _ = tracing (
               "Subgoal 1 of " ^ (string_of_int (length subgoals)) ^ ":\n" ^
               (subgoal |> pretty_term ctxt |> str) ^ "\n")
         val st = ProofStatus.init_status ctxt subgoal
         val (th, st') =
             timer ("Total time: ",
                    fn _ => ProofStatus.step_until 2000 (subgoal, st))
         val _ = tracing (Status.string_of_status st')
       in
         Thm.implies_elim state th
       end
    end

fun auto2_tac ctxt = PRIMITIVE (auto2 ctxt)
