(* Definitions and basic operations on the main data structures, up to
   Status, which represents the state of the proof.
 *)

type state_val = thm

signature BOXITEM =
sig
  type retro_handler
  datatype init_type = InitAssum | InitConcl | InitVar
  datatype raw_item = Init of term * init_type
                    | FreeVar of term
                    | Handler of term * retro_handler
                    | Fact of thm
                    | MutState of state_val
  (* term * init_type (for init) *)
  val is_init_assum: term * init_type -> bool
  val is_init_concl: term * init_type -> bool
  val is_init_var: term * init_type -> bool
  (* Facts. *)
  val is_fact_raw: raw_item -> bool
  val get_thm_raw: raw_item -> thm
  val get_fact_raw: raw_item -> term
  (* Variables. *)
  val is_freevar_raw: raw_item -> bool
  val dest_freevar_raw: raw_item -> term
  (* Inits. *)
  val is_init_raw: raw_item -> bool
  val dest_init_raw: raw_item -> term * init_type
  (* Handlers. *)
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term * retro_handler
  val handler_ritems: Proof.context -> term -> retro_handler -> raw_item list
  (* MutStates. *)
  val dest_mut_state_raw: raw_item -> state_val
  (* Misc. functions. *)
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val string_of_raw_item: Proof.context -> raw_item -> string
  val replace_internals_items:
      Proof.context * raw_item list -> Proof.context * raw_item list

  type box_item
  (* Facts. *)
  val is_fact: box_item -> bool
  val get_thm: box_item -> thm
  val get_fact: box_item -> term
  val aconvi: box_item * box_item -> bool
  (* Variables. *)
  val is_freevar: box_item -> bool
  val dest_freevar: box_item -> term
  (* Inits. *)
  val is_init: box_item -> bool
  val dest_init: box_item -> term * init_type
  (* Handlers. *)
  val is_handler: box_item -> bool
  val dest_handler: box_item -> term * retro_handler
  (* MutStates. *)
  val dest_mut_state: box_item -> state_val
  (* Misc. functions. *)
  val mk_box_item: box_id * int * raw_item -> box_item
  val id_of_item: box_item -> box_id
  val score_of_item: box_item -> int
  val string_of_item: Proof.context -> box_item -> string
end;

structure BoxItem : BOXITEM =
struct

type retro_handler = (term * term list -> bool) * (term * thm -> thm)
datatype init_type = InitAssum | InitConcl | InitVar
datatype raw_item = Init of term * init_type
                  | FreeVar of term
                  | Handler of term * retro_handler
                  | Fact of thm
                  | MutState of thm

fun is_init_assum (_, ityp) = case ityp of InitAssum => true | _ => false
fun is_init_concl (_, ityp) = case ityp of InitConcl => true | _ => false
fun is_init_var (_, ityp) = case ityp of InitVar => true | _ => false
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
fun dest_mut_state_raw ritem =
    case ritem of MutState th => th
                | _ => raise AUTO2 "dest_mut_state_raw: wrong type"
fun instantiate inst ritem =
    let
      val subst = subst_atomic (map (apply2 Thm.term_of) inst)
    in
      case ritem of Init (t, b) => Init (subst t, b)
                  | FreeVar t => FreeVar (subst t)
                  | Handler (t, handler) => Handler (subst t, handler)
                  | Fact th => Fact (th |> Thm.instantiate ([], inst)
                                        |> send_concrete_to_hyps)
                  | MutState th => MutState (th |> Thm.instantiate ([], inst)
                                                |> send_concrete_to_hyps)
    end
fun string_of_raw_item ctxt ritem =
    let val trm = case ritem of
                      Init (t, _) => t
                    | FreeVar t => t
                    | Handler (t, _) => t
                    | Fact _ => get_fact_raw ritem
                    | MutState th => Thm.prop_of th
    in trm |> pretty_term ctxt |> str end

(* Given a context and list of raw items, replace internal variables
   declared in the list and used in the terms in the list by fresh
   variables from context, and declare those variables in context.
 *)
fun replace_internals_items (ctxt, ritems) =
    let
      (* Original internal variables. *)
      val all_vars =
          ritems |> filter is_freevar_raw |> map dest_freevar_raw
                 |> filter is_Var |> map dest_Var
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
fun is_fact {ritem, ...} = is_fact_raw ritem
fun get_thm {ritem, ...} = get_thm_raw ritem
fun get_fact {ritem, ...} = get_fact_raw ritem
fun aconvi (item1, item2) = get_fact item1 aconv get_fact item2
fun is_freevar {ritem, ...} = is_freevar_raw ritem
fun dest_freevar {ritem, ...} = dest_freevar_raw ritem
fun is_init {ritem, ...} = is_init_raw ritem
fun dest_init {ritem, ...} = dest_init_raw ritem
fun is_handler {ritem, ...} = is_handler_raw ritem
fun dest_handler {ritem, ...} = dest_handler_raw ritem
fun dest_mut_state {ritem, ...} = dest_mut_state_raw ritem
fun mk_box_item (id, sc, ritem) = {id = id, sc = sc, ritem = ritem}
fun id_of_item {id, ...} = id
fun score_of_item {sc, ...} = sc
fun string_of_item ctxt {ritem, ...} = string_of_raw_item ctxt ritem

end  (* structure BoxItem. *)

open BoxItem

signature UPDATE =
sig
  datatype raw_update
    = AddItems of {id: box_id, raw_items: raw_item list}
    | AddMutState of {id: box_id, mut_type: string, sval: state_val}
    | AddBoxes of {id: box_id, freevars: term list, assums: term list,
                   concls: term list, cb: box_id * thm -> raw_update list}
    | ResolveBox of {id: box_id, th: thm}
  type resolve_callback
  type update
  val null_callback: resolve_callback
  val thm_update: box_id * thm -> raw_update
  val apply_horn_clause: box_id * thm -> resolve_callback -> raw_update list
  val target_of_update: raw_update -> box_id
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: Proof.context -> update -> string
end;

structure Update : UPDATE =
struct

datatype raw_update
  = AddItems of {id: box_id, raw_items: raw_item list}
  | AddMutState of {id: box_id, mut_type: string, sval: state_val}
  | AddBoxes of {id: box_id, freevars: term list, assums: term list,
                 concls: term list, cb: box_id * thm -> raw_update list}
  | ResolveBox of {id: box_id, th: thm}
type resolve_callback = box_id * thm -> raw_update list
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

val null_callback = K []

fun thm_update (id, th) =
    if Thm.prop_of th aconv @{prop "False"} then ResolveBox {id = id, th = th}
    else AddItems {id = id, raw_items = [Fact th]}

fun apply_horn_clause (id, th) cb =
    case Thm.prop_of th of
        Const ("Pure.imp", _) $ A $ _ =>
        let
          val (vars, body) = strip_obj_all_var (HOLogic.dest_Trueprop A)
          val (assums, concl) = (strip_obj_imp body)
                                    |> apfst (map HOLogic.mk_Trueprop)
                                    |> apsnd HOLogic.mk_Trueprop
          fun callback (id', th_fst) =
              apply_horn_clause (id', [th_fst] MRS th) cb
        in
          [AddBoxes {id = id, freevars = vars, assums = assums,
                     concls = [concl], cb = callback}]
        end
      | _ => if pointer_eq (cb, null_callback) then [thm_update (id, th)]
             else cb (id, th)

fun target_of_update raw_updt =
    case raw_updt of
        AddItems {id, ...} => id
      | AddMutState {id, ...} => id
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

signature BOX =
sig
  type box
  val init_box: box
  val add_item: box_item -> box -> box
  val remove_item: box_item -> box -> box
  val add_callback: Update.resolve_callback -> box -> box
  val get_callbacks: box -> Update.resolve_callback list
  val get_items: box -> box_item list
  val get_facts: box -> box_item list
  val get_init_facts: box -> (term * init_type) list
  val get_freevars: box -> term list
  val get_init_vars: box -> term list
  val get_dep_vars: box -> term list
  val get_handlers: box -> (term * retro_handler) list
  val string_of_box: Proof.context -> box -> string
  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct

type box = {items: box_item list, cbs: Update.resolve_callback list}
val init_box = {items = [], cbs = []}
fun add_item item {items, cbs} = {items = cons item items, cbs = cbs}
fun remove_item item {items, cbs} =
    {items = remove pointer_eq item items, cbs = cbs}
fun add_callback cb {items, cbs} =
    {items = items,
     cbs = if pointer_eq (cb, Update.null_callback) then cbs else cons cb cbs}
fun get_callbacks {cbs, ...} = cbs

fun get_items {items, ...} = items
val get_facts = filter is_fact o get_items
(* Return initial facts and variables in the order added. *)
fun get_init_facts box =
    (get_items box) |> filter is_init |> map dest_init
                    |> filter_out is_init_var |> rev
val get_freevars = map dest_freevar o filter is_freevar o get_items
fun get_init_vars box =
    (get_items box) |> filter is_init |> map dest_init
                    |> filter is_init_var |> map fst |> rev
fun get_dep_vars box =
    subtract (op aconv) (get_init_vars box) (get_freevars box)
val get_handlers = map dest_handler o filter is_handler o get_items

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

structure Updates_Heap =
Heap (
  type elem = Update.update
  fun ord ({sc = sc1, ...}, {sc = sc2, ...}) = int_ord (sc1, sc2)
)

signature STATUS =
sig
  type status
  val empty_status: Proof.context -> status
  val theory_of: status -> theory
  val normalize_ritem: Proof.context -> raw_item -> raw_item list
  val exist_box: status -> box_id -> bool
  val get_box: status -> box_id -> Box.box
  val get_rewrite_table: status -> RewriteTable.rewrite_table
  val get_init_type: status -> RewriteTable.rewrite_type
  val get_incr_type: status -> box_id -> thm -> RewriteTable.rewrite_type

  val get_lattice: status -> BoxID.box_lattice
  val get_focus: status -> box_id
  val set_focus: box_id -> status -> status
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
  val map_mut_states:
      string -> (box_item list -> box_item list) -> status -> status
  val add_mut_state: string -> box_item -> status -> status
  val del_mut_state: string -> box_item -> status -> status
  val get_mut_state_types: status -> string list
  val get_mut_states: status -> string -> box_item list
  val add_shadowed: box_id * term -> status -> status
  val query_shadowed: status -> box_id * term -> bool
  val add_prim_box: box_id -> Box.box -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_all_ids: status -> box_id list
  val get_resolved: status -> box_id list
  val get_unresolved: status -> box_id list
  val get_ancestors: status -> box_id -> box_id list
  val add_composite_box: box_id -> status -> status

  val get_facts: status -> box_id -> box_item list
  val get_init_facts: status -> box_id -> (term * init_type) list
  val get_init_vars: status -> box_id -> term list
  val get_dep_vars: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term * retro_handler) list
  val get_all_facts: status -> box_id -> box_item list
  val get_all_init_facts: status -> box_id -> (term * init_type) list
  val get_all_init_vars: status -> box_id -> term list
  val get_all_dep_vars: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term * retro_handler) list

  val find_fact: status -> box_id -> term -> (box_item * thm) option
  val is_triv_eq: status -> box_id -> box_item -> bool
  val shadow_ids: status -> box_item -> box_item -> box_id list
  val shadow_list_ids: status -> box_item list -> box_item -> box_id list
  val is_item_shadowed: status -> box_item list -> box_item -> bool
  val is_item_removed: status -> box_item -> bool
  val invoke_handler: term * retro_handler -> thm -> thm
  val invoke_handlers: (term * retro_handler) list -> thm -> thm
  val get_neg_form: Proof.context -> (term * init_type) list -> term
  val get_neg_form_thm: Proof.context -> (term * init_type) list * thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> raw_item
  val find_prim_box: status -> box_id -> term list -> box_id option
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
  shadowed: (box_id list) Termtab.table,
  mut_states: (box_item list) Symtab.table,
  queue: Updates_Heap.T,
  rewrites: RewriteTable.rewrite_table,
  ctxt: Proof.context
}

fun empty_status ctxt =
    {lat = BoxID.empty, boxes = Boxidtab.empty, shadowed = Termtab.empty,
     mut_states = Symtab.empty, queue = Updates_Heap.empty,
     rewrites = RewriteTable.empty ctxt, ctxt = ctxt}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

(* Perform some preliminary simplifications. *)
fun normalize_ritem ctxt ritem =
    case ritem of
        Fact th =>
        if (is_Term orf has_vars) (Thm.prop_of th) then [Fact th]
        else th |> normalize ctxt |> map Fact
      | _ => [ritem]

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
val get_focus = BoxID.get_focus o get_lattice
val get_parent_prim = BoxID.get_parent_prim o get_lattice
val get_parent_at_i = BoxID.get_parent_at_i o get_lattice
val merge_boxes = BoxID.merge_boxes o get_lattice
val is_ancestor = BoxID.is_ancestor o get_lattice
val is_descendent = BoxID.is_descendent o get_lattice
val is_eq_ancestor = BoxID.is_eq_ancestor o get_lattice
val is_eq_descendent = BoxID.is_eq_descendent o get_lattice
val is_box_resolved = BoxID.is_box_resolved o get_lattice
val is_box_unresolved = BoxID.is_box_unresolved o get_lattice

fun map_box id f {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat, boxes = Boxidtab.map_entry id f boxes, shadowed = shadowed,
     mut_states = mut_states, queue = queue, rewrites = rewrites, ctxt = ctxt}

fun map_context f {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, shadowed = shadowed, mut_states = mut_states,
     queue = queue, rewrites = rewrites |> RewriteTable.map_context f,
     ctxt = f ctxt}

fun map_rewrites f {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, shadowed = shadowed, mut_states = mut_states,
     queue = queue, rewrites = f rewrites, ctxt = ctxt}

fun map_mut_states
        mut_type f {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, shadowed = shadowed,
     mut_states = mut_states |> Symtab.map_default (mut_type, []) f,
     queue = queue, rewrites = rewrites, ctxt = ctxt}

fun add_mut_state mut_type mut_item =
    map_mut_states mut_type (cons mut_item)

fun del_mut_state mut_type mut_state =
    map_mut_states mut_type (remove pointer_eq mut_state)

fun get_mut_state_types {mut_states, ...} = Symtab.keys mut_states

fun get_mut_states {mut_states, ...} mut_type =
    the_default [] (Symtab.lookup mut_states mut_type)

fun add_shadowed
        (id, t)
        (st as {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt}) =
    let
      val ids_t = (id :: the_default [] (Termtab.lookup shadowed t))
                      |> max_partial (is_eq_ancestor st)
    in
      {lat = lat, boxes = boxes,
       shadowed = shadowed |> Termtab.update (t, ids_t),
       mut_states = mut_states, queue = queue, rewrites = rewrites, ctxt = ctxt}
    end

fun query_shadowed (st as {shadowed, ...}) (id, t) =
    exists (is_eq_descendent st id)
           (the_default [] (Termtab.lookup shadowed t))

fun add_prim_box parent_id new_box
                 {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    let
      val (id, lat') = BoxID.add_prim_id parent_id lat
    in
      (id, {lat = lat',
            boxes = Boxidtab.update_new ([id], new_box) boxes,
            shadowed = shadowed,
            mut_states = mut_states,
            queue = queue,
            rewrites = RewriteTable.map_lat (K lat') rewrites,
            ctxt = ctxt})
    end

fun set_focus foc {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat |> BoxID.set_focus foc, boxes = boxes, shadowed = shadowed,
     mut_states = mut_states, queue = queue,
     rewrites = rewrites |> RewriteTable.map_lat (BoxID.set_focus foc),
     ctxt = ctxt}

fun add_resolved id {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    let
      val lat' = BoxID.add_resolved id lat
    in
      {lat = lat', boxes = boxes, shadowed = shadowed, mut_states = mut_states,
       queue = queue, rewrites = RewriteTable.map_lat (K lat') rewrites,
       ctxt = ctxt}
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
fun add_composite_box
        id (st as {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt}) =
    let
      val new_box = Box.init_box
    in
      if exist_box st id then
        raise AUTO2 "Try to add a composite box that already exists"
      else if length id = 1 then
        raise AUTO2 "Try to add a primitive box as a composite"
      else
        {lat = lat, boxes = Boxidtab.update_new (id, new_box) boxes,
         shadowed = shadowed, mut_states = mut_states, queue = queue,
         rewrites = rewrites, ctxt = ctxt}
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

(* Try to find a box_item at id or ancestors whose term is equivalent
   to t. Return SOME (item, eq) if found, where item has proposition
   t' and eq is t' = t. Otherwise return NONE.
 *)
fun find_fact st id t =
    let
      val tbl = get_rewrite_table st
      fun process_item item =
          let
            val t' = get_fact item
            val eq_info = (RewriteTable.equiv_info tbl id (t', t))
                              |> filter (fn (id', _) => id = id')
          in
            case eq_info of
                [] => NONE
              | (_, eq_th) :: _ => SOME (item, eq_th)
          end
    in
      get_first process_item (get_all_facts st id)
    end

(* Whether item (which may be in another id) is a trivial equality
   when considered in the given id.
 *)
fun is_triv_eq st id item =
    if not (is_fact item orelse is_init item) then false else
    let
      val fact = if is_fact item then get_fact item else dest_init item |> fst
    in
      if not (is_all_eq_term' fact) then false
      else
        RewriteTable.is_equiv
            id (get_rewrite_table st)
            (fact |> HOLogic.dest_Trueprop |> dest_all_eq)
    end

(* Return the list of ids under which item2 will be extraneous because
   of item1.
 *)
fun shadow_ids st (item1 as {id = id1, ...}) (item2 as {id = id2, ...}) =
    if not (is_fact item1) orelse not (is_fact item2) then [] else
    let
      val tbl = get_rewrite_table st
      val (fact1, fact2) = (apply2 get_fact) (item1, item2)
      val id = merge_boxes st (id1, id2)

      (* Situations where item2 is redundant because it is the same as
         item1. For two items that are in non-comparable ids, we have
         to be careful not to eliminate both in the common id. For
         this, we eliminate the item in the larger id (according to
         list_ord int_ord).
       *)
      fun compare_id id1 id2 =
          if id1 = id2 then EQUAL
          else if is_ancestor st id1 id2 then LESS
          else if is_descendent st id1 id2 then GREATER
          else (list_ord int_ord) (id1, id2)

      val equiv_ids =
          if compare_id id1 id2 = GREATER orelse
             (id1 = id2 andalso Term_Ord.termless (fact2, fact1)) then []
          else if has_vars fact1 orelse has_vars fact2 then
            if fact1 aconv fact2 then [id] else []
          else if is_Term fact1 andalso is_Term fact2 then
            subequiv_ids id tbl (Logic.dest_term fact1, Logic.dest_term fact2)
          else if is_Trueprop fact1 andalso is_Trueprop fact2 then
            (* Redundant if fact1 and fact2 are equivalent, except if
               one of them is an equality and the other is not, since
               equality is treated differently (works with eq_elim
               proofstep).
             *)
            if is_eq_term' fact1 andalso not (is_eq_term' fact2) then [] else
            if is_eq_term' fact2 andalso not (is_eq_term' fact1) then [] else
            equiv_ids id tbl (HOLogic.dest_Trueprop fact1,
                              HOLogic.dest_Trueprop fact2)
          else []
    in
      max_partial (is_eq_ancestor st) equiv_ids
    end

(* Return the list of ids under which item will be extraneous because
   of one of the elements of items.
 *)
fun shadow_list_ids st items item =
    maps (fn item' => shadow_ids st item' item) items
         |> max_partial (is_eq_ancestor st)

(* Whether item is shadowed by the list items in its own id. *)
fun is_item_shadowed st items (item as {id, ...}) =
    member (op =) (shadow_list_ids st items item) id

(* Determine whether the given item is already removed from st (due to
   an item with the same term in an ancestor box).
 *)
fun is_item_removed st (item as {id, ...}) =
    not ((exist_box st id andalso
          member pointer_eq (Box.get_items (get_box st id)) item) orelse
         member pointer_eq (maps (get_mut_states st) (get_mut_state_types st))
                item)

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
      val neg_concls = inits |> filter is_init_concl |> map fst
      val facts = inits |> filter is_init_assum |> map fst
      val freevars = inits |> filter is_init_var |> map (dest_Free o fst)
      fun mk_all (nm, T) t = Logic.all_const T $ Term.absfree (nm, T) t
      val prop = @{prop False}
    in
      if length (facts @ neg_concls) = 0 then @{prop False} else
      (* Fold in reverse order, so the facts appear in the right order
         in imps.
       *)
      prop |> fold (curry Logic.mk_implies) (rev (facts @ neg_concls))
           |> cert ctxt
           |> rewrite_from_contra_form |> rhs_of
           |> fold mk_all (rev freevars) |> cert ctxt
           |> to_obj_conv ctxt |> rhs_of
    end

(* Given a theorem th with trms in the hypothesis, return a new
   theorem with trms pulled into the proposition of th, which is
   rewritten into a more human readable form.
 *)
fun get_neg_form_thm ctxt (inits, th) =
    let
      val neg_concls = inits |> filter is_init_concl |> map (cert ctxt o fst)
      val facts = inits |> filter is_init_assum |> map (cert ctxt o fst)
      val freevars = inits |> filter is_init_var |> map (cert ctxt o fst)
      val _ = assert (Thm.prop_of th aconv @{prop False})
                     "get_neg_form_thm: input should have prop False."
    in
      (* Fold in reverse order, so the facts appear in the right order
         in imps.
       *)
      th |> fold Thm.implies_intr (rev (facts @ neg_concls))
         |> rewrite_thm_from_contra_form
         |> fold Thm.forall_intr (rev freevars)
         |> apply_to_thm (to_obj_conv ctxt)
    end

(* Derive the consequence if box full_id is resolved, to the parent id
   formed by getting parent at prim_id.
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
      val init_vars = map (rpair InitVar) (get_init_vars st [prim_id])
      val inits = (if prim_id = 0 then init_facts else init_facts @ init_vars)
      val th'' = get_neg_form_thm ctxt (inits, th')
      val _ = if prim_id = 0 then
                assert (length (Thm.hyps_of th'') = 0)
                       "get_on_resolve: did not remove all hypothesis at box 0."
              else ()
      val _ = assert (Thm.prop_of th'' aconv get_neg_form ctxt inits)
                     "get_on_resolve: wrong value from get_neg_form_thm."
    in
      Fact th''
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box st id inits =
    let
      fun agree_inits inits' =
          eq_list (op aconv) (inits |> sort Term_Ord.term_ord, inits')
      fun agree_at_id id' =
          agree_inits (
            get_init_facts st id' |> map fst |> sort Term_Ord.term_ord)

      fun can_test_id id' =
          case id' of
              [prim_id'] => is_eq_ancestor st (get_parent_prim st prim_id') id
            | _ => false

      val ids_to_test = get_unresolved st |> filter can_test_id
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {lat, boxes, shadowed, mut_states, queue, rewrites, ctxt} =
    {lat = lat, boxes = boxes, shadowed = shadowed, mut_states = mut_states,
     queue = f queue, rewrites = rewrites, ctxt = ctxt}

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
