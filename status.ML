(* Definition of updates and proof status. *)

datatype update_type = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
datatype raw_update
  = AddItems of {id: box_id, sc: int option, raw_items: raw_item list}
  | AddBoxes of {id: box_id, sc: int option, init_assum: term}
  | ResolveBox of {id: box_id, th: thm}
  | ShadowItem of {id: box_id, item: box_item}
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

fun target_of_update raw_updt =
    case raw_updt of
        AddItems {id, ...} => id
      | AddBoxes {id, ...} => id
      | ResolveBox {id, ...} => id
      | ShadowItem {id, ...} => id

signature UPDATE =
sig
  val type_of_update: raw_update -> update_type
  val string_of_update_type: update_type -> string
  val string_of_raw_update: Proof.context -> raw_update -> string
  val thm_to_ritem: thm -> raw_item
  val thm_update: box_id * thm -> raw_update

  val apply_exists_ritems: Proof.context -> thm -> raw_item list * thm
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: update -> string
end;

structure Update : UPDATE =
struct

fun type_of_update raw_updt =
    case raw_updt of
        AddItems _ => ADD_ITEMS
      | AddBoxes _ => ADD_BOXES
      | ResolveBox _ => RESOLVE_BOX
      | ShadowItem _ => SHADOW_ITEM

fun string_of_update_type updt_ty =
    case updt_ty of
        ADD_ITEMS => "ADD_ITEMS"
      | ADD_BOXES => "ADD_BOXES"
      | RESOLVE_BOX => "RESOLVE_BOX"
      | SHADOW_ITEM => "SHADOW_ITEM"

fun string_of_raw_update ctxt raw_updt =
    case raw_updt of
        AddItems {id, raw_items, ...} =>
        "Add items " ^ (Util.string_of_list (
                           ItemIO.string_of_raw_item ctxt) raw_items) ^
        " to box " ^ (BoxID.string_of_box_id id)
      | AddBoxes {id, init_assum, ...} =>
        "Add box " ^ (Syntax.string_of_term ctxt init_assum) ^
        " under box " ^ (BoxID.string_of_box_id id)
      | ResolveBox {id, ...} =>
        "Resolve box " ^ (BoxID.string_of_box_id id)
      | ShadowItem {id, item} =>
        "Shadow item " ^ (ItemIO.string_of_item ctxt item) ^
        " in box " ^ (BoxID.string_of_box_id id)

fun thm_to_ritem th =
    let
      val prop = Thm.prop_of th
      val _ = assert (is_Trueprop prop) "thm_update: prop is not Trueprop."
      val _ = assert (not (Util.has_vars prop))
                     "thm_update: prop contains schematic variables."
    in
      Fact (TY_PROP, [dest_Trueprop prop], th)
    end

fun thm_update (id, th) =
    if Thm.prop_of th aconv pFalse then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, sc = NONE, raw_items = [thm_to_ritem th]}

(* Apply the given existence theorem and return the list of resulting ritems.
 *)
fun apply_exists_ritems ctxt ex_th =
    let
      val (vars, body) = (UtilLogic.strip_exists (prop_of' ex_th))
                            |> Util.replace_vars ctxt
                            |> Util.replace_internal_vars
                            |> apsnd mk_Trueprop
    in
      if null vars then ([], ex_th)
      else (map (BoxItem.var_to_fact) vars @ [Handler (vars, body, ex_th)],
            Thm.assume (Thm.cterm_of ctxt body))
    end

fun update_info ctxt id ritems =
    (Util.string_of_list' (ItemIO.string_of_raw_item ctxt)
                     (filter (not o BoxItem.is_handler_raw) ritems)) ^
    " at box " ^ (BoxID.string_of_box_id id)

fun uid_string_of_item {uid, ...} = "(" ^ string_of_int uid ^ ")"

fun source_info {prfstep_name, source, ...} =
    prfstep_name ^ " on " ^ (Util.string_of_list' (uid_string_of_item) source)

end  (* structure Update. *)

type box = {init_assum: term,
            handlers: (term list * term * thm) list,
            items: (box_item * box_id list) Inttab.table}

signature BOX =
sig
  val init_box: term -> box
  val get_init_assum: box -> term

  val add_handler: term list * term * thm -> box -> box
  val get_handlers: box -> (term list * term * thm) list

  val map_items: ((box_item * box_id list) Inttab.table ->
                  (box_item * box_id list) Inttab.table) -> box -> box
  val add_item: box_item -> box -> box
  val is_item_removed: box_item * box_id list -> bool
  val get_items: bool -> box -> box_item list
  val lookup_item: box -> int -> (box_item * box_id list) option
  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct

fun init_box init_assum =
    {init_assum = init_assum, handlers = [], items = Inttab.empty}
fun get_init_assum {init_assum, ...} = init_assum

fun add_handler (vars, t, ex_th) {init_assum, handlers, items} =
    {init_assum = init_assum, handlers = cons (vars, t, ex_th) handlers,
     items = items}
fun get_handlers {handlers, ...} = handlers

fun map_items f {init_assum, handlers, items} =
    {init_assum = init_assum, handlers = handlers, items = f items}

fun add_item (item as {uid, ...}) box =
    map_items (Inttab.update_new (uid, (item, []))) box
    handle Inttab.DUP _ => raise Fail "add_item: item already exists."

fun is_item_removed ({id, ...}, shadow_ids) =
    member (op =) shadow_ids id

fun get_items incl_removed {items, ...} =
    items |> Inttab.dest |> map snd
          |> (if incl_removed then I else filter_out is_item_removed)
          |> map fst

fun lookup_item {items, ...} uid =
    Inttab.lookup items uid

fun short_string_of_box ctxt {init_assum, ...} =
    Syntax.string_of_term ctxt init_assum

end  (* structure Box. *)

structure Updates_Heap =
Heap (
  type elem = update
  fun ord ({sc = sc1, raw_updt = ru1, ...}, {sc = sc2, raw_updt = ru2, ...}) =
      prod_ord int_ord (list_ord int_ord)
               ((sc1, target_of_update ru1), (sc2, target_of_update ru2))
)

type status = {
  uid_next: int,
  boxes: box Boxidtab.table,
  queue: Updates_Heap.T,
  resolve_th: thm option,
  ctxt: Proof.context
}

signature STATUS =
sig
  val empty_status: Proof.context -> status
  val theory_of: status -> theory
  val exist_box: status -> box_id -> bool
  val get_box: status -> box_id -> box

  val incr_uid: int -> status -> status
  val map_box: box_id -> (box -> box) -> status -> status
  val map_context: (Proof.context -> Proof.context) -> status -> status
  val set_resolve_th: thm -> status -> status
  val get_resolve_th: status -> thm
  val add_prim_box: box_id -> box -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_all_ids: status -> box_id list
  val get_resolved: status -> box_id list
  val get_unresolved: status -> box_id list
  val get_eq_ancestors: status -> box_id -> box_id list
  val add_composite_box: box_id -> status -> status

  val get_items: bool -> status -> box_id -> box_item list
  val get_init_assums: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term list * term * thm) list
  val get_all_items: bool -> status -> box_id -> box_item list
  val get_all_init_assums: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term list * term * thm) list
  val add_item: box_item -> status -> status
  val add_handler: box_id -> term list * term * thm -> status -> status
  val lookup_item: status -> box_id -> int -> (box_item * box_id list) option
  val lookup_item_all: status -> box_id -> int -> (box_item * box_id list) list
  val add_shadowed: box_id * box_item -> status -> status
  val query_shadowed: status -> box_id -> box_item -> bool
  val query_removed: status -> box_item -> bool

  val find_fact: status -> box_id -> term -> thm option
  val find_ritem_exact: status -> box_id -> raw_item -> bool
  val invoke_handler: Proof.context -> term list * term * thm -> thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> thm
  val find_prim_box: status -> box_id -> term -> box_id option
  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: update -> status -> status
  val delmin_from_queue: status -> status
end;

structure Status : STATUS =
struct

fun empty_status ctxt =
    {uid_next = 1, boxes = Boxidtab.empty, queue = Updates_Heap.empty,
     ctxt = ctxt, resolve_th = NONE}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id =
    the (Boxidtab.lookup boxes id)
    handle Option.Option => raise Fail "get_box: id not found."

fun incr_uid n {uid_next, boxes, queue, ctxt, resolve_th} =
    {uid_next = uid_next + n, boxes = boxes, queue = queue, ctxt = ctxt,
     resolve_th = resolve_th}

fun map_box id f {uid_next, boxes, queue, ctxt, resolve_th} =
    {uid_next = uid_next, boxes = Boxidtab.map_entry id f boxes,
     queue = queue, ctxt = ctxt, resolve_th = resolve_th}

fun map_context f {uid_next, boxes, queue, ctxt, resolve_th} =
    {uid_next = uid_next, boxes = boxes, queue = queue, ctxt = f ctxt,
     resolve_th = resolve_th}

fun set_resolve_th th {uid_next, boxes, queue, ctxt, ...} =
    {uid_next = uid_next, boxes = boxes, queue = queue, ctxt = ctxt,
     resolve_th = SOME th}

fun get_resolve_th {resolve_th, ...} =
    case resolve_th of
        NONE => raise Fail "get_resolve_th: not resolved."
      | SOME th => th

fun add_prim_box parent_id new_box {uid_next, boxes, queue, ctxt, resolve_th} =
    let
      val (id, ctxt') = BoxID.add_prim_id parent_id ctxt
    in
      (id, {uid_next = uid_next,
            boxes = Boxidtab.update_new ([id], new_box) boxes, queue = queue,
            ctxt = ctxt', resolve_th = resolve_th})
    end

fun add_resolved id {uid_next, boxes, queue, ctxt, resolve_th} =
    let
      val ctxt' = BoxID.add_resolved id ctxt
    in
      {uid_next = uid_next, boxes = boxes, queue = queue,
       ctxt = ctxt' |> RewriteTable.clean_resolved id
                    |> PropertyData.clean_resolved id
                    |> WellformData.clean_resolved id
                    |> Auto2Data.invoke_clean_resolved id,
       resolve_th = resolve_th}
    end

fun get_all_ids {boxes, ...} = Boxidtab.keys boxes
fun get_resolved (st as {ctxt, ...}) =
    filter (BoxID.is_box_resolved ctxt) (get_all_ids st)
fun get_unresolved (st as {ctxt, ...}) =
    filter_out (BoxID.is_box_resolved ctxt) (get_all_ids st)

(* Returns list of generalized boxes currently in st that are
   eq-ancestors of id. Note if id is unresolved, then all ancestors of
   id must be unresolved.
 *)
fun get_eq_ancestors (st as {ctxt, ...}) id =
    filter (BoxID.is_eq_descendent ctxt id) (get_unresolved st)

(* Add box with the given composite id to status. Assuming this ID is
   not already present in status.
 *)
fun add_composite_box id (st as {uid_next, boxes, queue, ctxt, resolve_th}) =
    if exist_box st id then
      raise Fail "Try to add a composite box that already exists"
    else if length id = 1 then
      raise Fail "Try to add a primitive box as a composite"
    else
      {uid_next = uid_next,
       boxes = Boxidtab.update_new (id, Box.init_box pFalse) boxes,
       queue = queue, ctxt = ctxt, resolve_th = resolve_th}

fun get_for_box f st id = if exist_box st id then f (get_box st id) else []
fun get_all_for_box f st id = maps (get_for_box f st) (get_eq_ancestors st id)
fun get_items b     = get_for_box (Box.get_items b)
val get_init_assums = get_for_box (fn box => [Box.get_init_assum box])
val get_handlers    = get_for_box Box.get_handlers
fun get_all_items b     = get_all_for_box (Box.get_items b)
val get_all_init_assums = get_all_for_box (fn box => [Box.get_init_assum box])
val get_all_handlers    = get_all_for_box Box.get_handlers

fun add_item (item as {id, ...}) = map_box id (Box.add_item item)

fun add_handler id handler = map_box id (Box.add_handler handler)

fun lookup_item st id uid =
    Box.lookup_item (get_box st id) uid

fun lookup_item_all st id uid =
    maps (fn id => the_list (lookup_item st id uid)) (get_eq_ancestors st id)

fun add_shadowed (shadow_id, {uid, id, ...}) (st as {ctxt, ...}) =
    case lookup_item st id uid of
        NONE => raise Fail "add_shadowed: item not found."
      | SOME (item, shadow_ids) =>
        let
          val shadow_ids' = (shadow_id :: shadow_ids)
                                |> Util.max_partial (BoxID.is_eq_ancestor ctxt)
        in
          map_box id (
            Box.map_items (Inttab.update (uid, (item, shadow_ids')))) st
        end

fun query_shadowed (st as {ctxt, ...}) shadow_id {uid, id, ...} =
    case lookup_item st id uid of
        NONE => raise Fail "query_shadowed: item not found."
      | SOME (_, shadow_ids) =>
        exists (BoxID.is_eq_descendent ctxt shadow_id) shadow_ids

fun query_removed st (item as {id, ...}) = query_shadowed st id item

(* Try to find fact at id or above with the proposition t. Return SOME
   th if found.
 *)
fun find_fact (st as {ctxt, ...}) id t =
    let
      val ct = Thm.cterm_of ctxt t
      val items = get_all_items false st id
      val res = (WellformData.find_fact ctxt items (id, ct))
                    |> filter (fn (id', _) => id' = id)
    in
      case res of
          [] => NONE
        | (_, th) :: _ => SOME th
    end

(* Find item with the exact ty_str and tname, whose id is an
   eq-ancestor of the given id.

   There are two special cases: if the ritem in question is of type EQ
   and PROPERTY, in which case we try to find it in the rewrite table.
 *)
fun find_ritem_exact (st as {ctxt, ...}) id ritem =
    case ritem of
        Handler _ => false
      | Fact (ty_str, tname, _) =>
        if ty_str = TY_EQ then
          let
            val (lhs, rhs) = the_pair (BoxItem.get_tname_raw ritem)
          in
            RewriteTable.is_equiv_t id ctxt (lhs, rhs)
          end
        else if ty_str = TY_PROPERTY then
          let
            val prop = the_single tname
            val infos =
                (PropertyData.get_property_t ctxt (id, prop))
                    |> filter (fn (id', _) => BoxID.is_eq_ancestor ctxt id' id)
          in
            length infos > 0
          end
        else
          let
            fun eq_item {ty_str = ty2, tname = ts2, ...} =
                ty_str = ty2 andalso
                eq_list (op aconv) (tname, map Thm.term_of ts2)
          in
            exists eq_item (get_all_items true st id)
          end

(* Invoke a single handler (vars, t, ex_th) on the theorem th. *)
fun invoke_handler ctxt (vars, t, ex_th) th =
    if member (op aconv) (Thm.hyps_of th) t then
      th |> Thm.implies_intr (Thm.cterm_of ctxt t)
         |> fold (UtilLogic.ex_elim ctxt) (rev vars)
         |> Thm.elim_implies ex_th
    else th

(* Derive the consequence if box id is resolved, to the parent id
   formed by getting parent at index i.
 *)
fun get_on_resolve (st as {ctxt, ...}) id i th =
    let
      (* First get list of handlers to invoke. *)
      val prim_id = nth id i
      val retro_ids = (get_unresolved st)
                          |> filter (BoxID.is_eq_ancestor ctxt [prim_id])
                          |> filter (BoxID.is_eq_descendent ctxt id)
      val handlers = maps (get_handlers st) retro_ids
      val init_assum = the_single (get_init_assums st [prim_id])
      val th' = th |> fold (invoke_handler ctxt) handlers
                   |> Thm.implies_intr (Thm.cterm_of ctxt init_assum)
                   |> apply_to_thm UtilLogic.rewrite_from_contra_form
      val _ = assert (prim_id <> 0 orelse null (Thm.hyps_of th'))
                     "get_on_resolve: did not remove all hypothesis at box 0."
    in
      th'
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box (st as {ctxt, ...}) id init_assum =
    let
      fun agree_at_id id' =
          let
            val parent = BoxID.get_parent_prim ctxt (the_single id')
            val is_equiv_t = RewriteTable.is_equiv_t parent ctxt
          in
            is_equiv_t (init_assum, the_single (get_init_assums st id'))
          end

      fun can_test_id id' =
          case id' of
              [prim_id'] =>
              BoxID.is_eq_ancestor ctxt (BoxID.get_parent_prim ctxt prim_id') id
            | _ => false

      val ids_to_test = get_all_ids st |> filter can_test_id
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {uid_next, boxes, queue, ctxt, resolve_th} =
    {uid_next = uid_next, boxes = boxes, queue = f queue, ctxt = ctxt,
     resolve_th = resolve_th}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

end  (* structure Status *)

val _ = Theory.setup (ItemIO.add_basic_item_io)
