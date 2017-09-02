(* Definition of updates and proof status. *)

datatype update_type = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
datatype init_info = InitVar of term | InitAssum of term
datatype raw_update
  = AddItems of {id: box_id, sc: int option, raw_items: raw_item list}
  | AddBoxes of {id: box_id, sc: int option, inits: init_info list}
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
  val dest_init_var: init_info -> term list
  val dest_init_assum: init_info -> term list
  val is_init_assum: init_info -> bool
  val build_init_infos: term list * term list -> init_info list
  val string_of_init_info: Proof.context -> init_info -> string
  val get_neg_form: init_info list -> term
  val get_neg_form_obj: Proof.context -> init_info list -> term
  val get_neg_form_thm: Proof.context -> init_info list -> thm -> thm

  val type_of_update: raw_update -> update_type
  val string_of_update_type: update_type -> string
  val string_of_raw_update: Proof.context -> raw_update -> string
  val thm_to_ritem: thm -> raw_item
  val thm_update: box_id * thm -> raw_update

  val handler_ritems: Proof.context -> term -> retro_handler -> raw_item list
  val apply_exists_ritems: Proof.context -> string list -> thm ->
                           raw_item list * thm
  val apply_exists: Proof.context -> string list -> box_id * thm ->
                    raw_update list
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: update -> string
end;

structure Update : UPDATE =
struct

fun dest_init_var init = case init of InitVar t => [t] | _ => []
fun dest_init_assum init = case init of InitAssum t => [t] | _ => []
fun is_init_assum init = case init of InitAssum _ => true | _ => false
fun build_init_infos (vars, assums) = map InitVar vars @ map InitAssum assums
fun string_of_init_info ctxt init =
    case init of
        InitVar t => ("Var " ^ (Syntax.string_of_term ctxt t))
      | InitAssum assum => ("Assum " ^ (Syntax.string_of_term ctxt assum))

(* Given list of initial variables and assumptions, return the
   contradiction derived from them. Each initial variable becomes !!,
   the last assumption is negated, and each assumption before the last
   becomes ==>.
 *)
fun get_neg_form inits =
    if null inits then pFalse
    else let
      fun mk_all (x, T) t = Logic.all_const T $ Term.absfree (x, T) t
      val concl = inits |> List.last |> dest_init_assum |> the_single
                        |> get_neg'
                  handle List.Empty =>
                         raise Fail "get_neg_form: last init should be prop."

      fun fold_init init t =
          case init of
              InitVar v => mk_all (dest_Free v) t
            | InitAssum assum => Logic.mk_implies (assum, t)
    in
      fold fold_init (tl (rev inits)) concl
    end

fun get_neg_form_obj ctxt inits =
    inits |> get_neg_form |> Thm.cterm_of ctxt
          |> UtilLogic.to_obj_conv ctxt |> Util.rhs_of

(* Given a contradiction th, returns a new theorem with assumptions
   pulled into the proposition of th. The resulting form of th is the
   same as that returned by get_neg_form.
 *)
fun get_neg_form_thm ctxt inits th =
    if null inits then th
    else let
      val _ = assert (Thm.prop_of th aconv pFalse)
                     "get_neg_form_thm: input th should be a contradiction."
      val tl_assum =
          inits |> List.last |> dest_init_assum |> the_single
          handle List.Empty =>
                 raise Fail "get_neg_form_thm: last init should be prop."

      fun fold_init init th =
          case init of
              InitVar v => Thm.forall_intr (Thm.cterm_of ctxt v) th
            | InitAssum assum => th |> Thm.implies_intr (Thm.cterm_of ctxt assum)
    in
      th |> Thm.implies_intr (Thm.cterm_of ctxt tl_assum)
         |> apply_to_thm UtilLogic.rewrite_from_contra_form
         |> fold fold_init (tl (rev inits))
    end

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
      | AddBoxes {id, inits, ...} =>
        "Add box " ^ (Util.string_of_list (string_of_init_info ctxt) inits) ^
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

fun handler_ritems ctxt t handler =
    let
      val _ = assert (fastype_of t = propT) "handler_ritems: wrong type"
    in
      [Handler (t, handler), thm_to_ritem (Util.assume_thm ctxt t)]
    end

(* Apply the given existence theorem and return the list of resulting ritems.
 *)
fun apply_exists_ritems ctxt xs ex_th =
    let
      val thy = Proof_Context.theory_of ctxt

      val ex_th' = ex_th |> apply_to_thm' (UtilLogic.normalize_exists ctxt)
      val (vars, body) = ex_th' |> prop_of' |> UtilLogic.strip_exists
                                |> apsnd mk_Trueprop
                                |> Util.replace_names xs

      val new_th = body |> Thm.cterm_of ctxt |> Thm.assume

      (* Given two terms t and u, where t may contain internal
         variables, find replacements for those internal variables so
         that t agrees with u. If there is no match, return the empty
         list.
       *)
      fun match_vars_one (t, u) =
          let
            val all_internal_vars =
                (Term.add_frees t [])
                    |> filter (fn (x, _) => Util.is_just_internal x)
            fun subst_for_var (x, T) =
                [(Free (x, T), Var ((x, 0), T))]
            val subst = maps subst_for_var all_internal_vars

            val pat = Term.subst_atomic subst t
            val inst = Pattern.first_order_match thy (pat, u) fo_init
            fun get_freevar (x, T) = (Free (x, T), lookup_inst inst x)
          in
            map get_freevar all_internal_vars
          end
          handle Pattern.MATCH => []

      (* Given two lists of terms, where terms of ts may contain
         internal variables, find replacements for those internal
         variables so that those terms match that in us. Note we do
         not check for contradictory replacements here.
       *)
      fun match_vars (ts, us) =
          (maps match_vars_one (Util.all_pairs (ts, us)))
              |> distinct (eq_pair (op aconv) (op aconv))

      (* Find new versions of vars by matching body and t. *)
      fun get_freevars t =
          let
            val subst = match_vars_one (body, t)
            fun get_freevar v =
                let
                  val (x, _) = Term.dest_Free v
                in
                  if not (Util.is_just_internal x) then v
                  else the (AList.lookup (op aconv) subst v)
                  handle Option.Option =>
                         raise Fail "get_freevars: cannot match body and t"
                end
          in
            map get_freevar vars
          end

      fun ready (t, ts) =
          let
            val fvars = get_freevars t
          in
            forall (fn t' => t' aconv t orelse not (Util.occurs_frees fvars t')) ts
          end

      fun handler (t, th) =
          let
            val subst = (match_vars (Thm.hyps_of ex_th', Thm.hyps_of th))
                            |> map (apply2 (Thm.cterm_of ctxt))
            val fvars = get_freevars t
          in
            th |> Thm.implies_intr (Thm.cterm_of ctxt t)
               |> fold (UtilLogic.ex_elim ctxt) (rev fvars)
               |> Thm.elim_implies (Util.subst_thm_atomic subst ex_th')
          end

      val ritems = (map (BoxItem.var_to_fact) vars) @
                   [Handler (body, (ready, handler))]
    in
      (ritems, new_th)
    end

(* Calls the previous function, and directly produces the update. *)
fun apply_exists ctxt xs (id, ex_th) =
    let
      val (ritems, new_th) = apply_exists_ritems ctxt xs ex_th
    in
      [AddItems {id = id, sc = NONE,
                 raw_items = ritems @ [thm_to_ritem new_th]}]
    end

fun update_info ctxt id ritems =
    (Util.string_of_list' (ItemIO.string_of_raw_item ctxt)
                     (filter (not o BoxItem.is_handler_raw) ritems)) ^
    " at box " ^ (BoxID.string_of_box_id id)

fun uid_string_of_item {uid, ...} = "(" ^ string_of_int uid ^ ")"

fun source_info {prfstep_name, source, ...} =
    prfstep_name ^ " on " ^ (Util.string_of_list' (uid_string_of_item) source)

end  (* structure Update. *)

type box = {inits: init_info list,
            handlers: (term * retro_handler) list,
            items: (box_item * box_id list) Inttab.table,
            resolve_th: thm option}

signature BOX =
sig
  val init_box: init_info list -> box
  val get_inits: box -> init_info list
  val get_init_vars: box -> term list
  val get_init_assums: box -> term list

  val add_handler: term * retro_handler -> box -> box
  val get_handlers: box -> (term * retro_handler) list

  val map_items: ((box_item * box_id list) Inttab.table ->
                  (box_item * box_id list) Inttab.table) -> box -> box
  val add_item: box_item -> box -> box
  val is_item_removed: box_item * box_id list -> bool
  val get_items: bool -> box -> box_item list
  val lookup_item: box -> int -> (box_item * box_id list) option

  val set_resolve_th: thm -> box -> box
  val get_resolve_th: box -> thm

  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct

fun init_box inits = {inits = inits, handlers = [], items = Inttab.empty,
                      resolve_th = NONE}
fun get_inits {inits, ...} = inits
fun get_init_vars {inits, ...} = maps Update.dest_init_var inits
fun get_init_assums {inits, ...} = maps Update.dest_init_assum inits

fun add_handler (t, handler) {inits, handlers, items, resolve_th} =
    {inits = inits, handlers = cons (t, handler) handlers, items = items,
     resolve_th = resolve_th}
fun get_handlers {handlers, ...} = handlers

fun map_items f {inits, handlers, items, resolve_th} =
    {inits = inits, handlers = handlers, items = f items,
     resolve_th = resolve_th}

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

fun set_resolve_th th {inits, handlers, items, ...} =
    {inits = inits, handlers = handlers, items = items, resolve_th = SOME th}

fun get_resolve_th {resolve_th, ...} =
    case resolve_th of
        NONE => raise Fail "get_resolve_th: box not resolved."
      | SOME th => th

fun short_string_of_box ctxt {inits, ...} =
    Update.get_neg_form inits |> Syntax.string_of_term ctxt

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
  val add_prim_box: box_id -> box -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_all_ids: status -> box_id list
  val get_resolved: status -> box_id list
  val get_unresolved: status -> box_id list
  val get_eq_ancestors: status -> box_id -> box_id list
  val add_composite_box: box_id -> status -> status

  val get_items: bool -> status -> box_id -> box_item list
  val get_inits: status -> box_id -> init_info list
  val get_init_vars: status -> box_id -> term list
  val get_init_assums: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term * retro_handler) list
  val get_all_items: bool -> status -> box_id -> box_item list
  val get_all_inits: status -> box_id -> init_info list
  val get_all_init_vars: status -> box_id -> term list
  val get_all_init_assums: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term * retro_handler) list
  val add_item: box_item -> status -> status
  val add_handler: box_id -> (term * retro_handler) -> status -> status
  val lookup_item: status -> box_id -> int -> (box_item * box_id list) option
  val lookup_item_all: status -> box_id -> int -> (box_item * box_id list) list
  val add_shadowed: box_id * box_item -> status -> status
  val query_shadowed: status -> box_id -> box_item -> bool
  val query_removed: status -> box_item -> bool
  val set_resolve_th: box_id -> thm -> status -> status
  val get_resolve_th: status -> box_id -> thm

  val find_fact: status -> box_id -> term -> thm option
  val find_neg_form: status -> box_id -> init_info list -> thm option
  val find_ritem_exact: status -> box_id -> raw_item -> bool
  val find_ritems_exact:
      status -> box_id -> raw_item list -> raw_item list * raw_item list
  val invoke_handler: term * retro_handler -> thm -> thm
  val invoke_handlers: (bool * (term * retro_handler)) list -> thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> thm
  val find_prim_box: status -> box_id -> init_info list -> box_id option
  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: update -> status -> status
  val delmin_from_queue: status -> status
end;

structure Status : STATUS =
struct

fun empty_status ctxt =
    {uid_next = 1, boxes = Boxidtab.empty, queue = Updates_Heap.empty, ctxt = ctxt}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id =
    the (Boxidtab.lookup boxes id)
    handle Option.Option => raise Fail "get_box: id not found."

fun incr_uid n {uid_next, boxes, queue, ctxt} =
    {uid_next = uid_next + n, boxes = boxes, queue = queue, ctxt = ctxt}

fun map_box id f {uid_next, boxes, queue, ctxt} =
    {uid_next = uid_next, boxes = Boxidtab.map_entry id f boxes,
     queue = queue, ctxt = ctxt}

fun map_context f {uid_next, boxes, queue, ctxt} =
    {uid_next = uid_next, boxes = boxes, queue = queue, ctxt = f ctxt}

fun add_prim_box parent_id new_box {uid_next, boxes, queue, ctxt} =
    let
      val (id, ctxt') = BoxID.add_prim_id parent_id ctxt
    in
      (id, {uid_next = uid_next,
            boxes = Boxidtab.update_new ([id], new_box) boxes, queue = queue,
            ctxt = ctxt'})
    end

fun add_resolved id {uid_next, boxes, queue, ctxt} =
    let
      val ctxt' = BoxID.add_resolved id ctxt
    in
      {uid_next = uid_next, boxes = boxes, queue = queue,
       ctxt = ctxt' |> RewriteTable.clean_resolved id
                    |> PropertyData.clean_resolved id
                    |> WellformData.clean_resolved id
                    |> Auto2Data.invoke_clean_resolved id}
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
fun add_composite_box id (st as {uid_next, boxes, queue, ctxt}) =
    if exist_box st id then
      raise Fail "Try to add a composite box that already exists"
    else if length id = 1 then
      raise Fail "Try to add a primitive box as a composite"
    else
      {uid_next = uid_next,
       boxes = Boxidtab.update_new (id, Box.init_box []) boxes,
       queue = queue, ctxt = ctxt}

fun get_for_box f st id = if exist_box st id then f (get_box st id) else []
fun get_all_for_box f st id = maps (get_for_box f st) (get_eq_ancestors st id)
fun get_items b     = get_for_box (Box.get_items b)
val get_inits       = get_for_box Box.get_inits
val get_init_vars   = get_for_box Box.get_init_vars
val get_init_assums = get_for_box Box.get_init_assums
val get_handlers    = get_for_box Box.get_handlers
fun get_all_items b     = get_all_for_box (Box.get_items b)
val get_all_inits       = get_all_for_box Box.get_inits
val get_all_init_vars   = get_all_for_box Box.get_init_vars
val get_all_init_assums = get_all_for_box Box.get_init_assums
val get_all_handlers    = get_all_for_box Box.get_handlers

fun add_item (item as {id, ...}) = map_box id (Box.add_item item)

fun add_handler id (t, handler) = map_box id (Box.add_handler (t, handler))

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

fun set_resolve_th id th st = st |> map_box id (Box.set_resolve_th th)
fun get_resolve_th st id = Box.get_resolve_th (get_box st id)

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

fun find_neg_form st id inits =
    if length inits = 1 andalso Update.is_init_assum (the_single inits) then
      let
        val t = inits |> maps Update.dest_init_assum |> the_single
                      |> dest_Trueprop |> get_neg
      in
        find_fact st id t
      end
    else NONE

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

(* Attempt to find the given ritems at id or its ancestors.

   If there are new variables among the ritems, convert each ritem
   (other than variables) into patterns, then attempt to match each of
   the patterns with items in the state.

   If there are no new variables among the ritems, try to find each of
   the ritems individually.

   Return two lists of ritems: those found at id and those not found.
 *)
fun find_ritems_exact st id ritems =
    let
      val thy = theory_of st
      val (var_ritems, ritems') =
          ritems |> filter_split (BoxItem.match_ty_str_raw TY_VAR)
    in
      if null var_ritems then
        filter_split (find_ritem_exact st id) ritems
      else let
        val vars = maps BoxItem.get_tname_raw var_ritems
        val sch_vars = vars |> map dest_Free
                            |> map (fn (x, T) => Var ((x, 0), T))
        val subst = vars ~~ sch_vars
        val items = get_all_items true st id

        fun find_ritem ritem insts =
            case ritem of
                Handler _ => insts
              | Fact (ty_str, tname, _) =>
                if exists Util.has_vars tname then [] else
                let
                  val tname' = map (Term.subst_atomic subst) tname

                  fun process_inst cts inst =
                      [Util.first_order_match_list
                           thy (tname' ~~ map Thm.term_of cts) inst]
                      handle Pattern.MATCH => []

                  fun match_item {ty_str = ty2, tname = ts2, ...} =
                      if ty_str <> ty2 then []
                      else if length tname' <> length ts2 then []
                      else maps (process_inst ts2) insts
                in
                  maps match_item items
                end

        val inst = fold find_ritem ritems' [fo_init]
      in
        if null inst then ([], ritems) else (ritems, [])
      end
    end

(* Invoke a single handler (_, f) on a term t. *)
fun invoke_handler (t, (_, f)) th = f (t, th)

(* Invoke any handler given in the list handlers, whose term appear as
   a hypothesis of th. Each handler is of the form (req, (t, _)),
   where req is a boolean specifying whether the handler must be
   applied.
 *)
fun invoke_handlers handlers th =
    let
      val all_hyps = Thm.hyps_of th
      val handlers' = handlers |> filter (
            fn (_, (t, _)) => member (op aconv) all_hyps t)
    in
      if null handlers' then th
      else let
        val to_invoke =
            find_index (fn (_, (t, (ready, _))) => ready (t, all_hyps))
                       handlers'
      in
        if to_invoke = ~1 then
          if forall (fn (req, _) => not req) handlers' then th
          else raise Fail "invoke_handlers: cannot find invokable handler."
        else
          th |> invoke_handler (snd (nth handlers' to_invoke))
             |> invoke_handlers handlers
      end
    end

(* Derive the consequence if box id is resolved, to the parent id
   formed by getting parent at index i.
 *)
fun get_on_resolve (st as {ctxt, ...}) id i th =
    let
      val parent = BoxID.get_parent_at_i ctxt id i
      val prim_id = nth id i

      (* First get list of handlers to invoke. *)
      val retro_ids = (get_unresolved st)
                          |> filter (BoxID.is_eq_ancestor ctxt [prim_id])
                          |> filter (BoxID.is_eq_descendent ctxt id)
      val handlers = map (pair true) (maps (get_handlers st) retro_ids) @
                     map (pair false) (get_handlers st parent)
      val th' = invoke_handlers handlers th
      val inits = get_inits st [prim_id]
      val th'' = Update.get_neg_form_thm ctxt inits th'
      val _ = if prim_id = 0 then
                assert (null (Thm.hyps_of th''))
                       "get_on_resolve: did not remove all hypothesis at box 0."
              else ()
      val _ = assert (Thm.prop_of th'' aconv Update.get_neg_form inits)
                     "get_on_resolve: wrong value from get_neg_form_thm."
    in
      th''
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box (st as {ctxt, ...}) id inits =
    let
      val vars = maps Update.dest_init_var inits
      val assums = maps Update.dest_init_assum inits
      fun agree_at_id id' =
          let
            val parent = BoxID.get_parent_prim ctxt (the_single id')
            val is_equiv_t = RewriteTable.is_equiv_t parent ctxt
          in
            eq_set is_equiv_t (vars, get_init_vars st id') andalso
            eq_set is_equiv_t (assums, get_init_assums st id')
          end

      fun can_test_id id' =
          case id' of
              [prim_id'] => BoxID.is_eq_ancestor ctxt (BoxID.get_parent_prim ctxt prim_id') id
            | _ => false

      val ids_to_test = get_all_ids st |> filter can_test_id
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {uid_next, boxes, queue, ctxt} =
    {uid_next = uid_next, boxes = boxes, queue = f queue, ctxt = ctxt}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

end  (* structure Status *)

val _ = Theory.setup (ItemIO.add_basic_item_io)
