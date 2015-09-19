(* Definitions and basic operations on the main data structures, up to
   Status, which represents the state of the proof.
 *)

val TY_EQ = "EQ"
val TY_VAR = "VAR"
val TY_PROP = "PROP"
val TY_TERM = "TERM"

signature BOXITEM =
sig
  type retro_handler
  datatype raw_item = Handler of term * retro_handler
                    | Fact of string * term list * thm
  (* Facts. *)
  val var_to_fact: term -> raw_item
  val term_to_fact: term -> raw_item
  val is_fact_raw: raw_item -> bool
  val get_thm_raw: raw_item -> thm
  val get_ty_str_raw: raw_item -> string
  val match_ty_str_raw: string -> raw_item -> bool
  val match_ty_strs_raw: string list -> raw_item -> bool
  val get_tname_raw: raw_item -> term list
  val get_single_tname_raw: raw_item -> term
  (* Handlers. *)
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term * retro_handler
  (* Misc. functions. *)
  val eq_ritem: raw_item * raw_item -> bool
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val obtain_variant_frees:
      Proof.context * raw_item list -> Proof.context * (cterm * cterm) list

  type box_item
  val id_of_item: box_item -> box_id
  val score_of_item: box_item -> int
  val get_thm: box_item -> thm
  val get_ty_str: box_item -> string
  val match_ty_str: string -> box_item -> bool
  val match_ty_strs: string list -> box_item -> bool
  val get_tname: box_item -> term list
  val get_single_tname: box_item -> term
  (* Misc. functions. *)
  val mk_box_item: box_id * int * raw_item -> box_item

  type pre_filter
  val no_prereq_fn: rewrite_table -> box_item -> bool
  val apply_pre_filter: rewrite_table -> pre_filter -> box_item -> bool
  val apply_pre_filter_ty_only: pre_filter -> box_item -> bool
end;

structure BoxItem : BOXITEM =
struct

type retro_handler = (term * term list -> bool) * (term * thm -> thm)
datatype raw_item = Handler of term * retro_handler
                  | Fact of string * term list * thm

fun var_to_fact t = Fact (TY_VAR, [t], true_th)
fun term_to_fact t = Fact (TY_TERM, [t], true_th)

fun is_fact_raw ritem =
    case ritem of Fact _ => true | _ => false
fun get_thm_raw ritem =
    case ritem of Fact (_, _, th) => th
                | _ => raise AUTO2 "get_thm_raw: wrong type"
fun get_ty_str_raw ritem =
    case ritem of Fact (ty_str, _, _) => ty_str
                | _ => raise AUTO2 "get_ty_str_raw: wrong type"
fun match_ty_str_raw s ritem =
    is_fact_raw ritem andalso (s = "" orelse get_ty_str_raw ritem = s)
fun match_ty_strs_raw slist ritem =
    is_fact_raw ritem andalso member (op =) slist (get_ty_str_raw ritem)
fun get_tname_raw ritem =
    case ritem of Fact (_, tname, _) => tname
                | _ => raise AUTO2 "get_term_raw: wrong type"
fun get_single_tname_raw ritem =
    the_single (get_tname_raw ritem)
    handle List.Empty => raise AUTO2 "get_single_tname: multiple tnames."

fun is_handler_raw ritem =
    case ritem of Handler _ => true | _ => false
fun dest_handler_raw ritem =
    case ritem of Handler (t, handler) => (t, handler)
                | _ => raise AUTO2 "dest_handler_raw: wrong type"

fun eq_ritem (ritem1, ritem2) =
    if is_handler_raw ritem1 andalso is_handler_raw ritem2 then
      eq_pair (op aconv) pointer_eq (dest_handler_raw ritem1,
                                     dest_handler_raw ritem2)
    else if is_fact_raw ritem1 andalso is_fact_raw ritem2 then
      (get_ty_str_raw ritem1 = get_ty_str_raw ritem2 andalso
       eq_list (op aconv) (get_tname_raw ritem1, get_tname_raw ritem2) andalso
       Thm.eq_thm (get_thm_raw ritem1, get_thm_raw ritem2))
    else false

fun instantiate inst ritem =
    let
      val subst = subst_atomic (map (apply2 Thm.term_of) inst)
    in
      case ritem of
          Handler (t, handler) => Handler (subst t, handler)
        | Fact (ty_str, tname, th) =>
          Fact (ty_str, map subst tname, th |> Thm.instantiate ([], inst)
                                            |> send_concrete_to_hyps)
    end

(* Given a context and list of raw items, obtain fresh names of free
   variables for each internal (schematic) variable declared in the
   raw items, and declare the new variables in context. Return the
   substitution from internal schematic variables to the new free
   variables.
 *)
fun obtain_variant_frees (ctxt, ritems) =
    let
      (* Original internal variables. *)
      val all_vars =
          ritems |> filter (match_ty_str_raw TY_VAR) |> map get_single_tname_raw
                 |> filter is_Var |> map dest_Var
      (* New names for these variables. *)
      val all_vars' =
          all_vars |> map (fn ((nm,_), T) => (Name.dest_internal nm, T))
                   |> Variable.variant_frees ctxt []
          handle Fail "unsuffix" =>
                 raise AUTO2 "replace_internals_items: dest_internal"
      val subst = (map Var all_vars) ~~ (map Free all_vars')
      val csubst = map (apply2 (cert ctxt)) subst
    in
      (* Use add_fixes_direct to update ctxt, since this is called
         when ctxt is in body.
       *)
      (Variable.add_fixes_direct (map fst all_vars') ctxt, csubst)
    end

type box_item =
     {id: box_id, sc: int, ty_str: string, tname: term list, prop: thm}
fun id_of_item {id, ...} = id
fun score_of_item {sc, ...} = sc
fun get_thm {prop, ...} = prop
fun get_ty_str {ty_str, ...} = ty_str
fun match_ty_str s {ty_str, ...} = (s = "" orelse s = ty_str)
fun match_ty_strs slist {ty_str, ...} = member (op =) slist ty_str
fun get_tname {tname, ...} = tname
fun get_single_tname {tname, ...} = the_single tname
fun mk_box_item (id, sc, ritem) =
    case ritem of
        Handler _ => raise AUTO2 "mk_box_item: ritem must be Fact"
      | Fact (ty_str, tname, prop) =>
        {id = id, sc = sc, ty_str = ty_str, tname = tname, prop = prop}

type pre_filter = {ty_str: string, pre_filt: rewrite_table -> box_item -> bool}

fun no_prereq_fn _ _ = true

fun apply_pre_filter tbl {ty_str, pre_filt} item =
    (match_ty_str ty_str item andalso pre_filt tbl item)
fun apply_pre_filter_ty_only {ty_str, ...} item = match_ty_str ty_str item

end  (* structure BoxItem. *)

open BoxItem

(* Registry of functions for matching items to patterns and for
   converting items to theorems.
 *)
type match_fn = term -> box_item -> rewrite_table -> id_inst -> id_inst_th list

datatype item_io_table
  = ItemIOTable of {
    item_to_th: ((term -> pre_filter option) * match_fn) list,
    th_to_item: (term -> thm -> raw_item option) list,
    str_of_item: (Proof.context -> term list * thm -> string) Symtab.table}

structure ItemIOData =
Theory_Data (
  type T = item_io_table;
  val empty = ItemIOTable {
        item_to_th = [], th_to_item = [], str_of_item = Symtab.empty};
  val extend = I;
  fun merge (
    ItemIOTable {item_to_th = ith1, th_to_item = thi1, str_of_item = tab1},
    ItemIOTable {item_to_th = ith2, th_to_item = thi2, str_of_item = tab2}) =
      ItemIOTable {item_to_th = Library.merge pointer_eq (ith1, ith2),
                   th_to_item = Library.merge pointer_eq (thi1, thi2),
                   str_of_item = Symtab.merge pointer_eq (tab1, tab2)}
)

signature ITEM_IO_DATA =
sig
  val add_item_to_th: (term -> pre_filter option) * match_fn -> theory -> theory
  val add_th_to_item: (term -> thm -> raw_item option) -> theory -> theory
  val add_str_of_item:
      string * (Proof.context -> term list * thm -> string) -> theory -> theory
  val univ_filt: pre_filter
  val find_th_matcher: theory -> term -> pre_filter * match_fn
  val univ_matcher: match_fn
  val prop_match: match_fn
  val term_match: match_fn
  val eq_prop_filt: term -> pre_filter option
  val eq_prop_match: match_fn
  val thm_to_ritem: theory -> thm -> raw_item
  val string_of_item_info: Proof.context -> string * term list * thm -> string
  val add_basic_item_io: theory -> theory
end;

structure ItemIO_Data : ITEM_IO_DATA =
struct

fun add_item_to_th (filt, matcher) = ItemIOData.map (
      fn ItemIOTable {item_to_th, th_to_item, str_of_item} =>
         ItemIOTable {item_to_th = (filt, matcher) :: item_to_th,
                      th_to_item = th_to_item, str_of_item = str_of_item})

fun add_th_to_item conv_fn = ItemIOData.map (
      fn ItemIOTable {item_to_th, th_to_item, str_of_item} =>
         ItemIOTable {item_to_th = item_to_th,
                      th_to_item = conv_fn :: th_to_item,
                      str_of_item = str_of_item})

fun add_str_of_item (ty_str, f) = ItemIOData.map (
      fn ItemIOTable {item_to_th, th_to_item, str_of_item} =>
         ItemIOTable {
           item_to_th = item_to_th, th_to_item = th_to_item,
           str_of_item = str_of_item |> Symtab.update_new (ty_str, f)})

(* Matching any Trueprop term with a PROP item. *)
fun prop_filt t =
    let
      fun filt pat tbl {id, tname, ...} =
          length (fo_table_match id tbl (pat, the_single tname)) > 0
    in
      case t of
          Const (@{const_name Trueprop}, _) $ pat =>
          SOME {ty_str = TY_PROP, pre_filt = filt pat}
        | _ => NONE
    end

fun prop_match t {tname, prop, ...} tbl (id, inst) =
    let
      val pat = HOLogic.dest_Trueprop t
      val insts' =
          RewriteTable.fo_rewrite_match tbl (pat, the_single tname) (id, inst)
      fun process_inst (inst, eq_th) =
          (inst, Thm.equal_elim (make_trueprop_eq (meta_sym eq_th)) prop)
    in
      map process_inst insts'
    end

(* Universal matcher (find the appropriate matcher for t at runtime). *)
val univ_filt = {ty_str = "", pre_filt = no_prereq_fn}

fun find_th_matcher thy t =
    case t of
        Const (@{const_name Trueprop}, _) $ Var _ => (univ_filt, univ_matcher)
      | _ =>
        let
          val ItemIOTable {item_to_th, ...} = ItemIOData.get thy
        in
          case find_first (fn (filt, _) => is_some (filt t)) item_to_th of
              NONE => raise AUTO2 "find_th_matcher: cannot find matcher."
            | SOME (filt, matcher) => (the (filt t), matcher)
        end

and univ_matcher t item tbl (id, inst) =
    let
      val thy = RewriteTable.theory_of tbl
      val (filt, matcher) = find_th_matcher thy t
      (* Change to default prop matcher, if still univ. *)
      val (filt', matcher') = if pointer_eq (matcher, univ_matcher) then
                                (the (prop_filt t), prop_match)
                              else (filt, matcher)
    in
      if apply_pre_filter_ty_only filt' item then
        matcher' t item tbl (id, inst)
      else []
    end

(* Matching any term (not of type prop) with a TERM item. *)
fun term_filt t =
    let
      fun filt tbl {id, tname, ...} =
          length (RewriteTable.fo_rewrite_match_head
                      tbl (t, the_single tname) (id, fo_init)) > 0
    in
      if fastype_of t = @{typ prop} then NONE
      else SOME {ty_str = TY_TERM, pre_filt = filt}
    end

fun term_match t {tname, ...} tbl (id, inst) =
    let
      val insts' = RewriteTable.fo_rewrite_match_head
                       tbl (t, the_single tname) (id, inst)
      fun process_inst (inst, _) = (inst, true_th)
    in
      map process_inst insts'
    end

(* Matching a Trueprop equality with a TERM item. *)
fun eq_prop_filt t =
    let
      fun filt pat tbl {id, tname, ...} =
          length (fo_table_match id tbl (pat, the_single tname)) > 0
    in
      case t of
          Const (@{const_name Trueprop}, _) $ (
            Const (@{const_name HOL.eq}, _) $ lhs $ _) =>
          SOME {ty_str = TY_TERM, pre_filt = filt lhs}
        | _ => NONE
    end

fun eq_prop_match t {tname, ...} tbl (id, inst) =
    let
      val (lhs, rhs) = t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      val u = the_single tname
      val insts' =
          RewriteTable.fo_rewrite_match_list
              tbl [(true, (lhs, u)), (false, (rhs, u))] (id, inst)
      fun process_inst (inst, ths) =
          let
            (* th1: lhs(env) == u, th2: rhs(env) == u. *)
            val (th1, th2) = the_pair ths
          in
            (inst, to_obj_eq (transitive_list [th1, meta_sym th2]))
          end
    in
      map process_inst insts'
    end

(* Whether the given term contains a non-internal schematic q
   variable.
 *)
fun has_non_internal_var t =
    exists (fn ((nm, _), _) => not (Name.is_internal nm))
           (Term.add_vars t [])

(* Remove any initial assumptions that contain no schematic variables
   or only internal schematic variables (which will be replaced by
   free variables).
 *)
fun strip_internal_var_assums prop =
    case prop of
        Const ("Pure.imp", _) $ A $ B =>
        if has_non_internal_var A then prop
        else strip_internal_var_assums B
      | _ => prop

fun thm_to_ritem thy th =
    let
      val ItemIOTable {th_to_item, ...} = ItemIOData.get thy
      val prop = strip_internal_var_assums (Thm.prop_of th)
    in
      case get_first (fn conv_fn => conv_fn prop th) th_to_item of
          NONE => raise AUTO2CT (
                   "thm_to_ritem: cannot convert theorem.", [Thm.cprop_of th])
        | SOME ritem => ritem
    end

fun prop_to_ritem prop th =
    if is_Trueprop prop andalso not (has_non_internal_var prop) then
      SOME (Fact (TY_PROP, [HOLogic.dest_Trueprop prop], th))
    else NONE

fun eq_to_ritem prop th =
    if is_eq_term' prop andalso not (has_non_internal_var prop) then
      SOME (Fact (TY_EQ, list_pair (HOLogic.dest_eq (
                                       HOLogic.dest_Trueprop prop)), th))
    else NONE

fun string_of_item_info ctxt (ty_str, tname, th) =
    let
      val thy = Proof_Context.theory_of ctxt
      val ItemIOTable {str_of_item, ...} = ItemIOData.get thy
    in
      case Symtab.lookup str_of_item ty_str of
          NONE => ty_str ^ " " ^ (tname |> pretty_terms ctxt |> str)
        | SOME f => f ctxt (tname, th)
    end

val add_basic_item_io =
    fold add_item_to_th [
      (prop_filt, prop_match),
      (term_filt, term_match)

    ] #> fold add_th_to_item [
      prop_to_ritem, eq_to_ritem

    ] #> fold add_str_of_item [
      (TY_EQ, fn ctxt => fn (_, th) =>
                 th |> Thm.prop_of |> pretty_term ctxt |> str),
      (TY_PROP, fn ctxt => fn (_, th) =>
                   th |> Thm.prop_of |> pretty_term ctxt |> str)
    ]

end  (* structure ItemIO_Data. *)

val thm_to_ritem = ItemIO_Data.thm_to_ritem
fun thm_to_ritem_ctxt ctxt = thm_to_ritem (Proof_Context.theory_of ctxt)
fun string_of_raw_item ctxt ritem =
    case ritem of
        Handler (t, _) => "Handler " ^ (t |> pretty_term ctxt |> str)
      | Fact info => ItemIO_Data.string_of_item_info ctxt info
fun string_of_item ctxt ({ty_str, tname, prop, ...}:box_item) =
    ItemIO_Data.string_of_item_info ctxt (ty_str, tname, prop)

val _ = Theory.setup ItemIO_Data.add_basic_item_io

signature UPDATE =
sig
  datatype update_type
    = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
  datatype raw_update
    = AddItems of {id: box_id, raw_items: raw_item list}
    | AddBoxes of {id: box_id, vars: term list, assums: term list,
                   concls: term list, cb: box_id * thm -> raw_update list}
    | ResolveBox of {id: box_id, th: thm}
    | ShadowItem of {id: box_id, item: box_item}
  type resolve_callback
  type update
  val type_of_update: raw_update -> update_type
  val null_callback: resolve_callback
  val thm_update: theory -> box_id * thm -> raw_update
  val handler_ritems: Proof.context -> term -> retro_handler -> raw_item list
  val apply_horn_clause:
      theory -> box_id * thm -> resolve_callback -> raw_update list
  val apply_exists: box_id * thm -> Proof.context -> string list ->
                    raw_update list
  val target_of_update: raw_update -> box_id
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: Proof.context -> update -> string
end;

structure Update : UPDATE =
struct

datatype update_type
  = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
datatype raw_update
  = AddItems of {id: box_id, raw_items: raw_item list}
  | AddBoxes of {id: box_id, vars: term list, assums: term list,
                 concls: term list, cb: box_id * thm -> raw_update list}
  | ResolveBox of {id: box_id, th: thm}
  | ShadowItem of {id: box_id, item: box_item}
type resolve_callback = box_id * thm -> raw_update list
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

fun type_of_update raw_updt =
    case raw_updt of
        AddItems _ => ADD_ITEMS
      | AddBoxes _ => ADD_BOXES
      | ResolveBox _ => RESOLVE_BOX
      | ShadowItem _ => SHADOW_ITEM

val null_callback = K []

fun thm_update thy (id, th) =
    if Thm.prop_of th aconv prop_False then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, raw_items = [thm_to_ritem thy th]}

fun handler_ritems ctxt t handler =
    [Handler (t, handler), thm_to_ritem_ctxt ctxt (assume_thm ctxt t)]

fun apply_horn_clause thy (id, th) cb =
    case Thm.prop_of th of
        Const ("Pure.imp", _) $ A $ _ =>
        let
          val (vars, body) = strip_obj_all_var (HOLogic.dest_Trueprop A)
          val (assums, concl) = (strip_obj_imp body)
                                    |> apfst (map HOLogic.mk_Trueprop)
                                    |> apsnd HOLogic.mk_Trueprop
          fun callback (id', th_fst) =
              apply_horn_clause thy (id', [th_fst] MRS th) cb
        in
          [AddBoxes {id = id, vars = vars, assums = assums, concls = [concl],
                     cb = callback}]
        end
      | _ => if pointer_eq (cb, null_callback) then [thm_update thy (id, th)]
             else cb (id, th)

(* nms specify the names of free variables, either internal (use
   replace_internals_items to fix) or otherwise (will be put into
   context as is).
 *)
fun apply_exists (id, ex_th) ctxt nms =
    let
      fun dest_one_abs nm t =
          case t of
              Const("HOL.Ex", _) $ Abs (_, T, body) =>
              let
                val (nm', body') = Term.dest_abs (nm, T, body)
                val _ = assert (nm = nm') "apply_exists: name clash"
              in
                if Name.is_internal nm then
                  let
                    val var = Var ((nm, 0), T)
                  in
                    (var, subst_atomic [(Free (nm, T), var)] body')
                  end
                else
                  (Free (nm, T), body')
              end
            | _ => raise AUTO2 "apply_exists: not exists statement."

      fun dest_all_abs nms t =
          case nms of
              [] => ([], t)
            | nm :: rest =>
              let
                val (var, t') = dest_one_abs nm t
                val (vars, t'') = dest_all_abs rest t'
              in
                (var :: vars, t'')
              end

      val (vars, new_prop) = ex_th |> prop_of' |> dest_all_abs nms
      val new_prop' = HOLogic.mk_Trueprop new_prop
      val new_th = new_prop' |> cert ctxt |> Thm.trivial

      fun get_freevars t =
          let
            val inst = pattern_fo_match ctxt (new_prop', t)
            fun get_freevar var =
                case var of
                    Free _ => var
                  | Var ((nm, i), _) => lookup_instn inst (nm, i)
                  | _ => raise AUTO2 "apply_exists: unexpected var."
          in
            map get_freevar vars
          end

      fun ready (t, ts) =
          forall (fn t' => t' aconv t orelse
                           not (occurs_frees (get_freevars t) t')) ts

      fun handler (t, th) =
          th |> Thm.implies_intr (cert ctxt t)
             |> fold (ex_elim ctxt) (rev (get_freevars t))
             |> Thm.elim_implies ex_th

      val ritems = (map var_to_fact vars) @
                   [Handler (new_prop', (ready, handler)),
                    Fact (TY_PROP, [new_prop], new_th)]
    in
      [AddItems {id = id, raw_items = ritems}]
    end

fun target_of_update raw_updt =
    case raw_updt of
        AddItems {id, ...} => id
      | AddBoxes {id, ...} => id
      | ResolveBox {id, ...} => id
      | ShadowItem {id, ...} => id

fun update_info ctxt id ritems =
    (string_of_list' (string_of_raw_item ctxt)
                     (filter (not o is_handler_raw) ritems)) ^
    " at box " ^ (string_of_box_id id)
fun source_info ctxt {sc, prfstep_name, source, ...} =
    (string_of_int sc) ^ ", " ^ prfstep_name ^
    (if prfstep_name = "DISJ" orelse prfstep_name = "DISJ_ACTIVE" then ""
     else " on " ^ (string_of_list' (string_of_item ctxt) source))

end  (* structure Update. *)

structure ItemTab =
Table (
  type key = string * term list
  val ord = prod_ord string_ord (list_ord Term_Ord.fast_term_ord)
);

signature BOX =
sig
  type box
  val init_box: term list * term list * term list -> box
  val get_init_vars: box -> term list
  val get_init_assums: box -> term list
  val get_init_concls: box -> term list

  val add_handler: term * retro_handler -> box -> box
  val get_handlers: box -> (term * retro_handler) list

  val map_items: ((box_item * box_id list) ItemTab.table ->
                  (box_item * box_id list) ItemTab.table) -> box -> box
  val add_item: box_item -> box -> box
  val is_item_removed: box_item * box_id list -> bool
  val get_items: box -> box_item list
  val lookup_item: box -> string * term list -> (box_item * box_id list) option
  val get_freevars: box -> term list
  val get_dep_vars: box -> term list

  val add_callback: Update.resolve_callback -> box -> box
  val get_callbacks: box -> Update.resolve_callback list

  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct

type box = {vars: term list, assums: term list, concls: term list,
            handlers: (term * retro_handler) list,
            items: (box_item * box_id list) ItemTab.table,
            cbs: Update.resolve_callback list}
fun init_box (vars, assums, concls) =
    {vars = vars, assums = assums, concls = concls, handlers = [],
     items = ItemTab.empty, cbs = []}
fun get_init_assums {assums, ...} = assums
fun get_init_concls {concls, ...} = concls
fun get_init_vars {vars, ...} = vars

fun add_handler (t, handler) {vars, assums, concls, handlers, items, cbs} =
    {vars = vars, assums = assums, concls = concls,
     handlers = cons (t, handler) handlers, items = items, cbs = cbs}
fun get_handlers {handlers, ...} = handlers

fun map_items f {vars, assums, concls, handlers, items, cbs} =
    {vars = vars, assums = assums, concls = concls, handlers = handlers,
     items = f items, cbs = cbs}

fun add_item (item as {ty_str, tname, ...}) =
    map_items (ItemTab.update_new ((ty_str, tname), (item, [])))
    handle ItemTab.DUP _ => raise AUTO2 "add_item: item already exists."

fun is_item_removed ({id, ...}, shadow_ids) =
    member (op =) shadow_ids id

fun get_items {items, ...} =
    ItemTab.dest items |> map snd |> filter_out is_item_removed |> map fst

fun lookup_item {items, ...} (ty_str, tname) =
    ItemTab.lookup items (ty_str, tname)

val get_freevars =
    map get_single_tname o filter (match_ty_str TY_VAR) o get_items
fun get_dep_vars box =
    subtract (op aconv) (get_init_vars box) (get_freevars box)

fun add_callback cb {vars, assums, concls, handlers, items, cbs} =
    {vars = vars, assums = assums, concls = concls, handlers = handlers,
     items = items, cbs = if pointer_eq (cb, Update.null_callback) then cbs
                          else cons cb cbs}
fun get_callbacks {cbs, ...} = cbs

fun short_string_of_box ctxt box =
    let val (assums, concls) = (get_init_assums box, get_init_concls box) in
      (if length assums > 0 then (assums |> pretty_terms ctxt |> str) ^ " ==> "
       else "") ^
      (if length concls > 0 then concls |> pretty_terms ctxt |> str
       else prop_False |> pretty_term ctxt |> str)
    end

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
  val exist_box: status -> box_id -> bool
  val get_box: status -> box_id -> Box.box
  val get_init_type: status -> rewrite_type
  val get_incr_type: status -> box_id -> thm -> rewrite_type

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
  val map_rewrites: (rewrite_table -> rewrite_table) -> status -> status
  val add_prim_box: box_id -> Box.box -> status -> int * status
  val add_resolved: box_id -> status -> status
  val get_all_ids: status -> box_id list
  val get_resolved: status -> box_id list
  val get_unresolved: status -> box_id list
  val get_eq_ancestors: status -> box_id -> box_id list
  val add_composite_box: box_id -> status -> status

  val get_items: status -> box_id -> box_item list
  val get_init_assums: status -> box_id -> term list
  val get_init_concls: status -> box_id -> term list
  val get_init_vars: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term * retro_handler) list
  val get_all_items: status -> box_id -> box_item list
  val get_all_init_assums: status -> box_id -> term list
  val get_all_init_concls: status -> box_id -> term list
  val get_all_init_vars: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term * retro_handler) list
  val add_item: box_item -> status -> status
  val add_handler: box_id -> (term * retro_handler) -> status -> status
  val lookup_item:
      status -> box_id -> string * term list -> (box_item * box_id list) option
  val lookup_item_all:
      status -> box_id -> string * term list -> (box_item * box_id list) list
  val add_shadowed: box_id * box_item -> status -> status
  val query_shadowed: status -> box_id -> box_item -> bool
  val query_removed: status -> box_item -> bool

  val find_item: status -> box_id -> string * term list -> box_item option
  val find_fact: status -> box_id -> term -> (box_item * thm) option
  val find_ritem_exact: status -> box_id -> raw_item -> box_item option
  val is_triv_eq: status -> box_id -> raw_item -> bool
  val invoke_handler: term * retro_handler -> thm -> thm
  val invoke_handlers: (term * retro_handler) list -> thm -> thm
  val get_neg_form: Proof.context -> term list * term list * term list -> term
  val get_neg_form_thm: Proof.context -> term list * term list * term list ->
                        thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> raw_item
  val find_prim_box: status -> box_id -> term list * term list -> box_id option
  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: Update.update -> status -> status
  val delmin_from_queue: status -> status
end;

structure Status : STATUS =
struct

type status = {
  lat: BoxID.box_lattice,
  boxes: Box.box Boxidtab.table,
  queue: Updates_Heap.T,
  tbl: rewrite_table,
  ctxt: Proof.context
}

fun empty_status ctxt =
    {lat = BoxID.empty, boxes = Boxidtab.empty, queue = Updates_Heap.empty,
     tbl = RewriteTable.empty ctxt, ctxt = ctxt}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id =
    the (Boxidtab.lookup boxes id)
    handle Option.Option => raise AUTO2 "get_box: id not found."

(* Obtain rewrite table contained in st, but with (lhs, rhs) added at
   an additional primitive id.
 *)
fun get_init_type {tbl, ...} = RewriteTable.SINGLE tbl
fun get_incr_type {tbl, ...} id eq_th =
    RewriteTable.LAST (tbl |> RewriteTable.append_rewrite_thm eq_th, id)

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

fun map_box id f {lat, boxes, queue, tbl, ctxt} =
    {lat = lat, boxes = Boxidtab.map_entry id f boxes, queue = queue, tbl = tbl,
     ctxt = ctxt}

fun map_context f {lat, boxes, queue, tbl, ctxt} =
    {lat = lat, boxes = boxes, queue = queue,
     tbl = tbl |> RewriteTable.map_context f, ctxt = f ctxt}

fun map_rewrites f {lat, boxes, queue, tbl, ctxt} =
    {lat = lat, boxes = boxes, queue = queue, tbl = f tbl, ctxt = ctxt}

fun add_prim_box parent_id new_box {lat, boxes, queue, tbl, ctxt} =
    let
      val (id, lat') = BoxID.add_prim_id parent_id lat
    in
      (id, {lat = lat', boxes = Boxidtab.update_new ([id], new_box) boxes,
            queue = queue,
            tbl = RewriteTable.map_lat (K lat') tbl, ctxt = ctxt})
    end

fun set_focus foc {lat, boxes, queue, tbl, ctxt} =
    {lat = lat |> BoxID.set_focus foc, boxes = boxes, queue = queue,
     tbl = tbl |> RewriteTable.map_lat (BoxID.set_focus foc), ctxt = ctxt}

fun add_resolved id {lat, boxes, queue, tbl, ctxt} =
    let
      val lat' = BoxID.add_resolved id lat
    in
      {lat = lat', boxes = boxes, queue = queue,
       tbl = RewriteTable.map_lat (K lat') tbl, ctxt = ctxt}
    end

fun get_all_ids {boxes, ...} = Boxidtab.keys boxes
fun get_resolved st = filter (is_box_resolved st) (get_all_ids st)
fun get_unresolved st = filter_out (is_box_resolved st) (get_all_ids st)

(* Returns list of generalized boxes currently in st that are
   eq-ancestors of id. Note if id is unresolved, then all ancestors of
   id must be unresolved.
 *)
fun get_eq_ancestors st id = filter (is_eq_descendent st id) (get_unresolved st)

(* Add box with the given composite id to status. Assuming this ID is
   not already present in status.
 *)
fun add_composite_box id (st as {lat, boxes, queue, tbl, ctxt}) =
    if exist_box st id then
      raise AUTO2 "Try to add a composite box that already exists"
    else if length id = 1 then
      raise AUTO2 "Try to add a primitive box as a composite"
    else
      {lat = lat,
       boxes = Boxidtab.update_new (id, Box.init_box ([], [], [])) boxes,
       queue = queue, tbl = tbl, ctxt = ctxt}

fun get_for_box f st id = if exist_box st id then f (get_box st id) else []
fun get_all_for_box f st id = maps (get_for_box f st) (get_eq_ancestors st id)
val get_items       = get_for_box Box.get_items
val get_init_assums = get_for_box Box.get_init_assums
val get_init_concls = get_for_box Box.get_init_concls
val get_init_vars   = get_for_box Box.get_init_vars
val get_handlers    = get_for_box Box.get_handlers
val get_all_items       = get_all_for_box Box.get_items
val get_all_init_assums = get_all_for_box Box.get_init_assums
val get_all_init_concls = get_all_for_box Box.get_init_concls
val get_all_init_vars   = get_all_for_box Box.get_init_vars
val get_all_handlers    = get_all_for_box Box.get_handlers

fun add_item (item as {id, ...}) = map_box id (Box.add_item item)

fun add_handler id (t, handler) = map_box id (Box.add_handler (t, handler))

fun lookup_item st id (ty_str, tname) =
    Box.lookup_item (get_box st id) (ty_str, tname)

fun lookup_item_all st id (ty_str, tname) =
    maps (fn id => the_list (lookup_item st id (ty_str, tname)))
         (get_eq_ancestors st id)

fun add_shadowed (shadow_id, {id, ty_str, tname, ...}) (st as {lat, ...}) =
    case lookup_item st id (ty_str, tname) of
        NONE => raise AUTO2 "add_shadowed: item not found."
      | SOME (item, shadow_ids) =>
        let
          val shadow_ids' = (shadow_id :: shadow_ids)
                                |> max_partial (BoxID.is_eq_ancestor lat)
        in
          map_box id (
            Box.map_items (
              ItemTab.update ((ty_str, tname), (item, shadow_ids')))) st
        end

fun query_shadowed st shadow_id {id, ty_str, tname, ...} =
    case lookup_item st id (ty_str, tname) of
        NONE => raise AUTO2 "query_shadowed: item not found."
      | SOME (_, shadow_ids) =>
        exists (is_eq_descendent st shadow_id) shadow_ids

fun query_removed st (item as {id, ...}) = query_shadowed st id item

(* Try to find an item with the given ty_str and tname. *)
fun find_item st id (ty_str, tname) =
    let
      fun match_item (item as {ty_str = ty_str', tname = tname', ...}) =
          if ty_str = ty_str' andalso eq_list (op aconv) (tname, tname') then
            SOME item
          else NONE
    in
      get_first match_item (get_all_items st id)
    end

(* Try to find a box_item at id or ancestors whose term is equivalent
   to t. Return SOME (item, eq) if found, where item has proposition
   t' and eq is t' = t. Otherwise return NONE.
 *)
fun find_fact (st as {tbl, ...}) id t =
    let
      fun match_item item =
          let
            val t' = Thm.prop_of (get_thm item)
            val eq_info = (RewriteTable.equiv_info tbl id (t', t))
                              |> filter (fn (id', _) => id = id')
          in
            case eq_info of
                [] => NONE
              | (_, eq_th) :: _ => SOME (item, eq_th)
          end
    in
      get_first match_item (get_all_items st id)
    end

(* Find item with the exact ty_str and tname, whose id is an
   eq-ancestor of the given id.
 *)
fun find_ritem_exact st id ritem =
    case ritem of
        Handler _ => NONE
      | Fact (ty_str, tname, _) =>
        case lookup_item_all st id (ty_str, tname) of
            [] => NONE
          | item :: _ => SOME (fst item)

(* Whether item (which may be in another id) is a trivial equality
   when considered in the given id.
 *)
fun is_triv_eq {tbl, ...} id ritem =
    if match_ty_str_raw "EQ" ritem then
      RewriteTable.is_equiv id tbl (the_pair (get_tname_raw ritem))
    else false

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
fun get_neg_form ctxt (vars, assums, concls) =
    let
      fun mk_all (nm, T) t = Logic.all_const T $ Term.absfree (nm, T) t
      val facts = assums @ (map get_neg' concls)
    in
      if length facts = 0 then prop_False else
      (* Fold in reverse order, so the facts appear in the right order
         in imps.
       *)
      prop_False |> fold (curry Logic.mk_implies) (rev facts)
                 |> cert ctxt
                 |> rewrite_from_contra_form |> rhs_of
                 |> fold mk_all ((rev o map dest_Free) vars) |> cert ctxt
                 |> to_obj_conv ctxt |> rhs_of
    end

(* Given a theorem th with trms in the hypothesis, return a new
   theorem with trms pulled into the proposition of th, which is
   rewritten into a more human readable form.
 *)
fun get_neg_form_thm ctxt (vars, assums, concls) th =
    let
      val _ = assert (Thm.prop_of th aconv prop_False)
                     "get_neg_form_thm: input should have prop False."
      val facts = assums @ (map get_neg' concls)
    in
      (* Fold in reverse order, so the facts appear in the right order
         in imps.
       *)
      th |> fold Thm.implies_intr ((rev o map (cert ctxt)) facts)
         |> rewrite_thm_from_contra_form
         |> fold Thm.forall_intr ((rev o map (cert ctxt)) vars)
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
      val assums = get_init_assums st [prim_id]
      val concls = get_init_concls st [prim_id]
      val vars = get_init_vars st [prim_id]
      val inits = if prim_id = 0 then ([], assums, concls)
                  else (vars, assums, concls)
      val th'' = get_neg_form_thm ctxt inits th'
      val _ = if prim_id = 0 then
                assert (length (Thm.hyps_of th'') = 0)
                       "get_on_resolve: did not remove all hypothesis at box 0."
              else ()
      val _ = assert (Thm.prop_of th'' aconv get_neg_form ctxt inits)
                     "get_on_resolve: wrong value from get_neg_form_thm."
    in
      thm_to_ritem_ctxt ctxt th''
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box (st as {tbl, ...}) id (assums, concls) =
    let
      fun agree_at_id id' =
          let
            val parent = get_parent_prim st (the_single id')
            val is_equiv = RewriteTable.is_equiv parent tbl
          in
            eq_set is_equiv (assums, get_init_assums st id') andalso
            eq_set is_equiv (concls, get_init_concls st id')
          end

      fun can_test_id id' =
          case id' of
              [prim_id'] => is_eq_ancestor st (get_parent_prim st prim_id') id
            | _ => false

      val ids_to_test = get_unresolved st |> filter can_test_id
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {lat, boxes, queue, tbl, ctxt} =
    {lat = lat, boxes = boxes, queue = f queue, tbl = tbl, ctxt = ctxt}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

end  (* structure Status *)

type status = Status.status
