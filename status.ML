(* Definitions and basic operations on the main data structures, up to
   Status, which represents the state of the proof.
 *)

val TY_NULL = "NULL"
val TY_EQ = "EQ"
val TY_VAR = "VAR"
val TY_PROP = "PROP"
val TY_TERM = "TERM"
val TY_PROPERTY = "PROPERTY"

signature BOXITEM =
sig
  type retro_handler
  datatype raw_item = Handler of term * retro_handler
                    | Fact of string * term * thm
  (* Facts. *)
  val var_to_fact: term -> raw_item
  val term_to_fact: term -> raw_item
  val is_fact_raw: raw_item -> bool
  val get_thm_raw: raw_item -> thm
  val get_ty_str_raw: raw_item -> string
  val match_ty_str_raw: string -> raw_item -> bool
  val match_ty_strs_raw: string list -> raw_item -> bool
  val get_tname_raw: raw_item -> term
  (* Handlers. *)
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term * retro_handler
  (* Misc. functions. *)
  val eq_ritem: raw_item * raw_item -> bool
  val subst_th: (cterm * cterm) list -> thm -> thm
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val obtain_variant_frees:
      Proof.context * raw_item list -> Proof.context * (cterm * cterm) list

  type box_item
  val null_item: box_item
  val uid_of_item: box_item -> int
  val score_of_item: box_item -> int
  val get_thm: box_item -> thm
  val get_ty_str: box_item -> string
  val match_ty_str: string -> box_item -> bool
  val match_ty_strs: string list -> box_item -> bool
  val get_tname: box_item -> term
  (* Misc. functions. *)
  val merged_id: box_lattice -> box_item list -> box_id
  val mk_box_item: int * box_id * int * raw_item -> box_item
end;

structure BoxItem : BOXITEM =
struct

type retro_handler = (term * term list -> bool) * (term * thm -> thm)
datatype raw_item = Handler of term * retro_handler
                  | Fact of string * term * thm

fun var_to_fact t = Fact (TY_VAR, t, true_th)
fun term_to_fact t = Fact (TY_TERM, t, true_th)

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
                | _ => raise AUTO2 "get_tname_raw: wrong type"

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
       get_tname_raw ritem1 aconv get_tname_raw ritem2 andalso
       Thm.eq_thm_prop (get_thm_raw ritem1, get_thm_raw ritem2))
    else false

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
          ritems |> filter (match_ty_str_raw TY_VAR) |> map get_tname_raw
                 |> filter is_Free |> map dest_Free
                 |> filter (is_just_internal o fst)
      (* New names for these variables. *)
      val all_vars' =
          all_vars |> map (fn (nm, T) => (Name.dest_internal nm, T))
                   |> Variable.variant_frees ctxt []
      val subst = map (apply2 (cert ctxt o Free)) (all_vars ~~ all_vars')
    in
      (fold declare_free_term (map Free all_vars') ctxt, subst)
    end

(* Replace using subst the internal variables in th. This proceeds in
   several steps: first, pull any hypotheses of the theorem involving
   the replaced variables into statement of the theorem, perform the
   replacement (using forall_intr then forall_elim), finally return
   the hypotheses to their original place.
 *)
fun subst_th subst th =
    let
      val old_cts = map fst subst
      val old_ts = map Thm.term_of old_cts
      val new_cts = map snd subst
      val chyps = filter (fn ct => has_subterm old_ts (Thm.term_of ct))
                         (Thm.chyps_of th)
    in
      th |> fold Thm.implies_intr chyps
         |> fold Thm.forall_intr old_cts
         |> fold Thm.forall_elim (rev new_cts)
         |> send_all_to_hyps
    end

(* Here inst is the return value of obtain_variant_frees. Perform the
   replacement on the ritems.
 *)
fun instantiate subst ritem =
    let
      val subst_fun = Term.subst_atomic (map (apply2 Thm.term_of) subst)
    in
      case ritem of
          Handler (t, handler) => Handler (subst_fun t, handler)
        | Fact (ty_str, tname, th) =>
          Fact (ty_str, subst_fun tname, subst_th subst th)
    end

type box_item =
     {uid: int, id: box_id, sc: int, ty_str: string, tname: term, prop: thm}
val null_item = {uid = 0, id = [], sc = 0, ty_str = TY_NULL,
                 tname = HOLogic.unit, prop = true_th}
fun uid_of_item {uid, ...} = uid
fun score_of_item {sc, ...} = sc
fun get_thm {prop, ...} = prop
fun get_ty_str {ty_str, ...} = ty_str
fun match_ty_str s {ty_str, ...} = (s = "" orelse s = ty_str)
fun match_ty_strs slist {ty_str, ...} = member (op =) slist ty_str
fun get_tname {tname, ...} = tname

fun merged_id lat items =
    let
      fun merge items =
          case items of
              [] => []
            | {id, ...} :: items' => BoxID.merge_boxes lat (id, merge items')
    in
      merge items
    end

fun mk_box_item (uid, id, sc, ritem) =
    case ritem of
        Handler _ => raise AUTO2 "mk_box_item: ritem must be Fact"
      | Fact (ty_str, tname, prop) =>
        {uid = uid, id = id, sc = sc, ty_str = ty_str, tname = tname,
         prop = prop}

end  (* structure BoxItem. *)

open BoxItem

(* Specifies a method for matching patterns against items.

   - pre_match is a filter function checking whether it is possible
     for the pattern to match the item, after possibly instantiating
     some schematic variables in the pattern (for example, this
     function should always return true if input pattern is ?A).

   - match is the actual matching function, returning instantiation,
     as well as theorem justifying the instantiated pattern.

   If the matcher is for justifying a proposition, the input term to
   pre_match and match is of type bool. Othewise, the restrictions
   depend on type of item to match.
 *)
type item_matcher = {
  pre_match: term -> box_item -> rewrite_table -> bool,
  match: term -> box_item -> rewrite_table -> id_inst -> id_inst_th list
}

(* Output function for items of a given type. *)
type item_output = Proof.context -> term * thm -> string

(* Data structure containing methods involved in the input / output of
   items of a given type.

   - prop_matchers: methods for matching the item against a desired
     proposition.

   - typed_matchers: methods for matching the item against a pattern
     for items of the same type.

   - output_fn: printing function of theorems. Input is tname and the
     proposition.
 *)
type item_io_info = {
  prop_matchers: item_matcher list, typed_matchers: item_matcher list,
  output_fn: item_output option}

fun add_prop_matcher_to_info mtch {prop_matchers, typed_matchers, output_fn} =
    {prop_matchers = mtch :: prop_matchers,
     typed_matchers = typed_matchers, output_fn = output_fn}

fun add_typed_matcher_to_info mtch {prop_matchers, typed_matchers, output_fn} =
    {prop_matchers = prop_matchers,
     typed_matchers = mtch :: typed_matchers, output_fn = output_fn}

fun join_infos ({prop_matchers = pm1, typed_matchers = tm1, output_fn = of1},
                {prop_matchers = pm2, typed_matchers = tm2, output_fn = of2}) =
    {prop_matchers = merge pointer_eq (pm1, pm2),
     typed_matchers = merge pointer_eq (tm1, tm2),
     output_fn = (if pointer_eq (of1, of2) then of1
                  else raise AUTO2 "join_infos: output non-equal")}

structure ItemIOData =
Theory_Data (
  type T = item_io_info Symtab.table
  val empty = Symtab.empty
  val extend = I;
  val merge = Symtab.join (fn _ => join_infos)
)

datatype match_arg = PropMatch of term
                   | TypedMatch of string * term
                   | PropertyMatch of term

fun pat_of_match_arg arg =
    case arg of
        PropMatch pat => pat
      | TypedMatch (_, pat) => pat
      | PropertyMatch pat => pat

fun subst_arg inst arg =
    case arg of
        PropMatch pat => PropMatch (subst_term_norm inst pat)
      | TypedMatch (ty_str, pat) =>
        TypedMatch (ty_str, subst_term_norm inst pat)
      | PropertyMatch pat =>
        PropertyMatch (subst_term_norm inst pat)

fun assert_valid_arg arg =
    case arg of
        PropMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropMatch should be bool."
      | TypedMatch _ => ()
      | PropertyMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropertyMatch should be bool."

fun check_ty_str ty_str arg =
    case arg of
        TypedMatch (ty_str', _) => ty_str = ty_str'
      | _ => true

fun is_property_match arg =
    case arg of PropertyMatch _ => true | _ => false

signature ITEM_IO_DATA =
sig
  val add_item_type: string * item_output option -> theory -> theory
  val add_prop_matcher: string * item_matcher -> theory -> theory
  val add_typed_matcher: string * item_matcher -> theory -> theory
  val get_io_info: theory -> string -> item_io_info
  val get_prop_matchers: theory -> string -> item_matcher list
  val get_typed_matchers: theory -> string -> item_matcher list
  val univ_matcher: item_matcher
  val prop_matcher: item_matcher
  val term_prop_matcher: item_matcher
  val term_typed_matcher: item_matcher
  val null_property_matcher: item_matcher
  val term_property_matcher: item_matcher
  val pre_match_arg: rewrite_table -> match_arg -> box_item -> bool
  val match_arg: rewrite_table -> match_arg -> box_item -> id_inst ->
                 id_inst_th list
  val output_prop_fn: item_output
  val string_of_item_info: Proof.context -> string * term * thm -> string
  val add_basic_item_io: theory -> theory
end;

structure ItemIO_Data : ITEM_IO_DATA =
struct

fun add_item_type (ty_str, output_fn) = ItemIOData.map (
      Symtab.update_new (ty_str, {prop_matchers = [], typed_matchers = [],
                                  output_fn = output_fn}))

fun add_prop_matcher (ty_str, it_match) = ItemIOData.map (
      Symtab.map_entry ty_str (add_prop_matcher_to_info it_match))

fun add_typed_matcher (ty_str, it_match) = ItemIOData.map (
      Symtab.map_entry ty_str (add_typed_matcher_to_info it_match))

fun get_io_info thy ty_str =
    the (Symtab.lookup (ItemIOData.get thy) ty_str)
    handle Option.Option => raise AUTO2 ("get_io_info: not found " ^ ty_str)

fun get_prop_matchers thy ty_str = #prop_matchers (get_io_info thy ty_str)
fun get_typed_matchers thy ty_str = #typed_matchers (get_io_info thy ty_str)

val univ_matcher =
    {pre_match = fn _ => fn _ => fn _ => true,
     match = fn _ => fn _ => fn _ => fn (id, inst) => [((id, inst), true_th)]}

(* Prop-matching with a PROP item. *)
val prop_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          if is_neg pat then
            is_neg tname andalso
            Matcher.pre_match_head tbl (get_neg pat, get_neg tname)
          else  (* not (is_neg pat) *)
            not (is_neg tname) andalso Matcher.pre_match_head tbl (pat, tname)

      fun match pat {tname, prop, ...} tbl (id, inst) =
          if is_neg pat andalso is_neg tname then
            let
              val insts' = Matcher.rewrite_match_head
                               tbl (get_neg pat, get_neg tname) (id, inst)
              fun process_inst (inst, eq_th) =
                  (inst, Thm.equal_elim (
                     make_trueprop_eq (make_neg_eq (meta_sym eq_th))) prop)
            in
              map process_inst insts'
            end
          else if not (is_neg pat) andalso not (is_neg tname) then
            let
              val insts' = Matcher.rewrite_match_head
                               tbl (pat, tname) (id, inst)
              fun process_inst (inst, eq_th) =
                  (inst, Thm.equal_elim (
                     make_trueprop_eq (meta_sym eq_th)) prop)
            in
              map process_inst insts'
            end
          else []
    in
      {pre_match = pre_match, match = match}
    end

(* Prop-matching with a TERM item (used to justify equalities). *)
val term_prop_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          case pat of
              Const ("HOL.eq", _) $ lhs $ _ =>
              Matcher.pre_match tbl (lhs, tname)
            | _ => false

      fun match pat {tname = u, ...} tbl (id, inst) =
          if fastype_of pat <> boolT orelse not (is_eq_term pat) then [] else
          let
            val (lhs, rhs) = pat |> HOLogic.dest_eq
            val pairs =
                if Term.is_Var lhs then [(false, (lhs, u)), (true, (rhs, u))]
                else [(true, (lhs, u)), (false, (rhs, u))]
            val insts' = Matcher.rewrite_match_list tbl pairs (id, inst)
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
    in
      {pre_match = pre_match, match = match}
    end

(* Typed matching with a TERM item. *)
val term_typed_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          Matcher.pre_match_head tbl (pat, tname)

      (* Return value is (inst, eq), where eq is pat(inst) == tname. *)
      fun match pat {tname, ...} tbl (id, inst) =
          Matcher.rewrite_match_head tbl (pat, tname) (id, inst)
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table. *)
val null_property_matcher =
    let
      fun pre_match pat _ tbl =
          is_property_const (RewriteTable.theory_of tbl) pat

      fun match pat _ tbl (id, inst) =
          if has_vars pat then [] else
          if not (is_property_const (RewriteTable.theory_of tbl) pat) then []
          else map (fn (id', th) => ((id', inst), th))
                   (RewriteTable.get_property tbl (id, pat))
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table, matching the argument
   of the property with the given term.
 *)
val term_property_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          is_property_const (RewriteTable.theory_of tbl) pat andalso
          Matcher.pre_match_head tbl (get_property_arg pat, tname)

      fun match pat {tname, ...} tbl (id, inst) =
          if not (has_vars pat) then [] else
          if not (is_property_const (RewriteTable.theory_of tbl) pat) then []
          else let
            val arg = get_property_arg pat
          in
            let
              val insts' =
                  Matcher.rewrite_match_head tbl (arg, tname) (id, inst)
              fun process_inst ((id', inst'), _) =
                  let
                    val t = subst_term_norm inst' pat
                  in
                    map (fn (id'', th) => ((id'', inst'), th))
                        (RewriteTable.get_property tbl (id', t))
                  end
            in
              maps process_inst insts'
            end
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Generic pre-matching function. Returns whether there is a possible
   match among any of the registered matchers.
 *)
fun pre_match_arg tbl arg (item as {ty_str, ...}) =
    if not (check_ty_str ty_str arg) then false else
    let
      val _ = assert_valid_arg arg
      val thy = RewriteTable.theory_of tbl
      val {prop_matchers, typed_matchers, ...} = get_io_info thy ty_str
      val pat = pat_of_match_arg arg
    in
      if not (is_pattern pat) then true else
      case (arg, pat) of
          (PropMatch _, Var _) => true
        | (PropMatch _, Const ("HOL.Not", _) $ Var _) => true
        | (PropMatch _, _) =>
          exists (fn f => f pat item tbl) (map #pre_match prop_matchers)
        | (TypedMatch _, _) =>
          exists (fn f => f pat item tbl) (map #pre_match typed_matchers)
        | (PropertyMatch _, _) =>
          raise AUTO2 "pre_match_arg: should not be called on PropertyMatch."
    end

(* Generic matching function. Returns list of all matches (iterating
   over all registered matchers for the given item type. Note box_id
   for item is taken into account here.
 *)
fun match_arg (tbl as {lat, ...}) arg (item as {id, ty_str, ...}) (id', inst) =
    if not (check_ty_str ty_str arg) then [] else
    let
      val _ = assert_valid_arg arg
      val thy = RewriteTable.theory_of tbl
      val {prop_matchers, typed_matchers, ...} = get_io_info thy ty_str
      val pat = pat_of_match_arg arg
      val id'' = BoxID.merge_boxes lat (id, id')
    in
      case arg of
          PropMatch _ => maps (fn f => f pat item tbl (id'', inst))
                              (map #match prop_matchers)
        | TypedMatch _ => maps (fn f => f pat item tbl (id'', inst))
                               (map #match typed_matchers)
        | PropertyMatch _ =>
          raise AUTO2 "match_arg: should not be called on PropertyMatch."
    end

fun output_prop_fn ctxt (_, th) = Thm.prop_of th |> pretty_term ctxt |> str

fun string_of_item_info ctxt (ty_str, tname, th) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {output_fn, ...} = get_io_info thy ty_str
    in
      case output_fn of
          NONE => ty_str ^ " " ^ (tname |> pretty_term ctxt |> str)
        | SOME f => f ctxt (tname, th)
    end

val add_basic_item_io =
    fold add_item_type [
      (TY_NULL, NONE), (TY_PROP, SOME output_prop_fn), (TY_TERM, NONE),
      (TY_EQ, SOME output_prop_fn), (TY_VAR, NONE), (TY_PROPERTY, NONE)

    ] #> fold add_prop_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_prop_matcher),
      (TY_NULL, null_property_matcher), (TY_TERM, term_property_matcher)

    ] #> fold add_typed_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_typed_matcher),
      (TY_VAR, term_typed_matcher), (TY_EQ, term_typed_matcher)
    ]

end  (* structure ItemIO_Data. *)

fun string_of_raw_item ctxt ritem =
    case ritem of
        Handler (t, _) => "Handler " ^ (t |> pretty_term ctxt |> str)
      | Fact info => ItemIO_Data.string_of_item_info ctxt info
fun string_of_item ctxt ({ty_str, tname, prop, ...}:box_item) =
    ItemIO_Data.string_of_item_info ctxt (ty_str, tname, prop)

val _ = Theory.setup ItemIO_Data.add_basic_item_io

signature UPDATE =
sig
  datatype update_type = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
  datatype init_info = InitVar of term | InitAssum of term
  type resolve_callback
  datatype raw_update
    = AddItems of {id: box_id, raw_items: raw_item list}
    | AddBoxes of {id: box_id, inits: init_info list,
                   cbs: resolve_callback list}
    | ResolveBox of {id: box_id, th: thm}
    | ShadowItem of {id: box_id, item: box_item}
  type update
  val dest_init_var: init_info -> term list
  val dest_init_assum: init_info -> term list
  val build_init_infos: term list * term list -> init_info list
  val string_of_init_info: Proof.context -> init_info -> string
  val get_neg_form: Proof.context -> init_info list -> term
  val get_neg_form_thm: Proof.context -> init_info list -> thm -> thm

  val type_of_update: raw_update -> update_type
  val string_of_update_type: update_type -> string
  val string_of_raw_update: Proof.context -> raw_update -> string
  val null_callback: resolve_callback
  val thm_to_ritem: thm -> raw_item
  val thm_update: box_id * thm -> raw_update
  val extract_init_infos: term -> init_info list

  val handler_ritems: Proof.context -> term -> retro_handler -> raw_item list
  val apply_horn_clause: box_id * thm -> resolve_callback -> raw_update list
  val apply_exists_ritems: thm -> Proof.context -> string list ->
                           raw_item list * thm
  val apply_exists: box_id * thm -> Proof.context -> string list ->
                    raw_update list
  val get_apply_exists_nms: thm -> string list
  val target_of_update: raw_update -> box_id
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: update -> string
end;

structure Update : UPDATE =
struct

datatype update_type = ADD_ITEMS | ADD_BOXES | RESOLVE_BOX | SHADOW_ITEM
datatype init_info = InitVar of term | InitAssum of term
datatype raw_update
  = AddItems of {id: box_id, raw_items: raw_item list}
  | AddBoxes of {id: box_id, inits: init_info list,
                 cbs: (box_id * thm -> raw_update list) list}
  | ResolveBox of {id: box_id, th: thm}
  | ShadowItem of {id: box_id, item: box_item}
type resolve_callback = box_id * thm -> raw_update list
type update = {sc: int, prfstep_name: string, source: box_item list,
               raw_updt: raw_update}

fun dest_init_var init = case init of InitVar t => [t] | _ => []
fun dest_init_assum init = case init of InitAssum t => [t] | _ => []
fun build_init_infos (vars, assums) = map InitVar vars @ map InitAssum assums
fun string_of_init_info ctxt init =
    case init of
        InitVar t => ("Var " ^ (t |> pretty_term ctxt |> str))
      | InitAssum assum => ("Assum " ^ (assum |> pretty_term ctxt |> str))

(* Given list of initial variables and assumptions, return the
   contradiction derived from them. Each initial variable becomes !,
   the last assumption is negated, and each assumption before the last
   becomes -->.
 *)
fun get_neg_form ctxt inits =
    if length inits = 0 then @{prop False}
    else let
      fun mk_all (nm, T) t = Logic.all_const T $ Term.absfree (nm, T) t
      val concl = inits |> List.last |> dest_init_assum |> the_single
                        |> get_neg'
                  handle List.Empty =>
                         raise AUTO2 "get_neg_form: last init should be prop."

      fun fold_init init t =
          case init of
              InitVar v => mk_all (dest_Free v) t
            | InitAssum assum => Logic.mk_implies (assum, t)
    in
      concl |> fold fold_init (tl (rev inits)) |> cert ctxt
            |> to_obj_conv ctxt |> rhs_of
    end

(* Given a contradiction th, returns a new theorem with assumptions
   pulled into the proposition of th. The resulting form of th is the
   same as that returned by get_neg_form.
 *)
fun get_neg_form_thm ctxt inits th =
    if length inits = 0 then th
    else let
      val _ = assert (Thm.prop_of th aconv prop_False)
                     "get_neg_form_thm: input th should be a contradiction."
      val tl_assum =
          inits |> List.last |> dest_init_assum |> the_single
          handle List.Empty =>
                 raise AUTO2 "get_neg_form_thm: last init should be prop."

      fun fold_init init th =
          case init of
              InitVar v => Thm.forall_intr (cert ctxt v) th
            | InitAssum assum => th |> Thm.implies_intr (cert ctxt assum)
    in
      th |> Thm.implies_intr (cert ctxt tl_assum)
         |> rewrite_thm_from_contra_form
         |> fold fold_init (tl (rev inits))
         |> apply_to_thm (to_obj_conv ctxt)
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
        AddItems {id, raw_items} =>
        "Add items " ^ (string_of_list (string_of_raw_item ctxt) raw_items) ^
        " to box " ^ (string_of_box_id id)
      | AddBoxes {id, inits, ...} =>
        "Add box " ^ (string_of_list (string_of_init_info ctxt) inits) ^
        " under box " ^ (string_of_box_id id)
      | ResolveBox {id, ...} =>
        "Resolve box " ^ (string_of_box_id id)
      | ShadowItem {id, item} =>
        "Shadow item " ^ (string_of_item ctxt item) ^
        " in box " ^ (string_of_box_id id)

val null_callback = K []

fun thm_to_ritem th =
    let
      val prop = Thm.prop_of th
      val _ = assert (is_Trueprop prop) "thm_update: prop is not Trueprop."
      val _ = assert (not (has_vars prop))
                     "thm_update: prop contains schematic variables."
      val prop' = HOLogic.dest_Trueprop prop
      val thy = Thm.theory_of_thm th
    in
      if is_eq_term prop' then
        Fact (TY_EQ, HOLogic.mk_prod (HOLogic.dest_eq prop'), th)
      else if is_property_const thy prop' then
        Fact (TY_PROPERTY, prop', th)
      else
        Fact (TY_PROP, prop', th)
    end

fun thm_update (id, th) =
    if Thm.prop_of th aconv prop_False then
      ResolveBox {id = id, th = th}
    else
      AddItems {id = id, raw_items = [thm_to_ritem th]}

fun extract_init_infos t =
    case t of
        Const ("HOL.All", _) $ Abs (nm, T, b) =>
        InitVar (Free (nm, T)) ::
        extract_init_infos (Term.subst_bound (Free (nm, T), b))
      | Const ("Set.Ball", _) $ S $ Abs (nm, T, b) =>
        InitVar (Free (nm, T)) ::
        InitAssum (HOLogic.mk_Trueprop (HOLogic.mk_mem (Free (nm, T), S))) ::
        extract_init_infos (Term.subst_bound (Free (nm, T), b))
      | Const ("HOL.implies", _) $ P $ Q =>
        InitAssum (HOLogic.mk_Trueprop P) :: extract_init_infos Q
      | _ => [InitAssum (HOLogic.mk_Trueprop (get_neg t))]

fun handler_ritems ctxt t handler =
    let
      val _ = assert (fastype_of t = propT) "handler_ritems: wrong type"
    in
      [Handler (t, handler), thm_to_ritem (assume_thm ctxt t)]
    end

fun apply_horn_clause (id, th) cb =
    case Thm.prop_of th of
        Const ("Pure.imp", _) $ A $ _ =>
        let
          val (vars, body) = strip_obj_all_var (HOLogic.dest_Trueprop A)
          val (assums, concl) = strip_obj_imp body
          val inits = map InitVar vars @
                      map (InitAssum o HOLogic.mk_Trueprop) assums @
                      [InitAssum (HOLogic.mk_Trueprop (get_neg concl))]
          fun callback (id', th_fst) =
              apply_horn_clause (id', [th_fst] MRS th) cb
        in
          [AddBoxes {id = id, inits = inits, cbs = [callback]}]
        end
      | _ => if pointer_eq (cb, null_callback) then [thm_update (id, th)]
             else cb (id, th)

(* nms specify the names of free variables, either internal (use
   obtain_variant_frees to fix) or otherwise (will be put into context
   as is). This function returns the list of VAR items and handlers,
   paired with the theorem produced.
 *)
fun apply_exists_ritems ex_th ctxt nms =
    let
      fun dest_one_abs nm t =
          case t of
              Const("HOL.Ex", _) $ Abs (_, T, body) =>
              let
                val (nm', body') = Term.dest_abs (nm, T, body)
                val _ = assert (nm = nm') "apply_exists: name clash"
              in
                ((nm, T), body')
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

      val ex_th' = apply_to_thm' (normalize_exs_conv (length nms) ctxt) ex_th
      val (vars, new_prop) = ex_th' |> prop_of' |> dest_all_abs nms
      val new_prop' = HOLogic.mk_Trueprop new_prop
      val new_th = new_prop' |> cert ctxt |> Thm.assume

      (* Given two terms t and u, where t may contain internal
         variables, find replacements for those internal variables so
         that t agrees with u. If there is no match, return the empty
         list.
       *)
      fun match_vars_one (t, u) =
          let
            val all_internal_vars =
                (Term.add_frees t [])
                    |> filter (fn (nm, _) => is_just_internal nm)
            fun subst_for_var (nm, T) =
                [(Free (nm, T), Var ((nm, 0), T))]
            val subst = maps subst_for_var all_internal_vars

            val pat = Term.subst_atomic subst t
            val inst = pattern_fo_match ctxt (pat, u)
            fun get_freevar (nm, T) = ((nm, T), lookup_inst inst nm)
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
          (maps match_vars_one (all_pairs (ts, us)))
              |> distinct (eq_pair (op =) (op aconv))

      (* Find new versions of vars by matching new_prop' and t. *)
      fun get_freevars t =
          let
            val subst = match_vars_one (new_prop', t)
            fun get_freevar (nm, T) =
                if not (is_just_internal nm) then Free (nm, T) else
                the (AList.lookup (op =) subst (nm, T))
                handle Option.Option =>
                       raise AUTO2 "get_freevars: cannot match new_prop' and t"
          in
            map get_freevar vars
          end

      fun ready (t, ts) =
          let
            val fvars = get_freevars t
          in
            forall (fn t' => t' aconv t orelse not (occurs_frees fvars t')) ts
          end

      fun handler (t, th) =
          let
            val subst = (match_vars (Thm.hyps_of ex_th', Thm.hyps_of th))
                            |> map (fn ((nm, T), t) =>
                                       (cert ctxt (Free (nm, T)), cert ctxt t))
            val fvars = get_freevars t
          in
            th |> Thm.implies_intr (cert ctxt t)
               |> fold (ex_elim ctxt) (rev fvars)
               |> Thm.elim_implies (subst_th subst ex_th')
          end

      val ritems = (map (var_to_fact o Free) vars) @
                   [Handler (new_prop', (ready, handler))]
    in
      (ritems, new_th)
    end

(* Calls the previous function, and directly produces the update. *)
fun apply_exists (id, ex_th) ctxt nms =
    let
      val (ritems, new_th) = apply_exists_ritems ex_th ctxt nms
    in
      [AddItems {id = id, raw_items = ritems @ [thm_to_ritem new_th]}]
    end

(* Given existence theorem, return list of suggested names of new
   variables, obtained from name hints of EX quantifiers.
 *)
fun get_apply_exists_nms th =
    let
      fun helper t =
          case t of
              Const ("HOL.Ex", _) $ Abs (abs as (nm, _, _)) =>
              let val (_, body) = Term.dest_abs abs in
                nm :: helper body
              end
            | _ => []
    in
      (Name.variant_list [] (helper (prop_of' th)))
          |> map Name.internal
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

fun uid_string_of_item {uid, ...} = "(" ^ string_of_int uid ^ ")"

fun source_info {prfstep_name, source, ...} =
    prfstep_name ^ " on " ^ (string_of_list' (uid_string_of_item) source)

end  (* structure Update. *)

structure ItemTab =
Table (
  type key = string * term
  val ord = prod_ord string_ord Term_Ord.fast_term_ord
);

signature BOX =
sig
  type box
  val init_box: Update.init_info list -> box
  val get_inits: box -> Update.init_info list
  val get_init_vars: box -> term list
  val get_init_assums: box -> term list

  val add_handler: term * retro_handler -> box -> box
  val get_handlers: box -> (term * retro_handler) list

  val map_items: ((box_item * box_id list) ItemTab.table ->
                  (box_item * box_id list) ItemTab.table) -> box -> box
  val add_item: box_item -> box -> box
  val is_item_removed: box_item * box_id list -> bool
  val get_items: box -> box_item list
  val lookup_item: box -> string * term -> (box_item * box_id list) option
  val get_freevars: box -> term list
  val get_dep_vars: box -> term list

  val add_callback: Update.resolve_callback -> box -> box
  val get_callbacks: box -> Update.resolve_callback list

  val set_resolve_th: thm -> box -> box
  val get_resolve_th: box -> thm

  val short_string_of_box: Proof.context -> box -> string
end;

structure Box : BOX =
struct

type box = {inits: Update.init_info list,
            handlers: (term * retro_handler) list,
            items: (box_item * box_id list) ItemTab.table,
            cbs: Update.resolve_callback list, resolve_th: thm option}
fun init_box inits = {inits = inits, handlers = [], items = ItemTab.empty,
                      cbs = [], resolve_th = NONE}
fun get_inits {inits, ...} = inits
fun get_init_vars {inits, ...} = maps Update.dest_init_var inits
fun get_init_assums {inits, ...} = maps Update.dest_init_assum inits

fun add_handler (t, handler) {inits, handlers, items, cbs, resolve_th} =
    {inits = inits, handlers = cons (t, handler) handlers, items = items,
     cbs = cbs, resolve_th = resolve_th}
fun get_handlers {handlers, ...} = handlers

fun map_items f {inits, handlers, items, cbs, resolve_th} =
    {inits = inits, handlers = handlers, items = f items, cbs = cbs,
     resolve_th = resolve_th}

fun add_item (item as {ty_str, tname, ...}) =
    map_items (ItemTab.update_new ((ty_str, tname), (item, [])))
    handle ItemTab.DUP _ => raise AUTO2 "add_item: item already exists."

fun is_item_removed ({id, ...}, shadow_ids) =
    member (op =) shadow_ids id

fun get_items {items, ...} =
    ItemTab.dest items |> map snd |> filter_out is_item_removed |> map fst

fun lookup_item {items, ...} (ty_str, tname) =
    ItemTab.lookup items (ty_str, tname)

val get_freevars = map get_tname o filter (match_ty_str TY_VAR) o get_items
fun get_dep_vars box =
    subtract (op aconv) (get_init_vars box) (get_freevars box)

fun add_callback cb {inits, handlers, items, cbs, resolve_th} =
    {inits = inits, handlers = handlers, items = items, cbs = cons cb cbs,
     resolve_th = resolve_th}
fun get_callbacks {cbs, ...} = cbs

fun set_resolve_th th {inits, handlers, items, cbs, ...} =
    {inits = inits, handlers = handlers, items = items, cbs = cbs,
     resolve_th = SOME th}

fun get_resolve_th {resolve_th, ...} =
    case resolve_th of
        NONE => raise AUTO2 "get_resolve_th: box not resolved."
      | SOME th => th

fun short_string_of_box ctxt {inits, ...} =
    Update.get_neg_form ctxt inits |> pretty_term ctxt |> str

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
  val merge_boxes: status -> box_id * box_id -> box_id
  val is_ancestor: status -> box_id -> box_id -> bool
  val is_descendent: status -> box_id -> box_id -> bool
  val is_eq_ancestor: status -> box_id -> box_id -> bool
  val is_eq_descendent: status -> box_id -> box_id -> bool
  val is_box_resolved: status -> box_id -> bool
  val is_box_unresolved: status -> box_id -> bool

  val incr_uid_next: status -> status
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
  val get_inits: status -> box_id -> Update.init_info list
  val get_init_vars: status -> box_id -> term list
  val get_init_assums: status -> box_id -> term list
  val get_handlers: status -> box_id -> (term * retro_handler) list
  val get_all_items: status -> box_id -> box_item list
  val get_all_inits: status -> box_id -> Update.init_info list
  val get_all_init_vars: status -> box_id -> term list
  val get_all_init_assums: status -> box_id -> term list
  val get_all_handlers: status -> box_id -> (term * retro_handler) list
  val add_item: box_item -> status -> status
  val add_handler: box_id -> (term * retro_handler) -> status -> status
  val lookup_item:
      status -> box_id -> string * term -> (box_item * box_id list) option
  val lookup_item_all:
      status -> box_id -> string * term -> (box_item * box_id list) list
  val add_shadowed: box_id * box_item -> status -> status
  val query_shadowed: status -> box_id -> box_item -> bool
  val query_removed: status -> box_item -> bool
  val set_resolve_th: box_id -> thm -> status -> status
  val get_resolve_th: status -> box_id -> thm

  val is_term_present: status -> term -> bool
  val find_fact: status -> box_id -> term -> (box_item * thm) option
  val find_ritem_exact: status -> box_id -> raw_item -> box_item option
  val is_triv_eq: status -> box_id -> raw_item -> bool
  val invoke_handler: term * retro_handler -> thm -> thm
  val invoke_handlers: (bool * (term * retro_handler)) list -> thm -> thm
  val get_on_resolve: status -> box_id -> int -> thm -> raw_item
  val find_prim_box: status -> box_id -> Update.init_info list -> box_id option
  val map_queue: (Updates_Heap.T -> Updates_Heap.T) -> status -> status
  val add_to_queue: Update.update -> status -> status
  val delmin_from_queue: status -> status
end;

structure Status : STATUS =
struct

type status = {
  uid_next: int,
  lat: BoxID.box_lattice,
  boxes: Box.box Boxidtab.table,
  queue: Updates_Heap.T,
  tbl: rewrite_table,
  ctxt: Proof.context
}

fun empty_status ctxt =
    {uid_next = 1, lat = BoxID.empty, boxes = Boxidtab.empty,
     queue = Updates_Heap.empty, tbl = RewriteTable.empty ctxt, ctxt = ctxt}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id =
    the (Boxidtab.lookup boxes id)
    handle Option.Option => raise AUTO2 "get_box: id not found."

fun get_init_type {tbl, ...} = RewriteTable.SINGLE tbl

(* Obtain incremental rtype. Distinguish between when th is an
   equality or a property. Add the theorem under an additional
   primitive id.
 *)
fun get_incr_type {tbl, ...} id th =
    if is_property_const (RewriteTable.theory_of tbl) (prop_of' th) then
      RewriteTable.LAST (tbl |> RewriteTable.append_property th, id)
    else if is_eq_term (prop_of' th) then
      RewriteTable.LAST (tbl |> RewriteTable.append_rewrite th, id)
    else
      raise AUTO2 "get_incr_type: wrong form of theorem."

fun get_lattice {lat, ...} = lat
val get_focus = BoxID.get_focus o get_lattice
val get_parent_prim = BoxID.get_parent_prim o get_lattice
val merge_boxes = BoxID.merge_boxes o get_lattice
val is_ancestor = BoxID.is_ancestor o get_lattice
val is_descendent = BoxID.is_descendent o get_lattice
val is_eq_ancestor = BoxID.is_eq_ancestor o get_lattice
val is_eq_descendent = BoxID.is_eq_descendent o get_lattice
val is_box_resolved = BoxID.is_box_resolved o get_lattice
val is_box_unresolved = BoxID.is_box_unresolved o get_lattice

fun incr_uid_next {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next + 1, lat = lat, boxes = boxes, queue = queue,
     tbl = tbl, ctxt = ctxt}

fun map_box id f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = Boxidtab.map_entry id f boxes,
     queue = queue, tbl = tbl, ctxt = ctxt}

fun map_context f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = boxes, queue = queue,
     tbl = tbl |> RewriteTable.map_context f, ctxt = f ctxt}

fun map_rewrites f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = boxes, queue = queue, tbl = f tbl,
     ctxt = ctxt}

fun add_prim_box parent_id new_box {uid_next, lat, boxes, queue, tbl, ctxt} =
    let
      val (id, lat') = BoxID.add_prim_id parent_id lat
    in
      (id, {uid_next = uid_next, lat = lat',
            boxes = Boxidtab.update_new ([id], new_box) boxes, queue = queue,
            tbl = RewriteTable.map_lat (K lat') tbl, ctxt = ctxt})
    end

fun set_focus foc {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat |> BoxID.set_focus foc, boxes = boxes,
     queue = queue, tbl = tbl |> RewriteTable.map_lat (BoxID.set_focus foc),
     ctxt = ctxt}

fun add_resolved id {uid_next, lat, boxes, queue, tbl, ctxt} =
    let
      val lat' = BoxID.add_resolved id lat
    in
      {uid_next = uid_next, lat = lat', boxes = boxes, queue = queue,
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
fun add_composite_box id (st as {uid_next, lat, boxes, queue, tbl, ctxt}) =
    if exist_box st id then
      raise AUTO2 "Try to add a composite box that already exists"
    else if length id = 1 then
      raise AUTO2 "Try to add a primitive box as a composite"
    else
      {uid_next = uid_next, lat = lat,
       boxes = Boxidtab.update_new (id, Box.init_box []) boxes,
       queue = queue, tbl = tbl, ctxt = ctxt}

fun get_for_box f st id = if exist_box st id then f (get_box st id) else []
fun get_all_for_box f st id = maps (get_for_box f st) (get_eq_ancestors st id)
val get_items       = get_for_box Box.get_items
val get_inits       = get_for_box Box.get_inits
val get_init_vars   = get_for_box Box.get_init_vars
val get_init_assums = get_for_box Box.get_init_assums
val get_handlers    = get_for_box Box.get_handlers
val get_all_items       = get_all_for_box Box.get_items
val get_all_inits       = get_all_for_box Box.get_inits
val get_all_init_vars   = get_all_for_box Box.get_init_vars
val get_all_init_assums = get_all_for_box Box.get_init_assums
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

fun set_resolve_th id th st = st |> map_box id (Box.set_resolve_th th)
fun get_resolve_th st id = Box.get_resolve_th (get_box st id)

fun is_term_present st t =
    let
      val items = maps (get_items st) (get_unresolved st)
    in
      exists (is_subterm t) (map #tname items)
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
      RewriteTable.is_equiv id tbl (HOLogic.dest_prod (get_tname_raw ritem))
    else false

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
      if length handlers' = 0 then th
      else let
        val to_invoke =
            find_index (fn (_, (t, (ready, _))) => ready (t, all_hyps))
                       handlers'
      in
        if to_invoke = ~1 then
          if forall (fn (req, _) => not req) handlers' then th
          else raise AUTO2 "invoke_handlers: cannot find invokable handler."
        else
          th |> invoke_handler (snd (nth handlers' to_invoke))
             |> invoke_handlers handlers
      end
    end

(* Derive the consequence if box id is resolved, to the parent id
   formed by getting parent at index i.
 *)
fun get_on_resolve (st as {lat, ctxt, ...}) id i th =
    let
      val parent = BoxID.get_parent_at_i lat id i
      val prim_id = nth id i

      (* First get list of handlers to invoke. *)
      val retro_ids = (get_unresolved st)
                          |> filter (is_eq_ancestor st [prim_id])
                          |> filter (is_eq_descendent st id)
      val handlers = map (pair true) (maps (get_handlers st) retro_ids) @
                     map (pair false) (get_handlers st parent)
      val th' = invoke_handlers handlers th
      val inits = (get_inits st [prim_id])
                      |> (if prim_id = 0 then
                            filter (fn init => case init of
                                                   Update.InitAssum _ => true
                                                 | _ => false)
                          else I)
      val th'' = Update.get_neg_form_thm ctxt inits th'
      val _ = if prim_id = 0 then
                assert (length (Thm.hyps_of th'') = 0)
                       "get_on_resolve: did not remove all hypothesis at box 0."
              else ()
      val _ = assert (Thm.prop_of th'' aconv Update.get_neg_form ctxt inits)
                     "get_on_resolve: wrong value from get_neg_form_thm."
    in
      Update.thm_to_ritem th''
    end

(* Find a primitive box (if there is any) whose initial facts agree
   exactly with the given initial facts. Note we cannot yet handle new
   variables.
 *)
fun find_prim_box (st as {tbl, ...}) id inits =
    let
      val vars = maps Update.dest_init_var inits
      val assums = maps Update.dest_init_assum inits
      fun agree_at_id id' =
          let
            val parent = get_parent_prim st (the_single id')
            val is_equiv = RewriteTable.is_equiv parent tbl
          in
            eq_set is_equiv (vars, get_init_vars st id') andalso
            eq_set is_equiv (assums, get_init_assums st id')
          end

      fun can_test_id id' =
          case id' of
              [prim_id'] => is_eq_ancestor st (get_parent_prim st prim_id') id
            | _ => false

      val ids_to_test = get_all_ids st |> filter can_test_id
    in
      find_first agree_at_id ids_to_test
    end

fun map_queue f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = boxes, queue = f queue, tbl = tbl,
     ctxt = ctxt}

fun add_to_queue updt = map_queue (Updates_Heap.insert updt)
val delmin_from_queue = map_queue Updates_Heap.delete_min

end  (* structure Status *)

type status = Status.status
