(* Definitions and basic operations on the main data structures, up to
   Status, which represents the state of the proof.
 *)

val TY_NULL = "NULL"
val TY_EQ = "EQ"
val TY_VAR = "VAR"
val TY_PROP = "PROP"
val TY_TERM = "TERM"
val TY_PROPERTY = "PROPERTY"

type retro_handler = (term * term list -> bool) * (term * thm -> thm)
datatype raw_item = Handler of term * retro_handler
                  | Fact of string * term list * thm
type box_item = {uid: int, id: box_id, sc: int, ty_str: string,
                 tname: cterm list, prop: thm}

signature BOXITEM =
sig
  (* Facts. *)
  val var_to_fact: term -> raw_item
  val term_to_fact: term -> raw_item
  val is_fact_raw: raw_item -> bool
  val match_ty_str_raw: string -> raw_item -> bool
  val match_ty_strs_raw: string list -> raw_item -> bool
  val get_tname_raw: raw_item -> term list
  val get_thm_raw: raw_item -> thm
  (* Handlers. *)
  val is_handler_raw: raw_item -> bool
  val dest_handler_raw: raw_item -> term * retro_handler
  (* Misc. functions. *)
  val eq_ritem: raw_item * raw_item -> bool
  val instantiate: (cterm * cterm) list -> raw_item -> raw_item
  val obtain_variant_frees:
      Proof.context * raw_item list -> Proof.context * (cterm * cterm) list

  val null_item: box_item
  val match_ty_str: string -> box_item -> bool
  val match_ty_strs: string list -> box_item -> bool
  (* Misc. functions. *)
  val merged_id: box_lattice -> box_item list -> box_id
  val mk_box_item: Proof.context -> int * box_id * int * raw_item -> box_item
end;

functor BoxItem(Base:UTIL_BASE) : BOXITEM =
struct

structure UtilLogic = UtilLogic(Base)
open Base
open UtilLogic

fun var_to_fact t = Fact (TY_VAR, [t], true_th)
fun term_to_fact t = Fact (TY_TERM, [t], true_th)

fun is_fact_raw ritem =
    case ritem of Fact _ => true | _ => false
fun match_ty_str_raw s ritem =
    case ritem of Fact (ty_str, _, _) => s = "" orelse ty_str = s | _ => false
fun match_ty_strs_raw slist ritem =
    case ritem of Fact (ty_str, _, _) => member (op =) slist ty_str | _ => false
fun get_tname_raw ritem =
    case ritem of Fact (_, ts, _) => ts | _ => raise Fail "get_tname_raw"
fun get_thm_raw ritem =
    case ritem of Fact (_, _, th) => th | _ => raise Fail "get_thm_raw"

fun is_handler_raw ritem =
    case ritem of Handler _ => true | _ => false
fun dest_handler_raw ritem =
    case ritem of Handler (t, handler) => (t, handler)
                | _ => raise Fail "dest_handler_raw: wrong type"

fun eq_ritem (ritem1, ritem2) =
    case ritem1 of
        Fact (ty1, ts1, th1) =>
        (case ritem2 of
             Fact (ty2, ts2, th2) =>
             ty1 = ty2 andalso eq_list (op aconv) (ts1, ts2) andalso
             Thm.eq_thm_prop (th1, th2)
           | _ => false)
      | Handler (t1, handler1) =>
        (case ritem2 of
             Fact _ => false
           | Handler (t2, handler2) =>
             t1 aconv t2 andalso pointer_eq (handler1, handler2))

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
          ritems |> filter (match_ty_str_raw TY_VAR) |> maps get_tname_raw
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
          Fact (ty_str, map subst_fun tname, subst_thm_atomic subst th)
    end

val null_item = {uid = 0, id = [], sc = 0, ty_str = TY_NULL,
                 tname = [], prop = true_th}
fun match_ty_str s {ty_str, ...} = (s = "" orelse s = ty_str)
fun match_ty_strs slist {ty_str, ...} = member (op =) slist ty_str

fun merged_id lat items =
    case items of
        [] => []
      | {id, ...} :: items' => BoxID.merge_boxes lat (id, merged_id lat items')

fun mk_box_item ctxt (uid, id, sc, ritem) =
    case ritem of
        Handler _ => raise Fail "mk_box_item: ritem must be Fact"
      | Fact (ty_str, ts, prop) =>
        {uid = uid, id = id, sc = sc, ty_str = ty_str,
         tname = map (cert ctxt) ts, prop = prop}

end  (* structure BoxItem. *)

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
type item_output = Proof.context -> term list * thm -> string

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
  term_fn: (term list -> term list) option, output_fn: item_output option}

fun add_prop_matcher_to_info
        mtch {prop_matchers, typed_matchers, term_fn, output_fn} =
    {prop_matchers = mtch :: prop_matchers, typed_matchers = typed_matchers,
     term_fn = term_fn, output_fn = output_fn}

fun add_typed_matcher_to_info
        mtch {prop_matchers, typed_matchers, term_fn, output_fn} =
    {prop_matchers = prop_matchers, typed_matchers = mtch :: typed_matchers,
     term_fn = term_fn, output_fn = output_fn}

fun join_infos (
  {prop_matchers = pm1, typed_matchers = tm1, term_fn = tf1, output_fn = of1},
  {prop_matchers = pm2, typed_matchers = tm2, term_fn = tf2, output_fn = of2}) =
    {prop_matchers = merge pointer_eq (pm1, pm2),
     typed_matchers = merge pointer_eq (tm1, tm2),
     term_fn = (if pointer_eq (tf1, tf2) then tf1
                else raise Fail "join_infos: term_fn non-equal"),
     output_fn = (if pointer_eq (of1, of2) then of1
                  else raise Fail "join_infos: output_fn non-equal")}

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
                   | WellFormMatch of term * term

signature ITEM_IO =
sig
  val pat_of_match_arg: match_arg -> term
  val subst_arg: Type.tyenv * Envir.tenv -> match_arg -> match_arg
  val assert_valid_arg: match_arg -> unit
  val check_ty_str: string -> match_arg -> bool
  val is_ordinary_match: match_arg -> bool
  val is_side_match: match_arg -> bool

  val add_item_type: string * (term list -> term list) option *
                     item_output option -> theory -> theory
  val add_prop_matcher: string * item_matcher -> theory -> theory
  val add_typed_matcher: string * item_matcher -> theory -> theory
  val get_io_info: theory -> string -> item_io_info
  val get_prop_matchers: theory -> string -> item_matcher list
  val get_typed_matchers: theory -> string -> item_matcher list
  val univ_matcher: item_matcher
  val prop_matcher: item_matcher
  val term_prop_matcher: item_matcher
  val null_eq_matcher: item_matcher
  val term_typed_matcher: item_matcher
  val eq_tname_typed_matcher: item_matcher
  val null_property_matcher: item_matcher
  val term_property_matcher: item_matcher
  val pre_match_arg: rewrite_table -> match_arg -> box_item -> bool
  val match_arg: rewrite_table -> match_arg -> box_item -> id_inst ->
                 id_inst_th list
  val no_rewr_terms: term list -> term list
  val rewr_terms_of_item: Proof.context -> string * term list -> term list
  val output_prop_fn: item_output
  val string_of_item_info: Proof.context -> string * term list * thm -> string
  val add_basic_item_io: theory -> theory
  val string_of_raw_item: Proof.context -> raw_item -> string
  val string_of_item: Proof.context -> box_item -> string
  val trace_ritem: Proof.context -> string -> raw_item -> unit
  val trace_item: Proof.context -> string -> box_item -> unit
  val trace_ritems: Proof.context -> string -> raw_item list -> unit
  val trace_items: Proof.context -> string -> box_item list -> unit
end;

functor ItemIO(Base:UTIL_BASE) : ITEM_IO =
struct

structure UtilLogic = UtilLogic(Base)
structure Property = Property(Base)
structure RewriteTable = RewriteTable(Base)
structure Matcher = Matcher(Base)
open Base
open UtilLogic

fun pat_of_match_arg arg =
    case arg of
        PropMatch pat => pat
      | TypedMatch (_, pat) => pat
      | PropertyMatch pat => pat
      | WellFormMatch (_, req) => req

fun subst_arg inst arg =
    case arg of
        PropMatch pat => PropMatch (subst_term_norm inst pat)
      | TypedMatch (ty_str, pat) =>
        TypedMatch (ty_str, subst_term_norm inst pat)
      | PropertyMatch pat =>
        PropertyMatch (subst_term_norm inst pat)
      | WellFormMatch (t, req) =>
        WellFormMatch (subst_term_norm inst t, subst_term_norm inst req)

fun assert_valid_arg arg =
    case arg of
        PropMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropMatch should be bool."
      | TypedMatch _ => ()
      | PropertyMatch pat =>
        assert (fastype_of pat = boolT)
               "assert_valid_arg: arg for PropertyMatch should be bool."
      | WellFormMatch (_, req) =>
        assert (fastype_of req = boolT)
               "assert_valid_arg: arg for WellFormMatch should be bool."

fun check_ty_str ty_str arg =
    case arg of
        TypedMatch (ty_str', _) => ty_str = ty_str'
      | _ => true

fun is_ordinary_match arg =
    case arg of PropMatch _ => true
              | TypedMatch _ => true
              | _ => false

fun is_side_match arg =
    case arg of PropertyMatch _ => true
              | WellFormMatch _ => true
              | _ => false

fun add_item_type (ty_str, term_fn, output_fn) = ItemIOData.map (
      Symtab.update_new (ty_str, {prop_matchers = [], typed_matchers = [],
                                  term_fn = term_fn, output_fn = output_fn}))

fun add_prop_matcher (ty_str, it_match) = ItemIOData.map (
      Symtab.map_entry ty_str (add_prop_matcher_to_info it_match))

fun add_typed_matcher (ty_str, it_match) = ItemIOData.map (
      Symtab.map_entry ty_str (add_typed_matcher_to_info it_match))

fun get_io_info thy ty_str =
    the (Symtab.lookup (ItemIOData.get thy) ty_str)
    handle Option.Option => raise Fail ("get_io_info: not found " ^ ty_str)

fun get_prop_matchers thy ty_str = #prop_matchers (get_io_info thy ty_str)
fun get_typed_matchers thy ty_str = #typed_matchers (get_io_info thy ty_str)

val univ_matcher =
    {pre_match = fn _ => fn _ => fn _ => true,
     match = fn _ => fn _ => fn _ => fn (id, inst) => [((id, inst), true_th)]}

(* Prop-matching with a PROP item. *)
val prop_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          let
            val ct = the_single tname
            val t = Thm.term_of ct
          in
            if is_neg pat then
              is_neg t andalso
              Matcher.pre_match_head tbl (get_neg pat, get_cneg ct)
            else
              Term.is_Var pat orelse
              (not (is_neg t) andalso Matcher.pre_match_head tbl (pat, ct))
          end

      fun match pat {tname, prop, ...} tbl (id, inst) =
          let
            val ct = the_single tname
            val t = Thm.term_of ct
          in
            if is_neg pat andalso is_neg t then
              let
                val insts' = Matcher.rewrite_match_head
                                 tbl (get_neg pat, get_cneg ct) (id, inst)
                fun process_inst (inst, eq_th) =
                    let
                      (* This version certainly will not cancel ~~ on
                       two sides.
                       *)
                      val make_neg_eq' = Thm.combination (Thm.reflexive cNot)
                    in
                      (inst, Thm.equal_elim (
                         make_trueprop_eq (make_neg_eq' (meta_sym eq_th))) prop)
                    end
              in
                map process_inst insts'
              end
            else if not (is_neg pat) andalso
                    (Term.is_Var pat orelse not (is_neg t)) then
              let
                val insts' = Matcher.rewrite_match_head tbl (pat, ct) (id, inst)
                fun process_inst (inst, eq_th) =
                    (inst, Thm.equal_elim (
                       make_trueprop_eq (meta_sym eq_th)) prop)
              in
                map process_inst insts'
              end
            else []
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Prop-matching with a TERM item (used to justify equalities). *)
val term_prop_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          if not (has_vars pat) then false
          else if is_eq_term pat then
            Matcher.pre_match tbl (fst (dest_eq pat), the_single tname)
          else false

      fun match pat {tname, ...} tbl (id, inst) =
          if not (is_eq_term pat) then [] else
          if not (has_vars pat) then [] else
          let
            val (lhs, rhs) = dest_eq pat
            val cu = the_single tname
            val pairs = if Term.is_Var lhs then
                          [(false, (lhs, cu)), (true, (rhs, cu))]
                        else [(true, (lhs, cu)), (false, (rhs, cu))]
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

val null_eq_matcher =
    let
      fun pre_match pat _ _ = is_eq_term pat

      fun match pat _ tbl (id, inst) =
          if not (is_eq_term pat) then [] else
          if has_vars pat then [] else
          let
            val (lhs, rhs) = dest_eq pat
            val infos = RewriteTable.equiv_info_t tbl id (lhs, rhs)
            fun process_info (id', th) =
                ((id', inst), to_obj_eq th)
          in
            map process_info infos
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Typed matching with a TERM item. *)
val term_typed_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          Matcher.pre_match_head tbl (pat, the_single tname)

      (* Return value is (inst, eq), where eq is pat(inst) == tname. *)
      fun match pat {tname, ...} tbl (id, inst) =
          Matcher.rewrite_match_head tbl (pat, the_single tname) (id, inst)
    in
      {pre_match = pre_match, match = match}
    end

(* Typed matching for items representing an equality ?A = ?B, where
   the tname is the pair (?A, ?B). Pattern is expected to be of the
   form ?A = ?B.
 *)
val eq_tname_typed_matcher =
    let
      fun pre_match pat {tname, ...} {ctxt, ...} =
          let
            val (lhs, rhs) = the_pair (map Thm.term_of tname)
            val _ = pattern_fo_match ctxt (pat, mk_eq (lhs, rhs))
          in
            true
          end
          handle Pattern.MATCH => false

      fun match pat {tname, ...} tbl (id, inst) =
          let
            val thy = RewriteTable.theory_of tbl
            val (lhs, rhs) = the_pair (map Thm.term_of tname)
            val inst' =
                Pattern.first_order_match thy (pat, mk_eq (lhs, rhs)) inst
          in
            [((id, inst'), true_th)]
          end
          handle Pattern.MATCH => []
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table. *)
val null_property_matcher =
    let
      fun pre_match pat _ tbl =
          Property.is_property_const (RewriteTable.theory_of tbl) pat

      fun match pat _ tbl (id, inst) =
          let
            val thy = RewriteTable.theory_of tbl
          in
            if has_vars pat then []
            else if not (Property.is_property_const thy pat) then []
            else
              map (fn (id', th) => ((id', inst), th))
                  (RewriteTable.get_property_t tbl (id, pat))
          end
    in
      {pre_match = pre_match, match = match}
    end

(* Obtain a proposition from the property table, matching the argument
   of the property with the given term.
 *)
val term_property_matcher =
    let
      fun pre_match pat {tname, ...} tbl =
          let
            val thy = RewriteTable.theory_of tbl
          in
            Property.is_property_const thy pat andalso
            Matcher.pre_match_head tbl (
              Property.get_property_arg pat, the_single tname)
          end

      fun match pat {tname, ...} tbl (id, inst) =
          if not (has_vars pat) then [] else
          if not (Property.is_property_const
                      (RewriteTable.theory_of tbl) pat) then []
          else let
            val arg = Property.get_property_arg pat
          in
            let
              val insts' = Matcher.rewrite_match_head
                               tbl (arg, the_single tname) (id, inst)
              fun process_inst ((id', inst'), _) =
                  let
                    val t = subst_term_norm inst' pat
                  in
                    map (fn (id'', th) => ((id'', inst'), th))
                        (RewriteTable.get_property_t tbl (id', t))
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
          (PropMatch _, _) =>
          if Term.is_Var pat orelse
             (is_neg pat andalso Term.is_Var (get_neg pat))
          then true
          else exists (fn f => f pat item tbl) (map #pre_match prop_matchers)
        | (TypedMatch _, _) =>
          exists (fn f => f pat item tbl) (map #pre_match typed_matchers)
        | (PropertyMatch _, _) =>
          raise Fail "pre_match_arg: should not be called on PropertyMatch."
        | (WellFormMatch _, _) =>
          raise Fail "pre_match_arg: should not be called on WellFormMatch."
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
          raise Fail "match_arg: should not be called on PropertyMatch."
        | WellFormMatch _ =>
          raise Fail "match_arg: should not be called on WellFormMatch."
    end

val no_rewr_terms = K []

fun arg_rewr_terms ts = maps dest_args ts

fun prop_rewr_terms ts =
    let
      val t = the_single ts
    in
      if is_neg t then t |> dest_arg |> dest_args
      else t |> dest_args
    end

fun rewr_terms_of_item ctxt (ty_str, tname) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {term_fn, ...} = get_io_info thy ty_str
    in
      case term_fn of
          NONE => tname
        | SOME f => f tname
    end

fun output_prop_fn ctxt (_, th) = Thm.prop_of th |> pretty_term ctxt |> str

fun string_of_item_info ctxt (ty_str, ts, th) =
    let
      val thy = Proof_Context.theory_of ctxt
      val {output_fn, ...} = get_io_info thy ty_str
    in
      case output_fn of
          NONE => ty_str ^ " " ^ (ts |> pretty_terms ctxt |> str)
        | SOME f => f ctxt (ts, th)
    end

fun string_of_raw_item ctxt ritem =
    case ritem of
        Handler (t, _) => "Handler " ^ (t |> pretty_term ctxt |> str)
      | Fact info => string_of_item_info ctxt info

fun string_of_item ctxt {ty_str, tname, prop, ...} =
    string_of_item_info ctxt (ty_str, map Thm.term_of tname, prop)

fun trace_ritem ctxt s ritem =
    tracing (s ^ " " ^ (string_of_raw_item ctxt ritem))

fun trace_ritems ctxt s ritems =
    tracing (s ^ "\n" ^ (cat_lines (map (string_of_raw_item ctxt) ritems)))

fun trace_item ctxt s item =
    tracing (s ^ " " ^ (string_of_item ctxt item))

fun trace_items ctxt s items =
    tracing (s ^ "\n" ^ (cat_lines (map (string_of_item ctxt) items)))

val add_basic_item_io =
    fold add_item_type [
      (TY_NULL, NONE, NONE),
      (TY_PROP, SOME prop_rewr_terms, SOME output_prop_fn),
      (TY_TERM, SOME no_rewr_terms, NONE), (TY_EQ, NONE, SOME output_prop_fn),
      (TY_VAR, NONE, NONE), (TY_PROPERTY, SOME arg_rewr_terms, NONE)

    ] #> fold add_prop_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_prop_matcher),
      (TY_NULL, null_eq_matcher), (TY_NULL, null_property_matcher),
      (TY_TERM, term_property_matcher)

    ] #> fold add_typed_matcher [
      (TY_PROP, prop_matcher), (TY_TERM, term_typed_matcher),
      (TY_VAR, term_typed_matcher), (TY_EQ, eq_tname_typed_matcher)
    ]

end  (* structure ItemIO. *)

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
  val apply_exists_ritems: thm -> Proof.context -> string list ->
                           raw_item list * thm
  val apply_exists: box_id * thm -> Proof.context -> string list ->
                    raw_update list
  val get_apply_exists_nms: thm -> string list
  val update_info: Proof.context -> box_id -> raw_item list -> string
  val source_info: update -> string
end;

functor Update(Base:UTIL_BASE) : UPDATE =
struct

structure UtilLogic = UtilLogic(Base)
structure BoxItem = BoxItem(Base)
structure ItemIO = ItemIO(Base)
open Base
open UtilLogic

fun dest_init_var init = case init of InitVar t => [t] | _ => []
fun dest_init_assum init = case init of InitAssum t => [t] | _ => []
fun is_init_assum init = case init of InitAssum _ => true | _ => false
fun build_init_infos (vars, assums) = map InitVar vars @ map InitAssum assums
fun string_of_init_info ctxt init =
    case init of
        InitVar t => ("Var " ^ (t |> pretty_term ctxt |> str))
      | InitAssum assum => ("Assum " ^ (assum |> pretty_term ctxt |> str))

(* Given list of initial variables and assumptions, return the
   contradiction derived from them. Each initial variable becomes !!,
   the last assumption is negated, and each assumption before the last
   becomes ==>.
 *)
fun get_neg_form inits =
    if length inits = 0 then pFalse
    else let
      fun mk_all (nm, T) t = Logic.all_const T $ Term.absfree (nm, T) t
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
    inits |> get_neg_form |> cert ctxt
          |> to_obj_conv ctxt |> rhs_of

(* Given a contradiction th, returns a new theorem with assumptions
   pulled into the proposition of th. The resulting form of th is the
   same as that returned by get_neg_form.
 *)
fun get_neg_form_thm ctxt inits th =
    if length inits = 0 then th
    else let
      val _ = assert (Thm.prop_of th aconv pFalse)
                     "get_neg_form_thm: input th should be a contradiction."
      val tl_assum =
          inits |> List.last |> dest_init_assum |> the_single
          handle List.Empty =>
                 raise Fail "get_neg_form_thm: last init should be prop."

      fun fold_init init th =
          case init of
              InitVar v => Thm.forall_intr (cert ctxt v) th
            | InitAssum assum => th |> Thm.implies_intr (cert ctxt assum)
    in
      th |> Thm.implies_intr (cert ctxt tl_assum)
         |> rewrite_thm_from_contra_form
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
        "Add items " ^ (string_of_list (
                           ItemIO.string_of_raw_item ctxt) raw_items) ^
        " to box " ^ (string_of_box_id id)
      | AddBoxes {id, inits, ...} =>
        "Add box " ^ (string_of_list (string_of_init_info ctxt) inits) ^
        " under box " ^ (string_of_box_id id)
      | ResolveBox {id, ...} =>
        "Resolve box " ^ (string_of_box_id id)
      | ShadowItem {id, item} =>
        "Shadow item " ^ (ItemIO.string_of_item ctxt item) ^
        " in box " ^ (string_of_box_id id)

fun thm_to_ritem th =
    let
      val prop = Thm.prop_of th
      val _ = assert (is_Trueprop prop) "thm_update: prop is not Trueprop."
      val _ = assert (not (has_vars prop))
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
      [Handler (t, handler), thm_to_ritem (assume_thm ctxt t)]
    end

(* nms specify the names of free variables, either internal (use
   obtain_variant_frees to fix) or otherwise (will be put into context
   as is). This function returns the list of VAR items and handlers,
   paired with the theorem produced.
 *)
fun apply_exists_ritems ex_th ctxt nms =
    let
      fun dest_one_abs nm t =
          case t of
              Const (c, _) $ Abs (_, T, body) =>
              if c = Ex_name then
                let
                  val (nm', body') = Term.dest_abs (nm, T, body)
                  val _ = assert (nm = nm') "apply_exists: name clash"
                in
                  ((nm, T), body')
                end
              else raise Fail "apply_exists: not exists statement."
            | _ => raise Fail "apply_exists: not exists statement."

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
      val new_prop' = mk_Trueprop new_prop
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
                       raise Fail "get_freevars: cannot match new_prop' and t"
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
               |> Thm.elim_implies (subst_thm_atomic subst ex_th')
          end

      val ritems = (map (BoxItem.var_to_fact o Free) vars) @
                   [Handler (new_prop', (ready, handler))]
    in
      (ritems, new_th)
    end

(* Calls the previous function, and directly produces the update. *)
fun apply_exists (id, ex_th) ctxt nms =
    let
      val (ritems, new_th) = apply_exists_ritems ex_th ctxt nms
    in
      [AddItems {id = id, sc = NONE,
                 raw_items = ritems @ [thm_to_ritem new_th]}]
    end

(* Given existence theorem, return list of suggested names of new
   variables, obtained from name hints of EX quantifiers.
 *)
fun get_apply_exists_nms th =
    let
      fun helper t =
          case t of
              Const (c, _) $ Abs (abs as (nm, _, _)) =>
              if c = Ex_name then
                let val (_, body) = Term.dest_abs abs in
                  nm :: helper body
                end
              else []
            | _ => []
    in
      (Name.variant_list [] (helper (prop_of' th)))
          |> map Name.internal
    end

fun update_info ctxt id ritems =
    (string_of_list' (ItemIO.string_of_raw_item ctxt)
                     (filter (not o BoxItem.is_handler_raw) ritems)) ^
    " at box " ^ (string_of_box_id id)

fun uid_string_of_item {uid, ...} = "(" ^ string_of_int uid ^ ")"

fun source_info {prfstep_name, source, ...} =
    prfstep_name ^ " on " ^ (string_of_list' (uid_string_of_item) source)

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

functor Box(Base:UTIL_BASE) : BOX =
struct

structure BoxItem = BoxItem(Base)
structure Update = Update(Base)

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
    Update.get_neg_form inits |> pretty_term ctxt |> str

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
  lat: BoxID.box_lattice,
  boxes: box Boxidtab.table,
  queue: Updates_Heap.T,
  tbl: rewrite_table,
  ctxt: Proof.context
}

signature STATUS =
sig
  val empty_status: Proof.context -> status
  val theory_of: status -> theory
  val exist_box: status -> box_id -> bool
  val get_box: status -> box_id -> box

  val get_lattice: status -> BoxID.box_lattice
  val get_parent_prim: status -> int -> box_id
  val merge_boxes: status -> box_id * box_id -> box_id
  val is_ancestor: status -> box_id -> box_id -> bool
  val is_descendent: status -> box_id -> box_id -> bool
  val is_eq_ancestor: status -> box_id -> box_id -> bool
  val is_eq_descendent: status -> box_id -> box_id -> bool
  val is_box_resolved: status -> box_id -> bool
  val is_box_unresolved: status -> box_id -> bool

  val incr_uid: int -> status -> status
  val map_box: box_id -> (box -> box) -> status -> status
  val map_context: (Proof.context -> Proof.context) -> status -> status
  val map_rewrites: (rewrite_table -> rewrite_table) -> status -> status
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

functor Status(Base:UTIL_BASE) : STATUS =
struct

structure UtilLogic = UtilLogic(Base)
structure RewriteTable = RewriteTable(Base)
structure BoxItem = BoxItem(Base)
structure Box = Box(Base)
structure Update = Update(Base)
open Base
open UtilLogic

fun empty_status ctxt =
    {uid_next = 1, lat = BoxID.empty, boxes = Boxidtab.empty,
     queue = Updates_Heap.empty, tbl = RewriteTable.empty ctxt, ctxt = ctxt}

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

fun exist_box {boxes, ...} id = Boxidtab.defined boxes id
fun get_box {boxes, ...} id =
    the (Boxidtab.lookup boxes id)
    handle Option.Option => raise Fail "get_box: id not found."

fun get_lattice {lat, ...} = lat
val get_parent_prim = BoxID.get_parent_prim o get_lattice
val merge_boxes = BoxID.merge_boxes o get_lattice
val is_ancestor = BoxID.is_ancestor o get_lattice
val is_descendent = BoxID.is_descendent o get_lattice
val is_eq_ancestor = BoxID.is_eq_ancestor o get_lattice
val is_eq_descendent = BoxID.is_eq_descendent o get_lattice
val is_box_resolved = BoxID.is_box_resolved o get_lattice
val is_box_unresolved = BoxID.is_box_unresolved o get_lattice

fun incr_uid n {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next + n, lat = lat, boxes = boxes, queue = queue,
     tbl = tbl, ctxt = ctxt}

fun map_box id f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = Boxidtab.map_entry id f boxes,
     queue = queue, tbl = tbl, ctxt = ctxt}

fun map_context f {uid_next, lat, boxes, queue, tbl, ctxt} =
    {uid_next = uid_next, lat = lat, boxes = boxes, queue = queue,
     tbl = tbl |> RewriteTable.map_context f, ctxt = f ctxt}

fun map_rewrites f {uid_next, lat, boxes, queue, tbl, ctxt = _} =
    let
      val (tbl' as {ctxt = ctxt', ...}) = f tbl
    in
      {uid_next = uid_next, lat = lat, boxes = boxes, queue = queue, tbl = tbl',
       ctxt = ctxt'}
    end

fun add_prim_box parent_id new_box {uid_next, lat, boxes, queue, tbl, ctxt} =
    let
      val (id, lat') = BoxID.add_prim_id parent_id lat
    in
      (id, {uid_next = uid_next, lat = lat',
            boxes = Boxidtab.update_new ([id], new_box) boxes, queue = queue,
            tbl = RewriteTable.map_lat (K lat') tbl, ctxt = ctxt})
    end

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
      raise Fail "Try to add a composite box that already exists"
    else if length id = 1 then
      raise Fail "Try to add a primitive box as a composite"
    else
      {uid_next = uid_next, lat = lat,
       boxes = Boxidtab.update_new (id, Box.init_box []) boxes,
       queue = queue, tbl = tbl, ctxt = ctxt}

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

fun add_shadowed (shadow_id, {uid, id, ...}) (st as {lat, ...}) =
    case lookup_item st id uid of
        NONE => raise Fail "add_shadowed: item not found."
      | SOME (item, shadow_ids) =>
        let
          val shadow_ids' = (shadow_id :: shadow_ids)
                                |> max_partial (BoxID.is_eq_ancestor lat)
        in
          map_box id (
            Box.map_items (Inttab.update (uid, (item, shadow_ids')))) st
        end

fun query_shadowed st shadow_id {uid, id, ...} =
    case lookup_item st id uid of
        NONE => raise Fail "query_shadowed: item not found."
      | SOME (_, shadow_ids) =>
        exists (is_eq_descendent st shadow_id) shadow_ids

fun query_removed st (item as {id, ...}) = query_shadowed st id item

fun set_resolve_th id th st = st |> map_box id (Box.set_resolve_th th)
fun get_resolve_th st id = Box.get_resolve_th (get_box st id)

(* Try to find fact at id or above with the proposition t. Return SOME
   th if found.
 *)
fun find_fact (st as {tbl, ctxt, ...}) id t =
    let
      val infos = (get_all_items false st id)
                      |> map (fn {id, prop, ...} => (id, prop))
      val res = (RewriteTable.rewrite_find_fact tbl infos (id, cert ctxt t))
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
fun find_ritem_exact (st as {tbl, ...}) id ritem =
    case ritem of
        Handler _ => false
      | Fact (ty_str, tname, _) =>
        if ty_str = TY_EQ then
          let
            val (lhs, rhs) = the_pair (BoxItem.get_tname_raw ritem)
          in
            RewriteTable.is_equiv_t id tbl (lhs, rhs)
          end
        else if ty_str = TY_PROPERTY then
          let
            val {lat, ...} = tbl
            val prop = the_single tname
            val infos =
                (RewriteTable.get_property_t tbl (id, prop))
                    |> filter (fn (id', _) => BoxID.is_eq_ancestor lat id' id)
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
      val {ctxt, ...} = st
      val (var_ritems, ritems') =
          ritems |> filter_split (BoxItem.match_ty_str_raw TY_VAR)
    in
      if length var_ritems = 0 then
        filter_split (find_ritem_exact st id) ritems
      else let
        val vars = maps BoxItem.get_tname_raw var_ritems
        val sch_vars = vars |> map dest_Free
                            |> map (fn (nm, T) => Var ((nm, 0), T))
        val subst = vars ~~ sch_vars
        val items = get_all_items true st id

        fun find_ritem ritem insts =
            case ritem of
                Handler _ => insts
              | Fact (ty_str, tname, _) =>
                if exists has_vars tname then [] else
                let
                  val tname' = map (Term.subst_atomic subst) tname

                  fun process_inst cts inst =
                      [pattern_fo_match_list
                           ctxt (tname' ~~ map Thm.term_of cts) inst]
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
        if length inst = 0 then ([], ritems) else (ritems, [])
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
      if length handlers' = 0 then th
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
      val inits = get_inits st [prim_id]
      val th'' = Update.get_neg_form_thm ctxt inits th'
      val _ = if prim_id = 0 then
                assert (length (Thm.hyps_of th'') = 0)
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
fun find_prim_box (st as {tbl, ...}) id inits =
    let
      val vars = maps Update.dest_init_var inits
      val assums = maps Update.dest_init_assum inits
      fun agree_at_id id' =
          let
            val parent = get_parent_prim st (the_single id')
            val is_equiv_t = RewriteTable.is_equiv_t parent tbl
          in
            eq_set is_equiv_t (vars, get_init_vars st id') andalso
            eq_set is_equiv_t (assums, get_init_assums st id')
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
