(* Rewrite table: keep track of list of equalities, automatically
   using transitivity on equality and the congruence property of
   functions.
 *)

val string_of_box_id = BoxID.string_of_box_id
val string_of_box_ids = string_of_list string_of_box_id

type box_lattice = BoxID.box_lattice

(* Order on equality theorems, by comparing the right side. *)
val simp_ord = Term_Ord.term_ord o (apply2 rhs_of)
val simp_less = Term_Ord.termless o (apply2 rhs_of)

(* Equality on box_id * thm, comparing the right side. *)
fun eq_info ((id, th), (id', th')) =
    (id = id' andalso rhs_of th aconv rhs_of th')

(* Debug functions. *)
fun print_info ctxt (id, th) = "(" ^ (string_of_box_id id) ^ ", " ^
                               (th |> rhs_of |> pretty_term ctxt |> str) ^ ")"
fun print_infos ctxt lst = commas (map (print_info ctxt) lst)
fun print_info' ctxt (id, ths) =
    "(" ^ (string_of_box_id id) ^ ", " ^
    (ths |> map rhs_of |> pretty_terms ctxt |> str) ^ ")"
fun print_infos' ctxt lst = cat_lines (map (print_info' ctxt) lst)

(* Data structure for rewrite table. *)
type rewrite_table = {
  (* Specifies inheritance relations on primitive boxes. *)
  lat: BoxID.box_lattice,
  (* terms[t] is the list of ids at which t is present. *)
  terms: (box_id list) Termtab.table,
  (* equiv[a] is list of (id, th), where th is "a == a'" under id. *)
  equiv: ((box_id * thm) list) Termtab.table,
  (* Index of reachability under equiv. *)
  all_equiv: ((box_id * thm) list) Termtab.table,
  (* Index of head equivs. *)
  head_equiv: ((term * (box_id * thm) list) list) Termtab.table,
  (* contain[A] is the list of terms for which A is a direct subterm. *)
  contain: (term list) Termtab.table,
  (* Rewrite info of a term. *)
  simp: ((box_id * thm) list) Termtab.table,
  (* Subterm rewrite info of a term. *)
  subsimp: ((box_id * thm) list) Termtab.table,
  (* Reverse of subsimp. Head rep of a term. *)
  reps: ((box_id * thm) list) Termtab.table,
  (* Property list of a term. *)
  property: ((box_id * thm) list) Termtab.table,
  (* Current context. *)
  ctxt: Proof.context
}

datatype rewrite_type = SINGLE of rewrite_table
                      | LAST of rewrite_table * box_id

signature REWRITE_TABLE =
sig
  val table_of_rtype: rewrite_type -> rewrite_table
  val single_of_rtype: rewrite_type -> rewrite_type
  val is_single_rtype: rewrite_type -> bool

  (* Internal functions. Do not use except in unit test. *)
  val refl: rewrite_table -> term -> thm
  val add_equiv: box_id * thm -> rewrite_table -> rewrite_table
  val equiv_neighs: rewrite_table -> term -> (box_id * thm) list
  val index_all_equiv: term -> rewrite_table -> rewrite_table
  val get_all_equiv: rewrite_table -> term -> (box_id * thm) list
  val in_table_raw_ids: rewrite_table -> term -> box_id list
  val in_table_raw_for_id: rewrite_table -> box_id * term -> bool
  val in_table_raw: rewrite_table -> term -> bool
  val add_term_raw: box_id * term -> rewrite_table -> rewrite_table
  val update_simp: box_id * thm -> rewrite_table -> rewrite_table
  val get_rewrite_info: rewrite_table -> term -> (box_id * thm) list
  val get_rewrite: box_id -> rewrite_table -> term -> thm
  val get_subterm_rewrite_info: rewrite_table -> term -> (box_id * thm) list
  val remove_rep: box_id * thm -> rewrite_table -> rewrite_table
  val update_subsimp: box_id * thm -> rewrite_table -> rewrite_table
  val get_head_rep_with_id_th:
      rewrite_table -> box_id * thm -> (box_id * thm) list
  val get_property_for_term: rewrite_table -> term -> (box_id * thm) list
  val add_property_raw: box_id * thm -> rewrite_table -> rewrite_table
  val reduce_equivs:
      rewrite_table -> term * (box_id * thm) list -> term * (box_id * thm) list
  val compute_head_equiv:
      rewrite_table -> term -> (term * (box_id * thm) list) list
  val index_head_equiv: term -> rewrite_table -> rewrite_table
  val get_head_equiv: rewrite_table -> term -> (term * (box_id * thm) list) list
  val get_head_equiv_with_t:
      rewrite_table -> box_id * term -> term -> (box_id * thm) list

  (* External *)
  val theory_of: rewrite_table -> theory
  val merge_box_with_info: rewrite_table -> box_id -> (box_id * 'a) list ->
                           (box_id * 'a) list
  val to_string: rewrite_table -> string
  val to_string_full: rewrite_table -> string
  val empty: Proof.context -> rewrite_table
  val map_lat: (box_lattice -> box_lattice) -> rewrite_table -> rewrite_table
  val map_context: (Proof.context -> Proof.context) -> rewrite_table ->
                   rewrite_table
  val get_all_terms: rewrite_table -> term list
  val get_all_id_terms: rewrite_table -> (box_id * term) list
  val reduce_simp_info:
      rewrite_table -> (box_id * thm) list -> (box_id * thm) list
  val merge_simp_infos: rewrite_table -> (box_id * thm) list list ->
                        (box_id * thm list) list
  val head_simplify: box_id -> rewrite_table -> term -> thm
  val simplify: box_id -> rewrite_table -> term -> thm
  val simp_val: box_id -> rewrite_table -> term -> term
  val subterm_simplify: box_id -> rewrite_table -> term -> thm
  val simplify_info: rewrite_table -> term -> (box_id * thm) list
  val subterm_simplify_info: rewrite_table -> term -> (box_id * thm) list
  val is_equiv: box_id -> rewrite_table -> term * term -> bool
  val is_equiv_th: box_id -> rewrite_table -> term * term -> thm option
  val is_subequiv: box_id -> rewrite_table -> term * term -> bool
  val equiv_info: rewrite_table -> box_id -> term * term -> (box_id * thm) list
  val subequiv_info:
      rewrite_table -> box_id -> term * term -> (box_id * thm) list
  val get_reachable_terms: bool -> rewrite_table -> term list -> term list
  val add_term: box_id * term -> rewrite_table -> rewrite_table
  val add_rewrite: box_id -> thm -> rewrite_table -> rewrite_table
  val add_property: box_id * thm -> rewrite_table -> rewrite_table
  val get_property: rewrite_table -> box_id * term -> (box_id * thm) list

  val append_rewrite: thm -> rewrite_table -> rewrite_table
  val replace_id_for_type:
      rewrite_type -> ((box_id * 'a) * 'b) list -> ((box_id * 'a) * 'b) list
  val replace_id_for_type':
      rewrite_type -> (box_id * 'a) list -> (box_id * 'a) list
  val get_new_terms: rewrite_table * rewrite_table -> (box_id * term) list
  val append_property: thm -> rewrite_table -> rewrite_table
  val get_new_properties: rewrite_type -> (box_id * thm) list
end;

functor RewriteTable(Base:UTIL_BASE) : REWRITE_TABLE =
struct

structure UtilLogic = UtilLogic(Base)
structure ACUtil = ACUtil(Base)
structure Subterms = Subterms(Base)
structure Property_Data = Property_Data(Base)
open Base
open UtilLogic
open Property_Data

fun table_of_rtype rtype =
    case rtype of SINGLE tbl => tbl | LAST (tbl, _) => tbl
fun single_of_rtype rtype =
    case rtype of SINGLE tbl => SINGLE tbl | LAST (tbl, _) => SINGLE tbl
fun is_single_rtype rtype = case rtype of SINGLE _ => true | _ => false

fun theory_of {ctxt, ...} = Proof_Context.theory_of ctxt

(*** Wrapper around most often used functions from box_id. ***)
fun get_lattice {lat, ...} = lat
val merge_boxes = BoxID.merge_boxes o get_lattice
val get_all_merges = BoxID.get_all_merges o get_lattice
val is_eq_ancestor = BoxID.is_eq_ancestor o get_lattice
val is_eq_descendent = BoxID.is_eq_descendent o get_lattice
fun merge_box_with_info tbl id =
    map (apfst (fn id' => merge_boxes tbl (id, id')))
fun merge_info tbl (id, th) (id', th') =
    (merge_boxes tbl (id, id'), transitive_list [th, th'])
val id_is_eq_ancestor = BoxID.id_is_eq_ancestor o get_lattice

(* Print info from one of the tables terms, equiv, simp, subsimp, and
   reps. print_val_fun specifies how to print list of values
   associated to a term.
 *)
fun to_string_table ctxt term_tbl print_val_fun =
    let
      fun print_lst (t, info_t) =
          (t |> pretty_term ctxt |> str) ^ ": " ^ (print_val_fun info_t)
    in
      cat_lines (map print_lst (Termtab.dest term_tbl))
    end

fun to_string {equiv, ctxt, ...} =
    to_string_table ctxt equiv (print_infos ctxt)
fun to_string_full {terms, equiv, simp, subsimp, reps, ctxt, ...} =
    "Terms: " ^ (to_string_table ctxt terms string_of_box_ids) ^
    "\nequiv table:\n" ^ (to_string_table ctxt equiv (print_infos ctxt)) ^
    "\nsimp table:\n" ^ (to_string_table ctxt simp (print_infos ctxt)) ^
    "\nsubsimp table:\n" ^ (to_string_table ctxt subsimp (print_infos ctxt)) ^
    "\nreps table:\n" ^ (to_string_table ctxt reps (print_infos ctxt))

(*** Certify using the current context. ***)
fun refl {ctxt, ...} t = Thm.reflexive (cert ctxt t)

(*** empty and basic modification functions. ***)
fun empty ctxt = {
  lat = BoxID.empty, terms = Termtab.empty, equiv = Termtab.empty,
  all_equiv = Termtab.empty, head_equiv = Termtab.empty,
  contain = Termtab.empty, simp = Termtab.empty, subsimp = Termtab.empty,
  reps = Termtab.empty, property = Termtab.empty, ctxt = ctxt}

fun map_lat f {lat, terms, equiv, all_equiv, head_equiv, contain, simp, subsimp,
               reps, property, ctxt} =
    let
      val lat' = f lat
      fun clean tb id_fun =
          tb |> Termtab.map
             (fn _ => filter (BoxID.is_box_supported lat' o id_fun))

      fun clean_head_equiv_1 (fhead, infos) =
          let
            val infos' = filter (BoxID.is_box_supported lat' o fst) infos
          in
            if length infos' = 0 then [] else [(fhead, infos')]
          end

      fun clean_head_equiv tb =
          tb |> Termtab.map (fn _ => maps clean_head_equiv_1)
    in
      {lat = lat', terms = clean terms I, equiv = clean equiv fst,
       all_equiv = clean all_equiv fst,
       head_equiv = clean_head_equiv head_equiv,
       contain = contain, simp = clean simp fst, subsimp = clean subsimp fst,
       reps = clean reps fst, property = clean property fst, ctxt = ctxt}
    end

fun map_terms f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, property, ctxt} =
    {lat = lat, terms = f terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, ctxt = ctxt}
fun map_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = f equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, ctxt = ctxt}
fun map_all_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                     subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = f all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, ctxt = ctxt}
fun map_head_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                      subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = f head_equiv, contain = contain, simp = simp,
     subsimp = subsimp, reps = reps, property = property, ctxt = ctxt}
fun map_contain f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = f contain, simp = simp,
     subsimp = subsimp, reps = reps, property = property, ctxt = ctxt}
fun map_simp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = f simp,
     subsimp = subsimp, reps = reps, property = property, ctxt = ctxt}
fun map_subsimp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp,
     subsimp = f subsimp, reps = reps, property = property, ctxt = ctxt}
fun map_reps f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = f reps, property = property, ctxt = ctxt}
fun map_property f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                    subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = f property, ctxt = ctxt}
fun map_context f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, ctxt = f ctxt}

(*** Basic manipulation of contain table. ***)

(* Add the information that t contains subt directly. *)
fun add_contain t subt (tbl as {contain, ...}) =
    let
      val contain_subt = the_default [] (Termtab.lookup contain subt)
    in
      if member (op aconv) contain_subt t then tbl
      else tbl |> map_contain (Termtab.update (subt,  t :: contain_subt))
    end

(* Get all terms that directly contains t. *)
fun immediate_contains {contain, ...} t =
    the_default [] (Termtab.lookup contain t)

(*** Basic manipulation of the terms table. ***)

(* Return ids in which t is directly in table. *)
fun in_table_raw_ids {terms, ...} t = the_default [] (Termtab.lookup terms t)

(* Whether the term is present in table at the given id. *)
fun in_table_raw_for_id tbl (id, t) =
    exists (is_eq_descendent tbl id) (in_table_raw_ids tbl t)

(* Whether the term is present at any id. *)
fun in_table_raw tbl t = length (in_table_raw_ids tbl t) > 0

(* Add t to table at the given id. *)
fun add_term_raw (id, t) (tbl as {terms, ...}) =
    let
      val ids_t = (id :: the_default [] (Termtab.lookup terms t))
                      |> max_partial (is_eq_ancestor tbl)
    in
      tbl |> map_terms (Termtab.update (t, ids_t))
    end

(* Return list of all terms (at any ids) present in table. *)
fun get_all_terms {terms, ...} = Termtab.keys terms

(* Return list of all terms with ids present in table. *)
fun get_all_id_terms tbl =
    get_all_terms tbl |> maps (fn t => map (rpair t) (in_table_raw_ids tbl t))

(*** Basic manipulation of equiv table. ***)

(* equiv_eq_better tbl info1 info2 means info2 is extraneous in the
   equiv table.
 *)
fun equiv_eq_better tbl (id, th) (id', th') =
    rhs_of th aconv rhs_of th' andalso is_eq_ancestor tbl id id'
fun has_equiv_eq_better tbl infos info' =
    exists (fn info => equiv_eq_better tbl info info') infos

(* Remove extraneous ids for infos with equal terms. *)
fun reduce_equiv_info tbl info = max_partial (equiv_eq_better tbl) info

(* Add one way equivalence edge. Maintain the non-comparable property
   of the set of equivalence edges between any two nodes. cur_info is
   of form (id, t == t').
 *)
fun add_equiv_raw (cur_info as (_, th)) (tbl as {equiv, ...}) =
    let
      val t = lhs_of th
      val equiv_t = the_default [] (Termtab.lookup equiv t)
    in
      if exists (fn info => equiv_eq_better tbl info cur_info) equiv_t then tbl
      else tbl |> map_equiv (
          Termtab.update (
            t, equiv_t |> filter_out (equiv_eq_better tbl cur_info)
                       |> cons cur_info))
    end

(* Add the given equivalence edge. *)
fun add_equiv (id, th) tbl =
    let
      val _ = assert (not (lhs_of th aconv rhs_of th)) "add_equiv: t == t'"
    in
      tbl |> add_equiv_raw (id, th)
          |> add_equiv_raw (id, meta_sym th)
    end

(* Get all edges coming from t in the equiv graph. *)
fun equiv_neighs {equiv, ...} t =
    case Termtab.lookup equiv t of
        NONE => []
      | SOME infos => infos

(* Assume t is directly in table. Returns list of (id, t == t') pairs,
   where id is the minimum assumption needed for t == t'.
 *)
fun compute_all_equiv tbl t =
    let
      (* Each item in new / all is (id, th). *)
      fun helper (new, all) =
          case new of
              [] => ([], all)
            | (id, th) :: rest =>
              let
                val t' = rhs_of th
                fun process_new (id', th') = merge_info tbl (id, th) (id', th')
                val new' = (equiv_neighs tbl t')
                               |> map process_new
                               |> filter_out (has_equiv_eq_better tbl all)
                val all' = new' @
                           (filter_out (has_equiv_eq_better tbl new') all)
              in
                helper (rest @ new', all')
              end
      val init = ([], refl tbl t)
    in
      snd (helper ([init], [init]))
    end

fun index_all_equiv t tbl =
    tbl |> map_all_equiv (Termtab.update (t, compute_all_equiv tbl t))

fun get_all_equiv {all_equiv, ...} t =
    the (Termtab.lookup all_equiv t)
    handle Option.Option => raise AUTO2 "all_equiv: not found"

(*** Basic manipulation of simp table. ***)

(* simp_eq_better tbl info1 info2 means info2 is extraneous in the
   simp table.
 *)
fun simp_eq_better tbl (id, th) (id', th') =
    if is_eq_ancestor tbl id id' then
      let val (t, t') = (rhs_of th, rhs_of th')
      in t aconv t' orelse Term_Ord.termless (t, t') end
    else false

(* Remove all extraneous rewrite or simplification infos. *)
fun reduce_simp_info tbl info = max_partial (simp_eq_better tbl) info

(* Update rewrite of t under id to th: t == t'. Similar to
   add_equiv_raw.
 *)
fun update_simp (id, th) (tbl as {simp, ...}) =
    let
      val t = lhs_of th
      val simp_t = the_default [([], refl tbl t)] (Termtab.lookup simp t)
    in
      if exists (fn info => simp_eq_better tbl info (id, th)) simp_t then tbl
      else
        tbl |> map_simp (
          Termtab.update (
            t, simp_t |> filter_out (simp_eq_better tbl (id, th))
                      |> cons (id, th)))
    end

(* Get the entire rewrite info of t as stored directly in
   table. Return as a list of (id, th) pairs.
 *)
fun get_rewrite_info (tbl as {simp, ...}) t =
    case Termtab.lookup simp t of
        NONE => [([], refl tbl t)]
      | SOME infos => infos

(* Return the rewrite of t under a given id, as stored directly in
   table. Return t == t if not in table.
 *)
fun get_rewrite id tbl t =
    case get_rewrite_info tbl t of
        [] => refl tbl t
      | ths' => ths' |> filter (is_eq_descendent tbl id o fst)
                     |> map snd
                     |> max (rev_order o simp_ord)

(*** Basic manipulation of subsimp and rep tables. ***)

(* Given list of lists of simplifying infos indexed by term and then
   id, return simplifying infos indexed first by id and then term.
 *)
fun merge_simp_infos tbl lsts =
    let
      val ids = map (map fst) lsts |> get_all_merges tbl
      fun get_for_id_lst id lst =
          lst |> filter (is_eq_descendent tbl id o fst)
              |> map snd |> max (rev_order o simp_ord)
      fun get_for_id id = (id, map (get_for_id_lst id) lsts)
    in
      map get_for_id ids
    end

(* Get entire subterm rewrite info of t. Return as a list of (id,
   rewrite) pairs.
 *)
fun get_subterm_rewrite_info (tbl as {ctxt, ...}) t =
    let
      val (t', subs) = Subterms.dest_subterms t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (get_rewrite_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, Subterms.build_equiv ctxt equivs t'))
          |> reduce_simp_info tbl
    end

(* Given a head rep (id, th) (where th is reverse of a subterm
   rewrite), remove th from the reps table.
 *)
fun remove_rep (id, th) (tbl as {reps, ...}) =
    let
      val t = lhs_of th
      val reps_t = the_default [] (Termtab.lookup reps t)
      val _ = assert (member eq_info reps_t (id, th)) "remove_rep: not found"
    in
      tbl |> map_reps (Termtab.map_entry t (remove eq_info (id, th)))
    end

(* Update subterm rewrite of t under id to th: t == t'. Also update
   the reps table (reverse of subsimp table).
 *)
fun update_subsimp (id, th) (tbl as {subsimp, ...}) =
    let
      val (t, t') = (lhs_of th, rhs_of th)
      val subsimp_t = the_default [] (Termtab.lookup subsimp t)
    in
      if exists (fn info => simp_eq_better tbl info (id, th)) subsimp_t then tbl
      else
        let
          val th' = meta_sym th
          val (rem, keep) = filter_split (simp_eq_better tbl (id, th)) subsimp_t
        in
          tbl |> map_subsimp (Termtab.update (t, (id, th) :: keep))
              |> map_reps (Termtab.map_default (t', []) (cons (id, th')))
              |> fold remove_rep (map (apsnd meta_sym) rem)
        end
    end

(* Returns the list of (id, th) pairs, where th is t == t', such that
   t' subterm rewrites to t at box id.
 *)
fun get_head_rep_info {reps, ...} t =
    case Termtab.lookup reps t of
        NONE => []
      | SOME infos => infos

(* Assume t is subterm simplified under id. Return SOME (t == v) if v
   is a term in the rewrite table that is subterm rewrites to t, under
   the given id. If there is no such v, return NONE.
 *)
fun get_head_rep id tbl t =
    get_first (fn (id', t') =>
                  if is_eq_ancestor tbl id' id then SOME t' else NONE)
              (get_head_rep_info tbl t)

(* Returns head representations of the right side of th under id, or
   under more restrictive assumptions. Merge the equivalence theorems
   with th. Not guaranteed to be non-redundant.
 *)
fun get_head_rep_with_id_th tbl (id, th) =
    get_head_rep_info tbl (rhs_of th) |> map (merge_info tbl (id, th))

(* Using the subsimp table for subterm simplification. *)
fun get_cached_subterm_rewrite_info {subsimp, ...} t =
    case Termtab.lookup subsimp t of
        NONE => []
      | SOME infos => infos

(* Obtain the subterm simplification of t under id, or a less
   restrictive assumption.
 *)
fun get_cached_subterm_rewrite id tbl t =
    case get_cached_subterm_rewrite_info tbl t of
        [] => refl tbl t
      | ths' => ths' |> filter (is_eq_descendent tbl id o fst)
                     |> map snd
                     |> max (rev_order o simp_ord)

(*** Basic manipulation of the property table. ***)

(* property_eq_better info1 info2 means info2 is extraneous in the
   property table. Note we compare theorems exactly, not up to
   rewriting.
 *)
fun property_eq_better tbl (id, th) (id', th') =
    Thm.prop_of th aconv Thm.prop_of th' andalso is_eq_ancestor tbl id id'

(* Retrieve the current list of properties for a term t. *)
fun get_property_for_term {property, ...} t =
    the_default [] (Termtab.lookup property t)

(* Add a new property. Similar to add_equiv_raw. *)
fun add_property_raw (cur_info as (_, th)) tbl =
    let
      val t = get_property_arg (prop_of' th)
      val property_t = get_property_for_term tbl t
    in
      if exists (fn info => property_eq_better tbl info cur_info)
                property_t then tbl
      else
        tbl |> map_property (
          Termtab.update (
            t, property_t |> filter_out (property_eq_better tbl cur_info)
                          |> cons cur_info))
    end

(* Convert property P s to P t using equality s == t. Merge boxes
   corresponding to the two theorems.
 *)
fun convert_property tbl (id', eq_th) (id, th) =
    (merge_boxes tbl (id, id'),
     th |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv eq_th)))

(*** Simplification of terms not indexed in table. ***)

(* Assume t is subterm simplified under id. *)
fun head_simplify id tbl t =
    case get_head_rep id tbl t of
        NONE => refl tbl t
      | SOME th => transitive_list [th, get_rewrite id tbl (rhs_of th)]

(* First simplify subterms, then simplify head. *)
fun simplify id tbl t =
    if in_table_raw tbl t then get_rewrite id tbl t else
    let val th = subterm_simplify id tbl t
    in transitive_list [th, head_simplify id tbl (rhs_of th)] end

(* Simplify subterms, but not head. *)
and subterm_simplify id (tbl as {ctxt, ...}) t =
    if in_table_raw tbl t then get_cached_subterm_rewrite id tbl t else
    let
      val (t', subs) = Subterms.dest_subterms t
      val equivs = map (simplify id tbl) subs
    in
      Subterms.build_equiv ctxt equivs t'
    end

(* Convenient function for getting simplified value. *)
fun simp_val id tbl t = rhs_of (simplify id tbl t)

(* Get all simplifications and subterm-simplifications. *)
fun simplify_info tbl t =
    if in_table_raw tbl t then get_rewrite_info tbl t else
    let
      val subtrm_info = subterm_simplify_info tbl t
      fun get_rewrite_with_id_th (id', th') =
          get_rewrite_info tbl (rhs_of th') |> map (merge_info tbl (id', th'))
      val head_info = subtrm_info |> maps (get_head_rep_with_id_th tbl)
                                  |> max_partial (id_is_eq_ancestor tbl)
                                  |> maps get_rewrite_with_id_th
    in
      subtrm_info @ head_info |> reduce_simp_info tbl
    end

(* Note similarity with get_subterm_rewrite_info. *)
and subterm_simplify_info (tbl as {ctxt, ...}) t =
    if in_table_raw tbl t then get_cached_subterm_rewrite_info tbl t else
    let
      val (t', subs) = Subterms.dest_subterms t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (simplify_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, Subterms.build_equiv ctxt equivs t'))
          |> reduce_simp_info tbl
    end

(* Exported equivalence function. *)
fun is_equiv id tbl (t1, t2) =
    if t1 aconv t2 then true else simp_val id tbl t1 aconv simp_val id tbl t2

fun is_equiv_th id tbl (t1, t2) =
    if t1 aconv t2 then SOME (refl tbl t1)
    else let
      val simp1 = simplify id tbl t1
      val simp2 = simplify id tbl t2
    in
      if rhs_of simp1 aconv rhs_of simp2 then
        SOME (transitive_list [simp1, meta_sym simp2])
      else NONE
    end

fun is_subequiv id tbl (t1, t2) =
    if t1 aconv t2 then true
    else (rhs_of (subterm_simplify id tbl t1))
             aconv (rhs_of (subterm_simplify id tbl t2))

(* infos is a list of (id, th), where the right side of each th is
   fhead as head.
 *)
fun reduce_equivs tbl (fhead, infos) =
    if length infos <= 1 then (fhead, infos) else
    let
      fun args_of id u =
          u |> dest_args |> map (simp_val id tbl)

      fun head_equiv_eq_better (id1, th1) (id2, th2) =
          is_eq_ancestor tbl id1 id2 andalso
          eq_list (op aconv) (args_of id2 (rhs_of th1),
                              args_of id2 (rhs_of th2))
    in
      (fhead, max_partial head_equiv_eq_better infos)
    end

(* No assumption on u. Get list of (id', u') pairs where id <= id', u'
   is in the table equivalent to u under id', and the head of u' is
   the same as that for t. If (id1, u1) and (id2, u2) are such that
   id2 implies id1 and all arguments of u1, u2 are equivalent under
   t2, then (id2, u2) is not included in the results. Arguments are
   ordered for non-AC functions, and unordered for AC functions. This
   function is much faster when u is in table (uses get_all_equiv
   directly).
 *)
fun compute_head_equiv tbl u =
    let
      val _ = if Term.is_open u then
                raise AUTO2 "get_all_head_equivs: u is open" else ()
      fun rep_eq_better (id1, th1) (id2, th2) =
          is_eq_ancestor tbl id1 id2 andalso
          is_equiv id2 tbl (rhs_of th1, rhs_of th2)
      fun get_all_equiv_under_id (id', th') =
          get_all_equiv tbl (rhs_of th') |> map (merge_info tbl (id', th'))

      (* Get all equivs from table. *)
      val all_equiv =
          if in_table_raw tbl u then get_all_equiv tbl u
          else (subterm_simplify_info tbl u)
                   |> maps (get_head_rep_with_id_th tbl)
                   |> max_partial rep_eq_better
                   |> maps get_all_equiv_under_id
                   |> cons ([], refl tbl u)
    in
      (* Sort by head of term, and reduce at each head. *)
      all_equiv |> map (fn (id, th) => (Term.head_of (rhs_of th), (id, th)))
                |> AList.group (op aconv)
                |> map (reduce_equivs tbl)
    end

fun index_head_equiv t tbl =
    tbl |> map_head_equiv (Termtab.update (t, compute_head_equiv tbl t))

fun get_head_equiv (tbl as {head_equiv, ...}) u =
    case Termtab.lookup head_equiv u of
        NONE => compute_head_equiv tbl u
      | SOME info => info

fun get_head_equiv_with_t tbl (id, u) t =
    let
      fun is_valid (uhead, infos) =
          if Term.is_Var t then infos
          else if Term.is_Var (Term.head_of t) then infos
          else if Term.aconv_untyped (uhead, Term.head_of t) then infos
          else []
    in
      (get_head_equiv tbl u)
          |> maps is_valid
          |> merge_box_with_info tbl id
    end

(*** Adding rewrite rules and maintain invariants of the table. ***)

(* Work out all consequences of updating simps in tbl. This includes
   updating simp of neighboring nodes, and updating simps / subsimps
   of nodes for which the current node is a subterm. inits is a list
   of simps to be added, where each element is of the form (id, t ==
   t') updating simp of t. In this function we maintain a list of
   simplifications (to_process) that have been added to the table, but
   whose consequences (on neighboring terms and containing terms) need
   to be processed.
 *)
fun process_update_simp inits tbl =
    let
      fun eq_update ((id, th), (id', th')) =
          (id = id' andalso Thm.prop_of th aconv Thm.prop_of th')

      (* Add the simp (id, th) for the left side of th to the
         table. If (id, th) is not redundant, add (id, th) to the list
         of simps whose consequences need to be processed.
       *)
      fun process_simp (id, th) (to_process, tbl) =
          if simp_less (th, get_rewrite id tbl (lhs_of th)) then
            (insert eq_update (id, th) to_process, update_simp (id, th) tbl)
          else
            (to_process, tbl)

      (* Recompute subterm simplifications of t. Update the subsimp
         table as well as the simp table (in the latter case possibly
         adding to the to_process list.
       *)
      fun process_term t (to_process, tbl) =
          let
            val subsimps = get_subterm_rewrite_info tbl t
            val tbl' = fold update_subsimp subsimps tbl
          in
            fold process_simp subsimps (to_process, tbl')
          end

      (* Pull the first item of to_process and work out its
         consequences.
       *)
      fun update_step (to_process, tbl) =
          case to_process of
              [] => ([], tbl)
            | (id, th) :: rest =>
              let
                val t = lhs_of th
                (* th: t == simp_t, th': t = t', result: t' = simp_t. *)
                fun process_neigh (id', th') =
                    merge_info tbl (id', meta_sym th') (id, th)
                val new_simp = map process_neigh (equiv_neighs tbl t)
              in
                (rest, tbl) |> fold process_simp new_simp
                            |> fold process_term (immediate_contains tbl t)
                            |> update_step
              end
    in
      ([], tbl) |> fold process_simp inits |> update_step |> snd
    end

(* Return list of ids that are descendents of id at which t1 and t2
   are equiv.
 *)
fun equiv_info tbl id (t1, t2) =
    let
      val simp1 = simplify_info tbl t1
      val simp2 = simplify_info tbl t2
      fun compare (id1, th1) (id2, th2) =
          if rhs_of th1 aconv rhs_of th2 then
            [(merge_boxes tbl (id1, id2), transitive_list [th1, meta_sym th2])]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1)
          |> merge_box_with_info tbl id
          |> max_partial (id_is_eq_ancestor tbl)
    end

(* Return list of ids that are descendents of id at which t1 and t2
   are subterm equiv.
 *)
fun subequiv_info tbl id (t1, t2) =
    if not (Term.head_of t1 aconv Term.head_of t2) then []
    else let
      val simp1 = subterm_simplify_info tbl t1
      val simp2 = subterm_simplify_info tbl t2
      fun compare (id1, th1) (id2, th2) =
          if rhs_of th1 aconv rhs_of th2 then
            [(merge_boxes tbl (id1, id2), transitive_list [th1, meta_sym th2])]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1)
          |> merge_box_with_info tbl id
          |> max_partial (id_is_eq_ancestor tbl)
    end

(* Attempt to retrieve property with the given statement from the table. *)
fun get_property tbl (id, prop) =
    let
      val t = dest_arg prop
      val property_t =
          if in_table_raw_for_id tbl (id, t) then
            get_property_for_term tbl t
          else let
            fun process_head_rep (id', eq_th) =
                (get_property_for_term tbl (rhs_of eq_th))
                    |> map (convert_property tbl (id', meta_sym eq_th))
          in
            (subterm_simplify_info tbl t)
                |> maps (get_head_rep_with_id_th tbl)
                |> maps process_head_rep
                |> merge_box_with_info tbl id
          end

      (* For th to justify prop, it should have the same property
         constant as head. Then each of the remaining arguments must
         be equivalent.
       *)
      fun process_property (id', th) =
          if prop_of' th aconv prop then
            [(merge_boxes tbl (id, id'), th)]
          else let
            val subequivs = subequiv_info tbl id' (prop_of' th, prop)
            fun process_info (id'', eq_th) =
                (merge_boxes tbl (id, id''),
                 Thm.equal_elim (make_trueprop_eq eq_th) th)
          in
            map process_info subequivs
          end
    in
      property_t |> maps process_property
                 |> max_partial (property_eq_better tbl)
    end

(* th is an instantiated property update rule (without schematic
   variables). All premises and conclusions of th should be
   properties. Apply this rule at id and below to get new property.
 *)
fun apply_property_update_rule (tbl as {lat, ...}) id th_opt =
    case th_opt of
        NONE => []
      | SOME th =>
        let
          val (prems, _) = strip_horn' th
        in
          if length prems = 0 then [(id, th)]
          else let
            val p_ths = (map (get_property tbl) (map (pair id) prems))
                            |> BoxID.get_all_merges_info lat
                            |> max_partial (BoxID.id_is_eq_ancestor lat)
            fun process_p_th (id', ths) = (id', ths MRS th)
          in
            map process_p_th p_ths
          end
        end

(* Find relevant property updates for term t, apply these to get list
   of new properties.
 *)
fun apply_property_update_on_term (tbl as {ctxt, ...}) id t =
    if fastype_of t = boolT then [] else
    case head_of t of
        Const (nm, _) =>
        let
          val updt_rules = lookup_property_update ctxt nm
          fun process_updt_rule th =
              th |> instantiate_property_update ctxt t
                 |> apply_property_update_rule tbl id
        in
          maps process_updt_rule updt_rules
        end
      | _ => []

(* Work out all consequences of updating the list of properties in
   tbl. This works in a similar manner to process_update_simp. One
   complication is the need to apply property update rules.
 *)
fun process_update_property inits (tbl as {ctxt, ...}) =
    let
      fun eq_property ((id, th), (id', th')) =
          (id = id' andalso Thm.prop_of th aconv Thm.prop_of th')

      fun process_property (id, th) (to_process, tbl) =
          let
            val t = get_property_arg (prop_of' th)
            val property_t = get_property_for_term tbl t
          in
            if exists (fn info => property_eq_better tbl info (id, th))
                      property_t then
              (to_process, tbl)
            else
              (insert eq_property (id, th) to_process,
               add_property_raw (id, th) tbl)
          end

      fun update_step (to_process, tbl) =
          case to_process of
              [] => ([], tbl)
            | (id, th) :: rest =>
              let
                val t = get_property_arg (prop_of' th)

                (* Neighbors of t. Here th: P t, th': t = t', result: P t'. *)
                fun process_neigh (id', eq_th) =
                    convert_property tbl (id', eq_th) (id, th)
                val new_property_neigh = map process_neigh (equiv_neighs tbl t)

                (* Derived properties of t. *)
                val nm = get_property_name (prop_of' th)
                val updt_rules = lookup_property_update ctxt nm
                fun process_updt_rule th =
                    th |> instantiate_property_update ctxt t
                       |> apply_property_update_rule tbl id
                val new_property_t = maps process_updt_rule updt_rules

                (* Derived properties of parent terms of t. *)
                val parents_t = immediate_contains tbl t
                val new_property_ps =
                    maps (apply_property_update_on_term tbl id) parents_t
              in
                (rest, tbl) |> fold process_property new_property_neigh
                            |> fold process_property new_property_t
                            |> fold process_property new_property_ps
                            |> update_step
              end
    in
      ([], tbl) |> fold process_property inits |> update_step |> snd
    end

(* Get list of terms reachable from the terms ts. If trav_contains =
   false, only travel along equiv edges. Otherwise also travel from t
   to any term containing t.
 *)
fun get_reachable_terms trav_contains tbl ts =
    let
      fun helper (new, all) =
          case new of
              [] => ([], all)
            | t :: rest =>
              let
                val contains =
                    if trav_contains then immediate_contains tbl t else []
                val neighs = (equiv_neighs tbl t)
                                 |> map (fn (_, th) => rhs_of th)
                val new' = (contains @ neighs)
                               |> distinct (op aconv)
                               |> subtract (op aconv) all
                val all' = new' @ all
              in
                helper (rest @ new', all')
              end
    in
      snd (helper (ts, ts))
    end

(* Assume t1 and t2 are already in table. Add equiv edge th: t1 == t2 and
   work out all the consequences.
 *)
fun add_rewrite_raw id th tbl =
    let
      val (t1, t2) = (lhs_of th, rhs_of th)

      (* New simplifications. *)
      val t1_rinfo = get_rewrite_info tbl t1
      val t2_rinfo = get_rewrite_info tbl t2
      val t1_news = t2_rinfo |> map (merge_info tbl (id, th))
      val t2_news = t1_rinfo |> map (merge_info tbl (id, meta_sym th))

      (* New properties. *)
      val t1_property = get_property_for_term tbl t1
      val t2_property = get_property_for_term tbl t2
      val t1_newp = t2_property |> map (convert_property tbl (id, meta_sym th))
      val t2_newp = t1_property |> map (convert_property tbl (id, th))
    in
      tbl |> add_equiv (id, th)
          |> process_update_simp (t1_news @ t2_news)
          |> process_update_property (t1_newp @ t2_newp)
          |> fold index_all_equiv (get_reachable_terms false tbl [t1, t2])
    end

(* Add equiv edges so tbl is consistent. That is, any two nodes that
   have the same simp should be connected in the equiv graph. Also
   return the list of equiv edges added.
 *)
fun complete_table tbl =
    let
      fun find_new_equiv t =
          let
            val equivs = get_all_equiv tbl t
          in
            (get_subterm_rewrite_info tbl t)
                |> maps (get_head_rep_with_id_th tbl)
                |> reduce_equiv_info tbl
                |> filter_out (has_equiv_eq_better tbl equivs)
          end
      val new_equivs = (maps find_new_equiv (get_all_terms tbl))
                           |> max_partial (id_is_eq_ancestor tbl)
    in
      case new_equivs of
          [] => ([], tbl)
        | (id, th) :: _ =>
          (* Add bi-directional edges for terms with the same subterm
             simplification. Keep track of list of edges added.
           *)
          let
            val tbl' = tbl |> add_rewrite_raw id th
            val (edges, tbl'') = complete_table tbl'
          in
            ((id, th) :: edges, tbl'')
          end
    end

(* Call complete table, then call index_head_equiv on all terms
   reachable from either side of any edges added, including
   prev_edges.
 *)
fun complete_table_with_edges prev_edges tbl =
    let
      val (edges, tbl') = complete_table tbl
      val update_terms = (prev_edges @ edges)
                             |> map snd
                             |> maps (fn th => [lhs_of th, rhs_of th])
                             |> distinct (op aconv)
                             |> get_reachable_terms true tbl'
    in
      fold index_head_equiv update_terms tbl'
    end

(* Add term t to tbl at box id. The primed version (used in
   add_rewrite_thm) add t and all its subterms to the table. The
   unprimed version also add new equiv edges if necessary, resulting
   is a consistent rewrite table.
 *)
fun add_term' (id, t) tbl =
    if in_table_raw_for_id tbl (id, t) then tbl
    else let
      (* First add subterms. *)
      val imm_subtrms = Subterms.list_subterms t
      val id_subs = map (pair id) imm_subtrms
      val tbl' = tbl |> fold add_term' id_subs |> add_term_raw (id, t)
    in
      (* If t is already in table (just not at id), then we are
         done. Otherwise compute all indexed info for t.
       *)
      if in_table_raw tbl t then tbl'
      else let
        (* Compute simplification and properties of t. Note we are
           doing this in box [] (not id), so it does not need to be
           recomputed if a term is added to a more general box.
         *)
        val simps = get_subterm_rewrite_info tbl' t
        val imm_properties = apply_property_update_on_term tbl' [] t
      in
        tbl' |> fold (add_contain t) imm_subtrms
             |> fold update_simp simps
             |> fold update_subsimp simps
             |> map_context (ACUtil.add_inst_ac_infos t)
             |> process_update_property imm_properties
             |> index_all_equiv t
             |> index_head_equiv t
      end
    end

fun add_term (id, t) tbl =
    if in_table_raw_for_id tbl (id, t) then tbl
    else tbl |> add_term' (id, t) |> complete_table_with_edges []

(* First make sure t1 and t2 are in table. Add t1 == t2 to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_rewrite id eq_th tbl =
    let
      val eq_prop = Thm.prop_of eq_th
      val (t1, t2) = eq_prop |> dest_Trueprop |> dest_eq
      val meta_eq = to_meta_eq eq_th
    in
      if is_equiv id tbl (t1, t2) then tbl
      else
        tbl |> add_term' (id, t1) |> add_term' (id, t2)
            |> add_rewrite_raw id meta_eq
            |> complete_table_with_edges [(id, meta_eq)]
    end

(* First make sure t is in the table. Add property P t to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_property (id, th) tbl =
    let
      val t = get_property_arg (prop_of' th)
    in
      tbl |> add_term (id, t)
          |> process_update_property [(id, th)]
    end

(* Add rewrite rule t1 == t2 to tbl with new prim_id. *)
fun append_rewrite eq_th (tbl as {lat, ...}) =
    let
      val (prim_id, lat') = BoxID.add_prim_id [] lat
    in
      tbl |> map_lat (K lat') |> add_rewrite [prim_id] eq_th
    end

(* Keep only the last prim id and replace it with repl_id in rtype. *)
fun replace_id_for_type rtype insts =
    case rtype of
        SINGLE _ => insts
      | LAST (tbl as {lat, ...}, repl_id) =>
        let
          val prim = (BoxID.num_prim_id lat) - 1
          fun process_info ((id, inst), th) =
              if member (op =) id prim then
                [((merge_boxes tbl (repl_id, remove (op =) prim id), inst), th)]
              else []
        in
          maps process_info insts
        end
fun replace_id_for_type' rtype insts =
    insts |> map (rpair ()) |> replace_id_for_type rtype |> map fst

(* Returns the list of terms in tbl' that is not in tbl. *)
fun get_new_terms (tbl, tbl') =
    let
      fun get_for_term t =
          (in_table_raw_ids tbl' t)
              |> filter_out (fn id => in_table_raw_for_id tbl (id, t))
              |> map (rpair t)
    in
      maps get_for_term (get_all_terms tbl')
    end

fun append_property th (tbl as {lat, ...}) =
    let
      val (prim_id, lat') = BoxID.add_prim_id [] lat
    in
      tbl |> map_lat (K lat') |> add_property ([prim_id], th)
    end

(* Returns the list of new properties in rtype (those depending on the
   new prim_id).
 *)
fun get_new_properties rtype =
    case rtype of
        SINGLE _ => raise AUTO2 "get_new_properties: expect LAST rtype."
      | LAST (tbl as {lat, ...}, _) =>
        let
          val prim = (BoxID.num_prim_id lat) - 1
          fun get_for_term t =
              (get_property_for_term tbl t)
                  |> filter (fn (id, _) => is_eq_ancestor tbl [prim] id)
        in
          maps get_for_term (get_all_terms tbl)
        end

end  (* structure RewriteTable. *)
