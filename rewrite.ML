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
  terms: (box_id list * cterm) Termtab.table,
  (* equiv[a] is list of (id, th), where th is "a == a'" under id. *)
  equiv: ((box_id * thm) list) Termtab.table,
  (* Index of reachability under equiv. *)
  all_equiv: ((box_id * thm) list) Termtab.table,
  (* Index of head equivs. *)
  head_equiv: ((term * (box_id * thm) list) list) Termtab.table,
  (* contain[A] is the list of terms for which A is a direct subterm. *)
  contain: (cterm list) Termtab.table,
  (* Rewrite info of a term. *)
  simp: ((box_id * thm) list) Termtab.table,
  (* Subterm rewrite info of a term. *)
  subsimp: ((box_id * thm) list) Termtab.table,
  (* Reverse of subsimp. Head rep of a term. *)
  reps: ((box_id * thm) list) Termtab.table,
  (* Property list of a term. *)
  property: ((box_id * thm) list) Termtab.table,
  (* Wellformed-ness data of a term. *)
  wellform: ((cterm * (box_id * thm) list) list) Termtab.table,
  (* Current context. *)
  ctxt: Proof.context
}

(* Initial and incremental rewrite tables. In the incremental case,
   new data is added under a fresh primitive ID. The original id of
   the new data, as well as the list of terms that are affected, are
   stored as well.
 *)
datatype rewrite_type = SINGLE of rewrite_table
                      | LAST of rewrite_table * box_id * cterm list

signature REWRITE_TABLE =
sig
  val table_of_rtype: rewrite_type -> rewrite_table
  val single_of_rtype: rewrite_type -> rewrite_type
  val is_single_rtype: rewrite_type -> bool
  val theory_of: rewrite_table -> theory

  (* Dealing with box_ids. *)
  val merge_boxes: rewrite_table -> box_id * box_id -> box_id
  val get_all_merges: rewrite_table -> box_id list list -> box_id list
  val is_eq_ancestor: rewrite_table -> box_id -> box_id -> bool
  val is_eq_descendent: rewrite_table -> box_id -> box_id -> bool
  val merge_box_with_info:
      rewrite_table -> box_id -> (box_id * 'a) list -> (box_id * 'a) list
  val merge_info: rewrite_table -> box_id * thm -> box_id * thm -> box_id * thm
  val id_is_eq_ancestor: rewrite_table -> box_id * thm -> box_id * thm -> bool

  (* Printing facilities. *)
  val to_string: rewrite_table -> string
  val to_string_full: rewrite_table -> string

  (* Construction and modification. *)
  val empty: Proof.context -> rewrite_table
  val map_lat: (box_lattice -> box_lattice) -> rewrite_table -> rewrite_table
  val map_context: (Proof.context -> Proof.context) -> rewrite_table ->
                   rewrite_table

  (* contain table. *)
  val add_contain: cterm -> term -> rewrite_table -> rewrite_table
  val immediate_contains: rewrite_table -> term -> cterm list

  (* terms table. *)
  val in_table_raw_ids: rewrite_table -> term -> box_id list
  val in_table_raw_for_id: rewrite_table -> box_id * term -> bool
  val in_table_raw: rewrite_table -> term -> bool
  val add_term_raw: box_id * cterm -> rewrite_table -> rewrite_table
  val get_all_terms: rewrite_table -> cterm list
  val get_all_id_terms: rewrite_table -> (box_id * cterm) list

  (* equiv table. *)
  val add_equiv: box_id * thm -> rewrite_table -> rewrite_table
  val equiv_neighs: rewrite_table -> term -> (box_id * thm) list
  val compute_all_equiv: rewrite_table -> cterm -> (box_id * thm) list
  val index_all_equiv: cterm -> rewrite_table -> rewrite_table
  val get_all_equiv: rewrite_table -> term -> (box_id * thm) list

  (* simp table. *)
  val reduce_simp_info:
      rewrite_table -> (box_id * thm) list -> (box_id * thm) list
  val update_simp: box_id * thm -> rewrite_table -> rewrite_table
  val get_rewrite_info: rewrite_table -> cterm -> (box_id * thm) list
  val get_rewrite: box_id -> rewrite_table -> cterm -> thm

  (* subsimp and rep tables. *)
  val merge_simp_infos:
      rewrite_table -> (box_id * thm) list list -> (box_id * thm list) list
  val get_subterm_rewrite_info: rewrite_table -> cterm -> (box_id * thm) list
  val remove_rep: box_id * thm -> rewrite_table -> rewrite_table
  val update_subsimp: box_id * thm -> rewrite_table -> rewrite_table
  val get_head_rep_info: rewrite_table -> term -> (box_id * thm) list
  val get_head_rep: box_id -> rewrite_table -> term -> thm option
  val get_head_rep_with_id_th:
      rewrite_table -> box_id * thm -> (box_id * thm) list
  val get_cached_subterm_rewrite_info:
      rewrite_table -> term -> (box_id * thm) list
  val get_cached_subterm_rewrite: box_id -> rewrite_table -> cterm -> thm

  (* property table. *)
  val get_property_for_term: rewrite_table -> term -> (box_id * thm) list
  val add_property_raw: box_id * thm -> rewrite_table -> rewrite_table
  val convert_property:
      rewrite_table -> box_id * thm -> box_id * thm -> box_id * thm

  (* Simplification of arbitrary terms. *)
  val head_simplify: box_id -> rewrite_table -> cterm -> thm
  val simplify: box_id -> rewrite_table -> cterm -> thm
  val subterm_simplify: box_id -> rewrite_table -> cterm -> thm
  val simp_val: box_id -> rewrite_table -> cterm -> cterm
  val simp_val_t: box_id -> rewrite_table -> term -> term
  val simplify_info: rewrite_table -> cterm -> (box_id * thm) list
  val subterm_simplify_info: rewrite_table -> cterm -> (box_id * thm) list
  val is_equiv: box_id -> rewrite_table -> cterm * cterm -> bool
  val is_equiv_t: box_id -> rewrite_table -> term * term -> bool
  val is_subequiv: box_id -> rewrite_table -> cterm * cterm -> bool

  (* head_equiv table. *)
  val reduce_equivs:
      rewrite_table -> term * (box_id * thm) list -> term * (box_id * thm) list
  val compute_head_equiv:
      rewrite_table -> cterm -> (term * (box_id * thm) list) list
  val index_head_equiv: cterm -> rewrite_table -> rewrite_table
  val get_head_equiv:
      rewrite_table -> cterm -> (term * (box_id * thm) list) list
  val get_head_equiv_with_t:
      rewrite_table -> box_id * cterm -> term -> (box_id * thm) list

  (* Update of whole rewrite table. *)
  val process_update_simp: (box_id * thm) list -> rewrite_table -> rewrite_table
  val equiv_info:
      rewrite_table -> box_id -> cterm * cterm -> (box_id * thm) list
  val equiv_info_t:
      rewrite_table -> box_id -> term * term -> (box_id * thm) list
  val subequiv_info:
      rewrite_table -> box_id -> cterm * cterm -> (box_id * thm) list
  val get_property: rewrite_table -> box_id * cterm -> (box_id * thm) list
  val get_property_t: rewrite_table -> box_id * term -> (box_id * thm) list
  val apply_property_update_rule:
      rewrite_table -> box_id -> thm option -> (box_id * thm) list
  val apply_property_update_on_term:
      rewrite_table -> box_id -> term -> (box_id * thm) list
  val process_update_property:
      (box_id * thm) list -> rewrite_table -> rewrite_table
  val get_reachable_terms: bool -> rewrite_table -> cterm list -> cterm list
  val add_rewrite_raw: box_id -> thm -> rewrite_table -> rewrite_table
  val complete_table: rewrite_table -> (box_id * thm) list * rewrite_table
  val complete_table_with_edges:
      (box_id * thm) list -> rewrite_table -> rewrite_table
  val initialize_wellform_data: term -> rewrite_table -> rewrite_table
  val add_term: box_id * cterm -> rewrite_table -> rewrite_table
  val add_rewrite: box_id * thm -> rewrite_table -> rewrite_table
  val add_property: box_id * thm -> rewrite_table -> rewrite_table

  (* wellform table. *)
  val get_wellform_for_term:
      rewrite_table -> term -> (cterm * (box_id * thm) list) list
  val get_wellform_infos_for_term: rewrite_table -> term -> (box_id * thm) list
  val convert_wellform:
      rewrite_table -> box_id * thm -> box_id * thm -> box_id * thm
  val get_wellform: rewrite_table -> box_id * cterm -> (box_id * thm) list
  val get_wellform_t: rewrite_table -> box_id * term -> (box_id * thm) list
  val get_complete_wellform:
      rewrite_table -> box_id * cterm -> (box_id * thm list) list
  val term_to_wfterm_on_tbl:
      rewrite_table -> term list -> box_id * cterm -> (box_id * wfterm) list
  val term_to_wfterm_on_tbl_t:
      rewrite_table -> term list -> box_id * term -> (box_id * wfterm) list

  (* Update to wellform table. *)
  val add_wellform_data_raw:
      term * (box_id * thm) -> rewrite_table -> rewrite_table
  val rewrite_find_fact: rewrite_table -> (box_id * thm) list ->
                         box_id * cterm -> (box_id * thm) list
  val complete_wellform_data_for_terms:
      (box_id * thm) list -> term list -> rewrite_table -> rewrite_table
  val complete_wellform_data:
      (box_id * thm) list -> rewrite_table -> rewrite_table

  (* Updating rewrite table from list of (id, th) pairs. *)
  val get_new_terms: rewrite_table * rewrite_table -> (box_id * cterm) list
  val get_new_wellform_data:
      int -> rewrite_table -> (term * (box_id * thm)) list
  val classify_th: theory -> thm -> string
  val relevant_terms_single: theory -> thm -> cterm list
  val add_infos: (box_id * thm) list -> box_id * thm list -> rewrite_table ->
                 rewrite_table
  val get_incr_type:
      rewrite_table -> (box_id * thm) list -> box_id * thm list -> rewrite_type

  (* Incremental tables. *)
  val filter_id_for_type:
      rewrite_type -> ((box_id * 'a) * 'b) list -> ((box_id * 'a) * 'b) list
  val replace_id_for_type:
      rewrite_type -> ((box_id * 'a) * 'b) list -> ((box_id * 'a) * 'b) list
  val replace_id_for_type':
      rewrite_type -> (box_id * 'a) list -> (box_id * 'a) list
end;

structure RewriteTable : REWRITE_TABLE =
struct

open Base
open UtilLogic

fun table_of_rtype rtype =
    case rtype of SINGLE tbl => tbl | LAST (tbl, _, _) => tbl
fun single_of_rtype rtype =
    case rtype of SINGLE tbl => SINGLE tbl | LAST (tbl, _, _) => SINGLE tbl
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
    "Terms: " ^ (to_string_table ctxt terms (string_of_box_ids o fst)) ^
    "\nequiv table:\n" ^ (to_string_table ctxt equiv (print_infos ctxt)) ^
    "\nsimp table:\n" ^ (to_string_table ctxt simp (print_infos ctxt)) ^
    "\nsubsimp table:\n" ^ (to_string_table ctxt subsimp (print_infos ctxt)) ^
    "\nreps table:\n" ^ (to_string_table ctxt reps (print_infos ctxt))

(*** empty and basic modification functions. ***)
fun empty ctxt = {
  lat = BoxID.empty, terms = Termtab.empty, equiv = Termtab.empty,
  all_equiv = Termtab.empty, head_equiv = Termtab.empty,
  contain = Termtab.empty, simp = Termtab.empty, subsimp = Termtab.empty,
  reps = Termtab.empty, property = Termtab.empty, wellform = Termtab.empty,
  ctxt = ctxt}

fun map_lat f {lat, terms, equiv, all_equiv, head_equiv, contain, simp, subsimp,
               reps, property, wellform, ctxt} =
    let
      val lat' = f lat
      fun clean tb id_fun =
          tb |> Termtab.map
             (fn _ => filter (BoxID.is_box_supported lat' o id_fun))

      fun clean_terms_1 (ids, ct) =
          (filter (BoxID.is_box_supported lat') ids, ct)

      fun clean_terms tb =
          tb |> Termtab.map (fn _ => clean_terms_1)

      fun clean_head_equiv_1 (fhead, infos) =
          let
            val infos' = filter (BoxID.is_box_supported lat' o fst) infos
          in
            if null infos' then [] else [(fhead, infos')]
          end

      fun clean_head_equiv tb =
          tb |> Termtab.map (fn _ => maps clean_head_equiv_1)

      fun clean_wellform_1 (ctarget, infos) =
          (ctarget, filter (BoxID.is_box_supported lat' o fst) infos)

      fun clean_wellform tb =
          tb |> Termtab.map (fn _ => map clean_wellform_1)
    in
      {lat = lat', terms = clean_terms terms, equiv = clean equiv fst,
       all_equiv = clean all_equiv fst,
       head_equiv = clean_head_equiv head_equiv,
       contain = contain, simp = clean simp fst, subsimp = clean subsimp fst,
       reps = clean reps fst, property = clean property fst,
       wellform = clean_wellform wellform, ctxt = ctxt}
    end

fun map_terms f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = f terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, wellform = wellform, ctxt = ctxt}
fun map_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = f equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, wellform = wellform, ctxt = ctxt}
fun map_all_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                     subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = f all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, wellform = wellform, ctxt = ctxt}
fun map_head_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                      subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = f head_equiv, contain = contain, simp = simp,
     subsimp = subsimp, reps = reps, property = property,
     wellform = wellform, ctxt = ctxt}
fun map_contain f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = f contain, simp = simp,
     subsimp = subsimp, reps = reps, property = property,
     wellform = wellform, ctxt = ctxt}
fun map_simp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = f simp,
     subsimp = subsimp, reps = reps, property = property,
     wellform = wellform, ctxt = ctxt}
fun map_subsimp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp,
     subsimp = f subsimp, reps = reps, property = property,
     wellform = wellform, ctxt = ctxt}
fun map_reps f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = f reps, property = property, wellform = wellform, ctxt = ctxt}
fun map_property f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                    subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = f property, wellform = wellform, ctxt = ctxt}
fun map_wellform f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                    subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, wellform = f wellform, ctxt = ctxt}
fun map_context f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, property, wellform, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, property = property, wellform = wellform, ctxt = f ctxt}

(*** Basic manipulation of contain table. ***)

(* Add the information that t contains subt directly. *)
fun add_contain ct subt (tbl as {contain, ...}) =
    let
      val contain_subt = the_default [] (Termtab.lookup contain subt)
    in
      if member (op aconvc) contain_subt ct then tbl
      else tbl |> map_contain (Termtab.update (subt,  ct :: contain_subt))
    end

(* Get all terms that directly contains t. *)
fun immediate_contains {contain, ...} t =
    the_default [] (Termtab.lookup contain t)

(*** Basic manipulation of the terms table. ***)

(* Return ids in which t is directly in table. *)
fun in_table_raw_ids {terms, ...} t =
    case Termtab.lookup terms t of
        NONE => []
      | SOME (ids, _) => ids

(* Whether the term is present in table at the given id. *)
fun in_table_raw_for_id tbl (id, t) =
    exists (is_eq_descendent tbl id) (in_table_raw_ids tbl t)

(* Whether the term is present at any id. *)
fun in_table_raw tbl t =
    length (in_table_raw_ids tbl t) > 0

(* Add t to table at the given id. *)
fun add_term_raw (id, ct) tbl =
    let
      val t = Thm.term_of ct
      val prev_ids = in_table_raw_ids tbl t
      val ids_t = (id :: prev_ids)
                      |> max_partial (is_eq_ancestor tbl)
    in
      tbl |> map_terms (Termtab.update (t, (ids_t, ct)))
    end

(* Return list of all terms (at any ids) present in table. *)
fun get_all_terms {terms, ...} =
    map (fn (_, (_, ct)) => ct) (Termtab.dest terms)

(* Return list of all terms with ids present in table. *)
fun get_all_id_terms {terms, ...} =
    maps (fn (_, (ids, ct)) => map (rpair ct) ids)
         (Termtab.dest terms)

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
fun compute_all_equiv tbl ct =
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
      val init = ([], Thm.reflexive ct)
    in
      snd (helper ([init], [init]))
    end

fun index_all_equiv ct tbl =
    tbl |> map_all_equiv (
      Termtab.update (Thm.term_of ct, compute_all_equiv tbl ct))

fun get_all_equiv {all_equiv, ...} t =
    the (Termtab.lookup all_equiv t)
    handle Option.Option => raise Fail "all_equiv: not found"

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
      val ct = Thm.lhs_of th
      val t = Thm.term_of ct
      val simp_t = the_default [([], Thm.reflexive ct)] (Termtab.lookup simp t)
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
fun get_rewrite_info {simp, ...} ct =
    case Termtab.lookup simp (Thm.term_of ct) of
        NONE => [([], Thm.reflexive ct)]
      | SOME infos => infos

(* Return the rewrite of t under a given id, as stored directly in
   table. Return t == t if not in table.
 *)
fun get_rewrite id tbl ct =
    case get_rewrite_info tbl ct of
        [] => Thm.reflexive ct
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
fun get_subterm_rewrite_info tbl ct =
    let
      val (ct', subs) = Subterms.dest_subterms ct
    in
      if null subs then [([], Thm.reflexive ct)] else
      (map (get_rewrite_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, Subterms.build_equiv equivs ct'))
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
fun get_cached_subterm_rewrite id tbl ct =
    case get_cached_subterm_rewrite_info tbl (Thm.term_of ct) of
        [] => Thm.reflexive ct
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
      val t = Property.get_property_arg (prop_of' th)
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
fun head_simplify id tbl ct =
    case get_head_rep id tbl (Thm.term_of ct) of
        NONE => Thm.reflexive ct
      | SOME th => transitive_list [th, get_rewrite id tbl (Thm.rhs_of th)]

(* First simplify subterms, then simplify head. *)
fun simplify id tbl ct =
    if in_table_raw tbl (Thm.term_of ct) then
      get_rewrite id tbl ct else
    let
      val th = subterm_simplify id tbl ct
    in
      transitive_list [th, head_simplify id tbl (Thm.rhs_of th)]
    end

(* Simplify subterms, but not head. *)
and subterm_simplify id tbl ct =
    if in_table_raw tbl (Thm.term_of ct) then
      get_cached_subterm_rewrite id tbl ct else
    let
      val (ct', subs) = Subterms.dest_subterms ct
      val equivs = map (simplify id tbl) subs
    in
      Subterms.build_equiv equivs ct'
    end

(* Convenient function for getting simplified value. *)
fun simp_val id tbl ct = Thm.rhs_of (simplify id tbl ct)

fun simp_val_t id (tbl as {ctxt, ...}) t =
    rhs_of (simplify id tbl (cert ctxt t))

(* Get all simplifications and subterm-simplifications. *)
fun simplify_info tbl ct =
    if in_table_raw tbl (Thm.term_of ct) then
      get_rewrite_info tbl ct else
    let
      val subtrm_info = subterm_simplify_info tbl ct
      fun get_rewrite_with_id_th (id', th') =
          (get_rewrite_info tbl (Thm.rhs_of th'))
              |> map (merge_info tbl (id', th'))
      val head_info = subtrm_info |> maps (get_head_rep_with_id_th tbl)
                                  |> max_partial (id_is_eq_ancestor tbl)
                                  |> maps get_rewrite_with_id_th
    in
      subtrm_info @ head_info |> reduce_simp_info tbl
    end

(* Note similarity with get_subterm_rewrite_info. *)
and subterm_simplify_info tbl ct =
    if in_table_raw tbl (Thm.term_of ct) then
      get_cached_subterm_rewrite_info tbl (Thm.term_of ct) else
    let
      val (ct', subs) = Subterms.dest_subterms ct
    in
      if null subs then [([], Thm.reflexive ct)] else
      (map (simplify_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, Subterms.build_equiv equivs ct'))
          |> reduce_simp_info tbl
    end

(* Exported equivalence function. *)
fun is_equiv id tbl (ct1, ct2) =
    ct1 aconvc ct2 orelse simp_val id tbl ct1 aconvc simp_val id tbl ct2

fun is_equiv_t id (tbl as {ctxt, ...}) (t1, t2) =
    t1 aconv t2 orelse is_equiv id tbl (cert ctxt t1, cert ctxt t2)

fun is_subequiv id tbl (ct1, ct2) =
    if ct1 aconvc ct2 then true
    else (rhs_of (subterm_simplify id tbl ct1))
             aconv (rhs_of (subterm_simplify id tbl ct2))

(* infos is a list of (id, th), where the right side of each th is
   fhead as head.
 *)
fun reduce_equivs tbl (fhead, infos) =
    if length infos <= 1 then (fhead, infos) else
    let
      fun args_of id cu =
          cu |> dest_cargs |> map (simp_val id tbl)

      fun head_equiv_eq_better (id1, th1) (id2, th2) =
          is_eq_ancestor tbl id1 id2 andalso
          eq_list (op aconvc) (args_of id2 (Thm.rhs_of th1),
                               args_of id2 (Thm.rhs_of th2))
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
fun compute_head_equiv tbl cu =
    let
      val u = Thm.term_of cu
      val _ = if Term.is_open u then
                raise Fail "get_all_head_equivs: u is open" else ()
      fun rep_eq_better (id1, th1) (id2, th2) =
          is_eq_ancestor tbl id1 id2 andalso
          is_equiv id2 tbl (Thm.rhs_of th1, Thm.rhs_of th2)
      fun get_all_equiv_under_id (id', th') =
          get_all_equiv tbl (rhs_of th') |> map (merge_info tbl (id', th'))

      (* Get all equivs from table. *)
      val all_equiv =
          if in_table_raw tbl u then get_all_equiv tbl u
          else (subterm_simplify_info tbl cu)
                   |> maps (get_head_rep_with_id_th tbl)
                   |> max_partial rep_eq_better
                   |> maps get_all_equiv_under_id
                   |> cons ([], Thm.reflexive cu)
    in
      (* Sort by head of term, and reduce at each head. *)
      all_equiv |> map (fn (id, th) => (Term.head_of (rhs_of th), (id, th)))
                |> AList.group (op aconv)
                |> map (reduce_equivs tbl)
    end

fun index_head_equiv ct tbl =
    tbl |> map_head_equiv (
      Termtab.update (Thm.term_of ct, compute_head_equiv tbl ct))

(* Get list of head equivs for cu, indexed by head term. *)
fun get_head_equiv (tbl as {head_equiv, ...}) cu =
    case Termtab.lookup head_equiv (Thm.term_of cu) of
        NONE => compute_head_equiv tbl cu
      | SOME info => info

(* Get list of head equivs for cu, whose head agrees (or matches) with t. *)
fun get_head_equiv_with_t tbl (id, cu) t =
    let
      fun is_valid (uhead, infos) =
          if Term.is_Var t then infos
          else if Term.is_Var (Term.head_of t) then infos
          else if Term.aconv_untyped (uhead, Term.head_of t) then infos
          else []
    in
      (get_head_equiv tbl cu)
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
          if simp_less (th, get_rewrite id tbl (Thm.lhs_of th)) then
            (insert eq_update (id, th) to_process, update_simp (id, th) tbl)
          else
            (to_process, tbl)

      (* Recompute subterm simplifications of t. Update the subsimp
         table as well as the simp table (in the latter case possibly
         adding to the to_process list.
       *)
      fun process_term ct (to_process, tbl) =
          let
            val subsimps = get_subterm_rewrite_info tbl ct
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
fun equiv_info tbl id (ct1, ct2) =
    let
      val simp1 = simplify_info tbl ct1
      val simp2 = simplify_info tbl ct2
      fun compare (id1, th1) (id2, th2) =
          if rhs_of th1 aconv rhs_of th2 then
            [(merge_boxes tbl (id1, id2), transitive_list [th1, meta_sym th2])]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1)
          |> merge_box_with_info tbl id
          |> max_partial (id_is_eq_ancestor tbl)
    end

fun equiv_info_t (tbl as {ctxt, ...}) id (t1, t2) =
    equiv_info tbl id (cert ctxt t1, cert ctxt t2)

(* Return list of ids that are descendents of id at which t1 and t2
   are subterm equiv.
 *)
fun subequiv_info tbl id (ct1, ct2) =
    if not ((Term.head_of (Thm.term_of ct1))
                aconv Term.head_of (Thm.term_of ct2)) then []
    else let
      val simp1 = subterm_simplify_info tbl ct1
      val simp2 = subterm_simplify_info tbl ct2
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
fun get_property tbl (id, cprop) =
    let
      val ct = Thm.dest_arg cprop
      val t = Thm.term_of ct
      fun head_agrees (_, th) =
          Term.head_of (prop_of' th) aconv Term.head_of (Thm.term_of cprop)

      val property_t =
          if in_table_raw_for_id tbl (id, t) then
            (get_property_for_term tbl t)
                |> filter head_agrees
          else let
            fun process_head_rep (id', eq_th) =
                (get_property_for_term tbl (rhs_of eq_th))
                    |> filter head_agrees
                    |> map (convert_property tbl (id', meta_sym eq_th))
          in
            (subterm_simplify_info tbl ct)
                |> maps (get_head_rep_with_id_th tbl)
                |> maps process_head_rep
          end
    in
      property_t |> merge_box_with_info tbl id
                 |> max_partial (property_eq_better tbl)
    end

fun get_property_t (tbl as {ctxt, ...}) (id, prop) =
    get_property tbl (id, cert ctxt prop)

(* th is an instantiated property update rule (without schematic
   variables). All premises and conclusions of th should be
   properties. Apply this rule at id and below to get new property.
 *)
fun apply_property_update_rule (tbl as {lat, ...}) id th_opt =
    case th_opt of
        NONE => []
      | SOME th =>
        let
          val (cprems, _) = cstrip_horn' th
        in
          if null cprems then [(id, th)]
          else let
            val p_ths = (map (get_property tbl) (map (pair id) cprems))
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
          val updt_rules = Property.lookup_property_update ctxt nm
          fun process_updt_rule th =
              th |> Property.instantiate_property_update ctxt t
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
      val thy = theory_of tbl

      fun eq_property ((id, th), (id', th')) =
          (id = id' andalso Thm.prop_of th aconv Thm.prop_of th')

      fun process_property (id, th) (to_process, tbl) =
          let
            val t = Property.get_property_arg (prop_of' th)
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
                val t = Property.get_property_arg (prop_of' th)

                (* Neighbors of t. Here th: P t, th': t = t', result: P t'. *)
                fun process_neigh (id', eq_th) =
                    convert_property tbl (id', eq_th) (id, th)
                val new_property_neigh = map process_neigh (equiv_neighs tbl t)

                (* Derived properties of t. *)
                val ts = Property.strip_property_field thy t
                val nm = Property.get_property_name (prop_of' th)
                val updt_rules = Property.lookup_property_update ctxt nm
                fun process_updt_rule (t, th) =
                    th |> Property.instantiate_property_update ctxt t
                       |> apply_property_update_rule tbl id
                val new_property_t = maps process_updt_rule
                                          (all_pairs (ts, updt_rules))

                (* Derived properties of parent terms of t. *)
                val parents_t = map (Thm.term_of) (immediate_contains tbl t)
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
fun get_reachable_terms trav_contains tbl cts =
    let
      fun helper (new, all) =
          case new of
              [] => ([], all)
            | ct :: rest =>
              let
                val t = Thm.term_of ct
                val contains =
                    if trav_contains then immediate_contains tbl t else []
                val neighs = (equiv_neighs tbl t)
                                 |> map (fn (_, th) => Thm.rhs_of th)
                val new' = (contains @ neighs)
                               |> distinct (op aconvc)
                               |> subtract (op aconvc) all
                val all' = new' @ all
              in
                helper (rest @ new', all')
              end
    in
      snd (helper (cts, cts))
    end

(* Assume t1 and t2 are already in table. Add equiv edge th: t1 == t2 and
   work out all the consequences.
 *)
fun add_rewrite_raw id th tbl =
    let
      val (ct1, ct2) = (Thm.lhs_of th, Thm.rhs_of th)
      val (t1, t2) = (Thm.term_of ct1, Thm.term_of ct2)

      (* New simplifications. *)
      val t1_rinfo = get_rewrite_info tbl ct1
      val t2_rinfo = get_rewrite_info tbl ct2
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
          |> fold index_all_equiv (get_reachable_terms false tbl [ct1, ct2])
    end

(* Add equiv edges so tbl is consistent. That is, any two nodes that
   have the same simp should be connected in the equiv graph. Also
   return the list of equiv edges added.
 *)
fun complete_table tbl =
    let
      fun find_new_equiv ct =
          let
            val equivs = get_all_equiv tbl (Thm.term_of ct)
          in
            (get_subterm_rewrite_info tbl ct)
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
                             |> maps (fn th => [Thm.lhs_of th, Thm.rhs_of th])
                             |> distinct (op aconvc)
                             |> get_reachable_terms true tbl'
    in
      fold index_head_equiv update_terms tbl'
    end

(* Initialize wellform data for term t, with (currently) empty slots
   for each target.
 *)
fun initialize_wellform_data t (tbl as {ctxt, ...}) =
    let
      val thy = theory_of tbl
      val targets = map (cert ctxt) (WellForm.lookup_wellform_data thy t)
    in
      if null targets then tbl
      else tbl |> map_wellform (Termtab.update (t, map (rpair []) targets))
    end

(* Add term t to tbl at box id. The primed version (used in
   add_rewrite_thm) add t and all its subterms to the table. The
   unprimed version also add new equiv edges if necessary, resulting
   is a consistent rewrite table.
 *)
fun add_term' (id, ct) tbl =
    if in_table_raw_for_id tbl (id, Thm.term_of ct) then tbl
    else let
      (* First add subterms. *)
      val imm_subtrms = Subterms.list_subterms ct
      val id_subs = map (pair id) imm_subtrms
      val tbl' = tbl |> fold add_term' id_subs |> add_term_raw (id, ct)
      val t = Thm.term_of ct
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
        val simps = get_subterm_rewrite_info tbl' ct
        val imm_properties = apply_property_update_on_term tbl' [] t
      in
        tbl' |> fold (add_contain ct) (map Thm.term_of imm_subtrms)
             |> fold update_simp simps
             |> fold update_subsimp simps
             |> process_update_property imm_properties
             |> initialize_wellform_data t
             |> index_all_equiv ct
             |> index_head_equiv ct
      end
    end

fun add_term (id, ct) tbl =
    if in_table_raw_for_id tbl (id, Thm.term_of ct) then tbl
    else tbl |> add_term' (id, ct) |> complete_table_with_edges []

(* First make sure t1 and t2 are in table. Add t1 == t2 to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_rewrite (id, eq_th) tbl =
    let
      val meta_eq = to_meta_eq eq_th
      val (ct1, ct2) = meta_eq |> Thm.cprop_of |> Thm.dest_equals
    in
      if is_equiv id tbl (ct1, ct2) then tbl
      else
        tbl |> add_term' (id, ct1) |> add_term' (id, ct2)
            |> add_rewrite_raw id meta_eq
            |> complete_table_with_edges [(id, meta_eq)]
    end

(* First make sure t is in the table. Add property P t to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_property (id, th) tbl =
    let
      val ct = Property.get_property_arg_th th
    in
      tbl |> add_term (id, ct)
          |> process_update_property [(id, th)]
    end

fun get_wellform_for_term {wellform, ...} t =
    the_default [] (Termtab.lookup wellform t)

(* Given a term t, return the wellform data for t in a list of (id,
   th) pairs.
 *)
fun get_wellform_infos_for_term tbl t =
    maps snd (get_wellform_for_term tbl t)

(* Given (id, th) a wellform data for the left side of eq_th, convert
   to a wellform data for the right side.
 *)
fun convert_wellform tbl (id', eq_th) (id, th) =
    let
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
    in
      if lhs aconv rhs then (id, th)
      else let
        val thy = theory_of tbl
      in
        case WellForm.lookup_wellform_pattern thy (lhs_of eq_th, prop_of' th) of
            NONE => raise Fail "convert_wellform: invalid input."
          | SOME (pat, data_pat) =>
            let
              (* Cannot use eq_th directly. Rather, find all the
                 equivalences again for all the subterms.
               *)
              val cargs1 = dest_cargs (Thm.lhs_of eq_th)
              val cargs2 = dest_cargs (Thm.rhs_of eq_th)
              val eq_ths =
                  map (fn (ct, ct') =>
                          (equiv_info tbl id' (ct, ct'))
                              |> filter (fn (id'', _) => id'' = id')
                              |> map snd |> the_single)
                      (cargs1 ~~ cargs2)
              val pat_args = dest_args pat
              val th' = apply_to_thm' (
                    pattern_rewr_conv data_pat (pat_args ~~ eq_ths)) th

              (* Check the result is in the right form. *)
              val subst' = pat_args ~~ map Thm.term_of cargs2
              val prop' = Term.subst_atomic subst' data_pat
              val _ = assert (prop_of' th' aconv prop')
                             "convert_wellform: invalid output."
            in
              (merge_boxes tbl (id, id'), th')
            end
      end
    end

(* Retrieve wellform data for the given term. May need to rewrite t up
   to subterm equivalence.
 *)
fun get_wellform tbl (id, ct) =
    let
      val t = Thm.term_of ct
    in
      if in_table_raw_for_id tbl (id, t) then
        (get_wellform_infos_for_term tbl t)
            |> merge_box_with_info tbl id
      else
        let
          (* eq_th rewrites t to t', where t' is subterm equivalent to
             t and in the table. Obtain wellform data for t', then
             convert them into wellform data for t.
           *)
          fun process_head_rep (id', eq_th) =
              (get_wellform_infos_for_term tbl (rhs_of eq_th))
                  |> map (convert_wellform tbl (id', meta_sym eq_th))
        in
          (subterm_simplify_info tbl ct)
              |> maps (get_head_rep_with_id_th tbl)
              |> maps process_head_rep
              |> merge_box_with_info tbl id
              |> max_partial (property_eq_better tbl)
        end
    end

fun get_wellform_t (tbl as {ctxt, ...}) (id, t) =
    get_wellform tbl (id, cert ctxt t)

(* Retrieve the complete set of wellform data for term t, indexed by
   box id.
 *)
fun get_complete_wellform (tbl as {lat, ...}) (id, ct) =
    let
      val thy = theory_of tbl
      val t = Thm.term_of ct
      val targets = WellForm.lookup_wellform_data thy t
      val data = (get_wellform tbl (id, ct))
                     |> map (fn (id', th) => (prop_of' th, (id', th)))
                     |> AList.group (op aconv)
                     |> map snd
      val _ = assert (length data <= length targets)
                     "get_complete_wellform: unexpected length data"
    in
      if length data < length targets then []
      else data |> BoxID.get_all_merges_info lat
                |> max_partial (BoxID.id_is_eq_ancestor lat)
    end

(* Given a regular term, construct a wellformed term by adding
   theorems corresponding to any combination whose head agrees with
   one of fheads.
 *)
fun term_to_wfterm_on_tbl (tbl as {lat, ...}) fheads (id, ct) =
    case Thm.term_of ct of
        _ $ _ =>
        let
          val t = Thm.term_of ct
          val (cf, cargs) = Drule.strip_comb ct
        in
          if forall (fn fhead => not (is_head fhead t)) fheads then
            [(id, WfTerm ct)] else
          let
            val wfdata = get_complete_wellform tbl (id, ct)
            fun process_wfdata (id', ths) =
                (* For each wellform data of t at box id', retrieve
                   the wellform data of each argment, then merge
                   together.
                 *)
                cargs |> map (pair id')
                      |> map (term_to_wfterm_on_tbl tbl fheads)
                      |> BoxID.get_all_merges_info lat
                      |> map (fn (id'', arg') => (id'', WfComb (cf, arg', ths)))
          in
            (maps process_wfdata wfdata)
                |> max_partial (BoxID.id_is_eq_ancestor lat)
          end
        end
      | _ => [(id, WfTerm ct)]

fun term_to_wfterm_on_tbl_t (tbl as {ctxt, ...}) fheads (id, t) =
    term_to_wfterm_on_tbl tbl fheads (id, cert ctxt t)

(* Add the given wellform data (id, th) for the term t to the table. *)
fun add_wellform_data_raw (t, (id, th)) tbl =
    let
      val cprop = cprop_of' th
      val wellform_data = get_wellform_for_term tbl t
      val infos = the (AList.lookup (op aconvc) wellform_data cprop)
                  handle Option.Option => raise Fail "add_wellform_data_raw"
    in
      if exists (fn info => property_eq_better tbl info (id, th)) infos then tbl
      else let
        val infos' = infos |> filter_out (property_eq_better tbl (id, th))
                           |> cons (id, th)
      in
        tbl |> map_wellform (
          Termtab.map_entry t (AList.map_entry (op aconvc) cprop (K infos')))
      end
    end

(* Given a list of (id, th) pairs, attempt to justify t (of type bool)
   using the theorems, or equalities / properties in the rewrite
   table. Return a list of (id', th') pairs, where the statement of
   th' is t.
 *)
fun rewrite_find_fact tbl infos (id, ct) =
    let
      fun match_fact (id', th) =
          if not (is_Trueprop (Thm.prop_of th)) then [] else
          let
            val id'' = merge_boxes tbl (id, id')
            val ct' = cprop_of' th
            val eq_info = equiv_info tbl id'' (ct', ct)

            fun process_info (id''', eq_th) =
                let
                  val eq_th' = make_trueprop_eq eq_th
                in
                  (id''', Thm.equal_elim eq_th' th)
                end
          in
            map process_info eq_info
          end

      val t = Thm.term_of ct
    in
      if is_eq_term t then  (* Equality case *)
        map (apsnd to_obj_eq)
            (equiv_info tbl id (cdest_eq ct))
      else if Property.is_property_const (theory_of tbl) t then
        (* Property case *)
        get_property tbl (id, ct)
      else  (* General case *)
        maps match_fact infos
    end

(* Given a list of (id, th), complete the wellform data. New wellform
   data could be added when:

   - There are new theorems in the list of (id, th).

   - There are new properties added.

   - There are new equalities added.
 *)
fun complete_wellform_data_for_terms infos ts tbl =
    let
      fun get_for_t t =
          let
            val cur_data = get_wellform_for_term tbl t
            val target_ids = in_table_raw_ids tbl t

            fun is_target (id, cprop) =
                let
                  val prop_data = the (AList.lookup (op aconvc) cur_data cprop)
                in
                  not (exists (fn (id', _) => is_eq_ancestor tbl id' id)
                              prop_data)
                end

            val targets = (all_pairs (target_ids, map fst cur_data))
                              |> filter is_target
          in
            targets |> maps (rewrite_find_fact tbl infos)
                    |> map (pair t)
          end

      val all_data = maps get_for_t ts
    in
      fold add_wellform_data_raw all_data tbl
    end

fun complete_wellform_data infos (tbl as {wellform, ...}) =
    let
      val ts = Termtab.keys wellform
    in
      complete_wellform_data_for_terms infos ts tbl
    end

(* Returns the list of terms in tbl' that is not in tbl. *)
fun get_new_terms (tbl, tbl') =
    let
      fun get_for_term ct =
          (in_table_raw_ids tbl' (Thm.term_of ct))
              |> filter_out (fn id =>
                                in_table_raw_for_id tbl (id, Thm.term_of ct))
              |> map (rpair ct)
    in
      maps get_for_term (get_all_terms tbl')
    end

(* Return the list of new wellform data (added under id prim or
   lower). Return as a list of (t, (id, th)).
 *)
fun get_new_wellform_data prim_id (tbl as {wellform, ...}) =
    wellform |> Termtab.dest
             |> maps (fn (t, vals) => map (pair t) (maps snd vals))
             |> filter (fn (_, (id, _)) => is_eq_ancestor tbl [prim_id] id)

(* Return the list of new properties, as a list of (id, th). *)
fun get_new_property prim_id (tbl as {property, ...}) =
    property |> Termtab.dest_list
             |> filter (fn (_, (id, _)) => is_eq_ancestor tbl [prim_id] id)

(* Use strings normally reserved for ty_str for convenience only. Does
   not indicate the original ty_str of the item.
 *)
fun classify_th thy th =
    if is_eq_term (prop_of' th) then "EQ"
    else if Property.is_property_const thy (prop_of' th) then "PROPERTY"
    else "PROP"

(* Helper function for the two functions below. *)
fun relevant_terms_single thy th =
    if classify_th thy th <> "EQ" then [] else
    let
      val (lhs, rhs) = cdest_eq (cprop_of' th)
    in
      [lhs, rhs]
    end

(* Add the given (id, th) pairs to the rewrite table. Consider three
   cases: where th is an equalitiy, a property, and an ordinary
   theorem.
 *)
fun add_infos infos (id, new_infos) tbl =
    if exists (fn th => not (is_Trueprop (Thm.prop_of th))) new_infos then
      raise Fail "add_info"
    else let
      val thy = theory_of tbl

      val relevant_terms =
          new_infos |> maps (relevant_terms_single thy)
                    |> get_reachable_terms true tbl
                    |> map Thm.term_of

      val relevant_props =
          filter (fn (_, th) => classify_th thy th = "PROP")
                 (map (pair id) new_infos) @
          filter (fn (_, th) => has_subterm relevant_terms (prop_of' th)) infos

      fun add_one_info th tbl =
          case classify_th thy th of
              "EQ" => add_rewrite (id, th) tbl
            | "PROPERTY" => add_property (id, th) tbl
            | _ => tbl
    in
      tbl |> fold add_one_info new_infos
          |> complete_wellform_data relevant_props
    end

(* Obtain the incremental rtype corresponding to the given (id, th)
   pairs. Consider three cases: when th is an equality, a property,
   and an ordinary theorem.
 *)
fun get_incr_type (tbl as {lat, ctxt, ...}) infos (id, new_infos) =
    if exists (fn th => not (is_Trueprop (Thm.prop_of th))) new_infos then
      raise Fail "get_incr_type"
    else let
      val thy = theory_of tbl

      val (prim_id, lat') = BoxID.add_prim_id [] lat

      val relevant_terms =
          new_infos |> maps (relevant_terms_single thy)
                    |> get_reachable_terms true tbl
                    |> map Thm.term_of

      val relevant_props =
          filter (fn (_, th) => classify_th thy th = "PROP")
                 (map (pair [prim_id]) new_infos) @
          filter (fn (_, th) => has_subterm relevant_terms (prop_of' th)) infos

      fun add_one_info th tbl =
          case classify_th thy th of
              "EQ" => add_rewrite ([prim_id], th) tbl
            | "PROPERTY" => add_property ([prim_id], th) tbl
            | _ => tbl

      val tbl' = tbl |> map_lat (K lat')
                     |> fold add_one_info new_infos
                     |> complete_wellform_data relevant_props

      val new_ts = (maps (relevant_terms_single thy) new_infos @
                    maps (Property.get_property_arg_th_gen o snd o snd)
                         (get_new_property prim_id tbl') @
                    map (cert ctxt o fst) (get_new_wellform_data prim_id tbl'))
                       |> distinct (op aconvc)
    in
      LAST (tbl', id, get_reachable_terms true tbl new_ts)
    end

fun filter_id_for_type rtype insts =
    case rtype of
        SINGLE _ => insts
      | LAST ({lat, ...}, _, _) =>
        let
          val prim = (BoxID.num_prim_id lat) - 1
        in
          filter (fn ((id, _), _) => member (op =) id prim) insts
        end

(* Keep only the last prim id and replace it with repl_id in rtype. *)
fun replace_id_for_type rtype insts =
    case rtype of
        SINGLE _ => insts
      | LAST (tbl as {lat, ...}, repl_id, _) =>
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

end  (* structure RewriteTable. *)
