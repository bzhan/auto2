(* Facility for dealing with equal terms. *)

(* Keeps list of "constants": terms to which rewriting rules are
   always directed.
 *)
structure RewConstData =
Theory_Data (
  type T = (term list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (op =)
)

fun add_rew_const t =
    case t of
        Const (nm, _) => RewConstData.map (Symtab.map_default (nm, []) (cons t))
      | _ => raise AUTO2 "add_rew_const: not a constant"

fun is_rew_const thy t =
    case t of
        Const (nm, _) =>
        let
          val tab = RewConstData.get thy
          fun typ_can_match t' =
              let val _ = typ_match thy (type_of t', type_of t) in true end
              handle Type.TYPE_MATCH => false
        in
          case Symtab.lookup tab nm of
              NONE => false
            | SOME ts => exists typ_can_match ts
        end
      | _ => false

fun is_rev_const_simp thy th =
    is_rew_const thy (lhs_of th) andalso not (is_rew_const thy (rhs_of th))

val string_of_box_id = BoxID.string_of_box_id
val string_of_box_ids = string_of_list string_of_box_id

type box_lattice = BoxID.box_lattice
type head_equiv = (box_id * thm) * term list list

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

signature REWRITE_TABLE =
sig
  type rewrite_table
  datatype rewrite_type = SINGLE of rewrite_table
                        | LAST of rewrite_table * box_id
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
  val reduce_equivs:
      rewrite_table -> term * head_equiv list -> term * head_equiv list
  val compute_head_equiv: rewrite_table -> term -> (term * head_equiv list) list
  val index_head_equiv: term -> rewrite_table -> rewrite_table
  val get_head_equiv: rewrite_table -> term -> (term * head_equiv list) list
  val get_head_equiv_with_t:
      rewrite_table -> box_id * term -> term -> head_equiv list
  val norm_ac_equiv: rewrite_table -> ac_inst_info -> head_equiv -> head_equiv

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
  val add_rewrite_thm: box_id -> thm -> rewrite_table -> rewrite_table
  val add_rewrite: box_id -> term * term -> rewrite_table -> rewrite_table

  val fo_rewrite_match_gen:
      bool -> rewrite_table -> term * term -> id_inst -> id_inst_th list
  val fo_rewrite_match:
      rewrite_table -> term * term -> id_inst -> id_inst_th list
  val fo_rewrite_match_head:
      rewrite_table -> term * term -> id_inst -> id_inst_th list
  val fo_rewrite_match_list: rewrite_table -> (bool * (term * term)) list ->
                             id_inst -> id_inst_ths list

  val append_rewrite: term * term -> rewrite_table -> rewrite_table
  val append_rewrite_thm: thm -> rewrite_table -> rewrite_table
  val replace_id_for_type:
      rewrite_type -> ((box_id * 'a) * 'b) list -> ((box_id * 'a) * 'b) list
  val replace_id_for_type':
      rewrite_type -> (box_id * 'a) list -> (box_id * 'a) list
  val get_new_terms: rewrite_table * rewrite_table -> (box_id * term) list
end;

structure RewriteTable : REWRITE_TABLE =
struct

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
  head_equiv: ((term * head_equiv list) list) Termtab.table,
  (* contain[A] is the list of terms for which A is a direct subterm. *)
  contain: (term list) Termtab.table,
  (* Rewrite info of a term. *)
  simp: ((box_id * thm) list) Termtab.table,
  (* Subterm rewrite info of a term. *)
  subsimp: ((box_id * thm) list) Termtab.table,
  (* Reverse of subsimp. Head rep of a term. *)
  reps: ((box_id * thm) list) Termtab.table,
  (* Current context. *)
  ctxt: Proof.context
}

datatype rewrite_type = SINGLE of rewrite_table
                      | LAST of rewrite_table * box_id
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
fun id_is_eq_ancestor tbl (i,_) (j,_) = is_eq_ancestor tbl i j

(*** Wrapper around functions in subterms. ***)
fun dest_subterms tbl skip_if = Subterms.dest_subterms (theory_of tbl) skip_if
fun list_subterms tbl skip_if = Subterms.list_subterms (theory_of tbl) skip_if
fun build_equiv {ctxt, ...} = Subterms.build_equiv ctxt
fun normalize_all_th (tbl as {ctxt, ...}) th =
    case Subterms.get_head_ac_info_with_inv (theory_of tbl) (rhs_of th) of
        NONE => th
      | SOME ac_info => apply_to_rhs (Subterms.normalize_all_ac ctxt ac_info) th

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
  reps = Termtab.empty, ctxt = ctxt}

fun map_lat f {lat, terms, equiv, all_equiv, head_equiv, contain, simp, subsimp,
               reps, ctxt} =
    let
      val lat' = f lat
      fun clean tb id_fun =
          tb |> Termtab.map
             (fn _ => filter (BoxID.is_box_supported lat' o id_fun))

      fun clean_head_equiv_1 (fhead, infos) =
          let
            val infos' = filter (BoxID.is_box_supported lat' o fst o fst) infos
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
       reps = clean reps fst, ctxt = ctxt}
    end

fun map_terms f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, ctxt} =
    {lat = lat, terms = f terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, ctxt = ctxt}
fun map_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                 subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = f equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, ctxt = ctxt}
fun map_all_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                     subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = f all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, ctxt = ctxt}
fun map_head_equiv f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                      subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = f head_equiv, contain = contain, simp = simp,
     subsimp = subsimp, reps = reps, ctxt = ctxt}
fun map_contain f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = f contain, simp = simp,
     subsimp = subsimp, reps = reps, ctxt = ctxt}
fun map_simp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = f simp,
     subsimp = subsimp, reps = reps, ctxt = ctxt}
fun map_subsimp f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp,
     subsimp = f subsimp, reps = reps, ctxt = ctxt}
fun map_reps f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = f reps, ctxt = ctxt}
fun map_context f {lat, terms, equiv, all_equiv, head_equiv, contain, simp,
                   subsimp, reps, ctxt} =
    {lat = lat, terms = terms, equiv = equiv, all_equiv = all_equiv,
     head_equiv = head_equiv, contain = contain, simp = simp, subsimp = subsimp,
     reps = reps, ctxt = f ctxt}

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

(*** Basic manipulation of equiv table. ***)

(* equiv_eq_better tbl info1 info2 means info2 is extraneous in the
   equiv table. The primed version compares trav first.
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
      if is_rev_const_simp (theory_of tbl) th then tbl else
      if exists (fn info => equiv_eq_better tbl info cur_info) equiv_t then
        tbl
      else
        tbl |> map_equiv (
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
fun get_subterm_rewrite_info tbl t =
    let
      val (t', subs) = dest_subterms tbl false t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (get_rewrite_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, build_equiv tbl equivs t'))
          |> map (apsnd (normalize_all_th tbl))
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
and subterm_simplify id tbl t =
    if in_table_raw tbl t then get_cached_subterm_rewrite id tbl t else
    let
      val (t', subs) = dest_subterms tbl false t
      val equivs = map (simplify id tbl) subs
    in
      build_equiv tbl equivs t' |> normalize_all_th tbl
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
and subterm_simplify_info tbl t =
    if in_table_raw tbl t then get_cached_subterm_rewrite_info tbl t else
    let
      val (t', subs) = dest_subterms tbl false t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (simplify_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, build_equiv tbl equivs t'))
          |> map (apsnd (normalize_all_th tbl))
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

(* Remove units, and combine terms on the rhs that are equiv to each
   other.
 *)
fun norm_ac_equiv tbl (ac_info as {unit_val, ...}) ((id, th), groups) =
    let
      val us = ACUtil.dest_ac ac_info (rhs_of th)
      fun equiv_to_rhs u' eq_th = is_equiv_th id tbl (u', rhs_of eq_th)

      (* Given list of normalizing equalities for previous terms, find
         the normalizing equality of the current term: if the current
         term is equivalent to unit, normalize to unit. Otherwise, if
         the current term is equivalent to the normalization of a
         previous term, normalize to the same term.
       *)
      fun norm_step u' prev_ths =
          case is_equiv_th id tbl (u', unit_val) of
              NONE => (case get_first (equiv_to_rhs u') prev_ths of
                           NONE => refl tbl u' :: prev_ths
                         | SOME eq_th => eq_th :: prev_ths)
            | SOME eq_th => eq_th :: prev_ths

      val norms = fold norm_step us [] |> rev
      val th' = norms |> ACUtil.comb_ac_equiv ac_info
                      |> apply_to_rhs (ACUtil.normalize_cu ac_info)

      (* Normalize all terms in groups. *)
      fun subst t = case find_first (fn norm => t aconv lhs_of norm) norms of
                        NONE => t | SOME norm => rhs_of norm
      val groups' = map (map subst) groups |> distinct (eq_set (op aconv))
    in
      ((id, transitive_list [th, th']), groups')
    end

(* infos is a list of (id, th), where the right side of each th is
   fhead as head.
 *)
fun reduce_equivs tbl (fhead, infos) =
    if length infos <= 1 then (fhead, infos) else
    let
      val thy = theory_of tbl
      val opt_ac = ACUtil.get_head_ac_info thy fhead

      fun args_of id u =
          case opt_ac of
              NONE => Term.strip_comb u |> snd |> map (simp_val id tbl)
            | SOME (ac_info as {unit_val, comm_th, ...}) =>
              (ACUtil.dest_ac ac_info u)
                  |> map (simp_val id tbl)
                  |> filter_out (fn u' => u' aconv unit_val)
                  |> (if is_true_th comm_th then I
                      else sort Term_Ord.fast_term_ord)

      fun head_equiv_eq_better ((id1, th1), _) ((id2, th2), _) =
          if not (is_eq_ancestor tbl id1 id2) then false
          else eq_list (op aconv) (args_of id2 (rhs_of th1),
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
fun compute_head_equiv (tbl as {lat, ctxt, ...}) u =
    let
      val _ = if Term.is_open u then
                raise AUTO2 "get_all_head_equivs: u is open" else ()
      val thy = theory_of tbl
      fun rep_eq_better (id1, th1) (id2, th2) =
          is_eq_ancestor tbl id1 id2 andalso
          is_equiv id2 tbl (rhs_of th1, rhs_of th2)
      fun get_all_equiv_under_id (id', th') =
          get_all_equiv tbl (rhs_of th') |> map (merge_info tbl (id', th'))

      (* First step: get all equivs from table. *)
      val all_equiv =
          if in_table_raw tbl u then get_all_equiv tbl u
          else (subterm_simplify_info tbl u)
                   |> maps (get_head_rep_with_id_th tbl)
                   |> max_partial rep_eq_better
                   |> maps get_all_equiv_under_id
                   |> cons ([], refl tbl u)

      (* Return all head equiv of u that is the given AC function
         applied on 0 or more than 2 terms.
       *)
      fun get_ac_head_equiv (ac_info as {unit_val, ...}) (id, u) =
          let
            fun agrees_or_unit u' =
                (ACUtil.head_agrees ac_info u' orelse u' aconv unit_val)
                andalso not (member (op aconv) (ACUtil.dest_ac ac_info u') u)

            val _ = assert (not (ACUtil.head_agrees ac_info u))
                           "get_ac_head_equiv: t head agrees with ac_info"
          in
            if in_table_raw tbl u then
              (get_all_equiv tbl u) |> filter (agrees_or_unit o rhs_of o snd)
                                    |> merge_box_with_info tbl id
            else []
          end

      (* When u is -u', get all head equiv of u' and take inverse. *)
      fun get_inv_ac_head_equiv (ac_info as {uinv_op, ...}) (id, u) =
          if Term.head_of u aconv uinv_op then
            let
              val u' = u |> Term.dest_comb |> snd
              val eq_ths = get_ac_head_equiv ac_info (id, u')
              fun process_eq_th eq_th =
                  eq_th |> Thm.combination (Thm.reflexive (cert ctxt uinv_op))
                        |> apply_to_rhs (ACUtil.normalize_minus ac_info)
            in
              map (apsnd process_eq_th) eq_ths
            end
          else []

      (* Expand AC equivs for a list of terms us. *)
      fun get_ac_head_equiv_list ac_info (id, us) =
          let
            fun get_equiv u =
                [(id, refl tbl u)] @ get_ac_head_equiv ac_info (id, u) @
                get_inv_ac_head_equiv ac_info (id, u)

            fun process_equiv_list (id, eq_ths) =
                let
                  val eq_th =
                      (ACUtil.comb_ac_equiv ac_info eq_ths)
                          |> apply_to_rhs (ACUtil.normalize_assoc ac_info)
                  val groups = (map rhs_of eq_ths)
                                   |> filter (ACUtil.head_agrees ac_info)
                                   |> map (ACUtil.dest_ac ac_info)
                in
                  norm_ac_equiv tbl ac_info ((id, eq_th), groups)
                end
          in
            us |> map get_equiv
               |> BoxID.get_all_merges_info lat
               |> map process_equiv_list
          end

      (* Second step: for those equivs that have AC functions as head,
         expand AC equivs for the arguments.
       *)
      fun process_equiv (id, th) =
          case ACUtil.get_head_ac_info thy (rhs_of th) of
              NONE => [((id, th), [])]
            | SOME (ac_info as {cfhead, ...}) =>
              (* Do not associate-expand conj and disj. *)
              if member (op aconv) [HOLogic.conj, HOLogic.disj]
                        (Thm.term_of cfhead) then [((id, th), [])]
              else let
                val us = ACUtil.dest_ac ac_info (rhs_of th)
                val us_equivs = get_ac_head_equiv_list ac_info (id, us)
                fun process_us_equiv ((id', th'), groups) =
                    ((id', transitive_list [th, th']), groups)
              in
                map process_us_equiv us_equivs
              end
    in
      (* Third step, sort by head of term, and reduce at each head. *)
      all_equiv |> maps process_equiv
                |> map (fn ((id, th), groups) =>
                           (get_head (rhs_of th), ((id, th), groups)))
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
      val thy = theory_of tbl
      val ac_info_opt = ACUtil.get_head_ac_info_with_inv thy t

      fun is_valid (uhead, infos) =
          if Term.is_Var t then infos
          else if Term.is_Var (get_head t) then infos
          else if Term.aconv_untyped (uhead, get_head t) then infos
          else if is_some ac_info_opt andalso
                  ACUtil.head_agrees (the ac_info_opt) uhead then infos
          else []
    in
      (get_head_equiv tbl u)
          |> maps is_valid
          |> map (apfst (apfst (fn id' => merge_boxes tbl (id, id'))))
    end

(*** Adding rewrite rules and maintain invariants of the table. ***)

(* Work out all consequences of updating simps in tbl. This includes
   updating simp of neighboring nodes, and updating simps / subsimps
   of nodes for which the current node is a subterm. inits is a list
   of simps to be added, with each element of form (id, t == t')
   updating simp of t.
 *)
fun process_update_simp inits tbl =
    let
      val eq_update = eq_pair (op =) (op aconv o apply2 Thm.prop_of)
      fun process_simp (id, th) (to_update, tbl) =
          if simp_less (th, get_rewrite id tbl (lhs_of th)) then
            (insert eq_update (id, th) to_update, update_simp (id, th) tbl)
          else
            (to_update, tbl)

      fun process_term t (to_update, tbl) =
          let
            val subsimps = get_subterm_rewrite_info tbl t
            val tbl' = fold update_subsimp subsimps tbl
          in
            fold process_simp subsimps (to_update, tbl')
          end

      fun update_step (to_update, tbl) =
          case to_update of
              [] => ([], tbl)
            | (id, th) :: rest =>
              let
                val t = lhs_of th
                fun process_neigh (id', th') =
                    merge_info tbl (id', meta_sym th') (id, th)
                val new_simp = map process_neigh (equiv_neighs tbl t)
              in
                (rest, tbl)
                    |> fold process_simp new_simp
                    |> fold process_term (immediate_contains tbl t)
                    |> update_step
              end
    in
      ([], tbl) |> fold process_simp inits |> update_step |> snd
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
      val t1_rinfo = get_rewrite_info tbl t1
      val t2_rinfo = get_rewrite_info tbl t2
      val t1_news = t2_rinfo |> map (merge_info tbl (id, th))
      val t2_news = t1_rinfo |> map (merge_info tbl (id, meta_sym th))
    in
      tbl |> add_equiv (id, th)
          |> process_update_simp (t1_news @ t2_news)
          |> fold index_all_equiv (get_reachable_terms false tbl [t1, t2])
    end

(* Add equiv edges so tbl is consistent. That is, any two nodes that
   have the same simp should be connected in the equiv graph. Also
   return the list of equiv edges added.
 *)
fun complete_table tbl =
    let
      val thy = theory_of tbl
      fun find_new_equiv t =
          let
            val equivs = get_all_equiv tbl t
            val rep_info = (get_subterm_rewrite_info tbl t)
                               |> maps (get_head_rep_with_id_th tbl)
                               |> reduce_equiv_info tbl
            val simp_info =
                (get_rewrite_info tbl t)
                    |> filter (fn (_, th) => is_rew_const thy (rhs_of th))
          in
            (rep_info @ simp_info)
                |> filter_out (has_equiv_eq_better tbl equivs)
                |> filter_out (fn (_, th) => is_rev_const_simp thy th)
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
    else
      let
        val imm_subtrms = list_subterms tbl true t
        val id_subs = map (pair id) imm_subtrms
        val tbl' = tbl |> fold add_term' id_subs |> add_term_raw (id, t)
        val simps = get_subterm_rewrite_info tbl' t
      in
        (* If t is already in table (just not at id), then we are
           done. Otherwise compute all indexed info for t.
         *)
        if in_table_raw tbl t then tbl'
        else
          tbl' |> fold (add_contain t) imm_subtrms
               |> fold update_simp simps
               |> fold update_subsimp simps
               |> index_all_equiv t
               |> index_head_equiv t
      end
fun add_term (id, t) tbl = tbl |> add_term' (id, t)
                               |> complete_table_with_edges []

(* First make sure t1 and t2 are in table. Add t1 == t2 to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_rewrite_thm id eq_th tbl =
    let
      val eq_prop = Thm.prop_of eq_th
      val (t1, t2) = eq_prop |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      val meta_eq = to_meta_eq eq_th
    in
      if is_equiv id tbl (t1, t2) then tbl
      else
        tbl |> add_term' (id, t1) |> add_term' (id, t2)
            |> add_rewrite_raw id meta_eq
            |> complete_table_with_edges [(id, meta_eq)]
    end

(* Same as add_rewrite_thm, but with trivial assumed theorem. *)
fun add_rewrite id (t1, t2) tbl =
    if is_equiv id tbl (t1, t2) then tbl
    else add_rewrite_thm id (assume_eq (theory_of tbl) (t1, t2)) tbl

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

(* Return a list of (id', env, th), which specifies matches of u (an
   ordinary term) with t (a term that may contain schematic
   variables), where id' is the minimum assumption for the match to
   hold, and th is t(env) == u.
 *)
fun fo_rewrite_match_gen at_head (tbl as {ctxt, ...}) (t, u) (id, env) =
    let
      val thy = theory_of tbl
      val _ = assert (not (has_vars u))
                     "fo_rewrite_match: u should not have schematic variables."

      (* Whether u contains any of the bd_vars. *)
      fun is_open bd_vars u =
          (inter (op aconv) bd_vars (map Free (Term.add_frees u []))) <> []

      (* Match type at the top level for t and u. If there is no
         match, return NONE. Otherwise, return the updated instsp as
         well as t instantiated with the new type.
       *)
      fun check_type_term (t, u) (id, (tyinst, inst)) =
          let
            val (T, U) = (fastype_of t, fastype_of u)
          in
            if T = U then SOME ((id, (tyinst, inst)), t) else
            let
              val tyinst' = Sign.typ_match thy (T, U) tyinst
              val t' = Envir.subst_term_types tyinst' t
            in
              SOME ((id, (tyinst', inst)), t')
            end
          end
          handle Type.TYPE_MATCH => NONE

      fun check_type (T, U) (id, (tyinst, inst)) =
          let
            val tyinst' = if T = U then tyinst
                          else Sign.typ_match thy (T, U) tyinst
          in
            SOME (id, (tyinst', inst))
          end
          handle Type.TYPE_MATCH => NONE

      (* Assign schematic variable with indexname ixn to u. Type of
         the schematic variable is determined by the type of u.
       *)
      fun update_inst bd_vars ixn u (id, (tyinsts, insts)) =
          if is_open bd_vars u then []
          else [((id, (update_env (ixn, u) (tyinsts, insts))), refl tbl u)]

      (* If t is of AC-form, return a list of t' where t' is formed by
         removing units, such that only one term in the AC-form
         remains (so t' has a different head).
       *)
      fun remove_unit_t t =
          case ACUtil.get_head_ac_info thy t of
              NONE => [t]
            | SOME (ac_info as {unit_val, ...}) =>
              let
                val targs = ACUtil.dest_ac ac_info t
              in
                if length targs = 2 then
                  if nth targs 0 aconv unit_val orelse
                     ACUtil.is_unit_allowed_var (nth targs 0) then
                    t :: remove_unit_t (nth targs 1)
                  else if nth targs 1 aconv unit_val orelse
                          ACUtil.is_unit_allowed_var (nth targs 1) then
                    t :: remove_unit_t (nth targs 0)
                  else [t]
                else [t]
              end

      (* Matching a list of terms. Return a list of ((id, env), ths),
         where ths are equalities from instantiations of ts using env
         to us.
       *)
      fun match_list_hd_first bd_vars instsp ((t, ts'), (u, us')) =
          let
            val insts_t = match bd_vars instsp (t, u)
            fun process_inst_t (instsp', th) =
                let
                  val insts_ts' = match_list bd_vars instsp' (ts', us')
                in
                  map (apsnd (cons th)) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end

      and match_list_tl_first bd_vars instsp ((t, ts'), (u, us')) =
          let
            val insts_ts' = match_list bd_vars instsp (ts', us')
            fun process_inst_ts' (instsp', ths) =
                let
                  val insts_t = match bd_vars instsp' (t, u)
                in
                  map (apsnd (fn th => th :: ths)) insts_t
                end
          in
            maps process_inst_ts' insts_ts'
          end

      and match_list _ instsp ([], []) = [(instsp, [])]
        | match_list bd_vars instsp (t::ts', u::us') =
          (match_list_hd_first bd_vars instsp ((t, ts'), (u, us'))
           handle AUTO2 "invalid pattern" =>
                  match_list_tl_first bd_vars instsp ((t, ts'), (u, us')))
        | match_list _ _ _ = []

      (* Match a (non-AC) function. *)
      and match_comb bd_vars (instsp as (_, (_, inst))) (t, u) =
          let
            val (tf, targs) = Term.strip_comb t
            val (uf, uargs) = Term.strip_comb u
          in
            if Term.aconv_untyped (tf, uf) then
              let
                val instsps' = match_list bd_vars instsp (targs, uargs)
                fun process_inst (instsp', ths) =
                    (instsp', comb_equiv (cert ctxt uf, ths))
              in
                map process_inst instsps'
              end
            else
              case tf of
                  Var (ixn, _) =>
                  (case Vartab.lookup inst ixn of
                       NONE =>
                       if subset (op aconv) (targs, bd_vars) andalso
                          not (has_duplicates (op aconv) targs) then
                         let
                           val u' = fold lambda_abstract (rev targs) u
                         in
                           map (fn (instsp', _) => (instsp', refl tbl u))
                               (update_inst bd_vars ixn u' instsp)
                         end
                       else
                         raise AUTO2 "invalid pattern"
                     | SOME (_, tf') =>
                       let
                         val t' = Term.list_comb (tf', targs) |> Envir.beta_norm
                       in
                         match bd_vars instsp (t', u)
                       end)
                | _ => []
          end

      (* Head must match explicitly. Schematic variables may appear in
         subterms of the left side. Here assume that u is normalized.
       *)
      and match_head bd_vars (instsp as (_, (_, inst))) (t, (u, groups)) =
          let
            val _ = assert (fastype_of t = fastype_of u) "match_head"
          in
            case (t, u) of
                (Var ((nm, i), _), _) =>
                (case Vartab.lookup inst (nm, i) of
                     NONE =>
                     if (nm = "NUMC" orelse nm = "NUMCu") andalso
                        not (is_numc u) then []
                     else if nm = "FREE" andalso not (Term.is_Free u) then []
                     else update_inst bd_vars (nm, i) u instsp
                   | SOME (_, u') =>
                     match_head bd_vars instsp (u', (u, groups)))
              | (Free (a, _), Free (b, _)) =>
                if a = b then [(instsp, refl tbl u)] else []
              | (Const (a, _), Const (b, _)) =>
                if a = b then [(instsp, refl tbl u)] else []
              | (_ $ _, _) =>
                (case ACUtil.get_head_ac_info_with_inv thy t of
                     NONE => match_comb bd_vars instsp (t, u)
                   | SOME ac_info =>
                     ACUtil.match_ac thy ac_info (match bd_vars) instsp
                                     (t, (u, groups)))
              | _ => []
          end

      (* No group information. Also first normalize u. *)
      and match_head' bd_vars instsp (t, u) =
          case ACUtil.get_head_ac_info_with_inv thy t of
              NONE => match_head bd_vars instsp (t, (u, []))
            | SOME ac_info =>
              let
                val ((_, norm_th), _) =
                    norm_ac_equiv tbl ac_info ((id, refl tbl u), [])
                val u' = rhs_of norm_th
                fun process_inst (instsp', th) =
                    (* th: t(env) == u', norm_th: u = u'. *)
                    (instsp', transitive_list [th, meta_sym norm_th])
              in
                map process_inst (match_head bd_vars instsp (t, (u', [])))
              end

      and match_all_head bd_vars (id, env) (t, u) =
          if is_open bd_vars u then match_head' bd_vars (id, env) (t, u)
          else let
            val all_t = remove_unit_t t
            val all_t' = case find_first Term.is_Var all_t of
                             NONE => all_t
                           | SOME v => [v]
            val u_equivs = maps (get_head_equiv_with_t tbl (id, u)) all_t'
            fun process_equiv ((id', th), groups) =
                let
                  val _ = assert (u aconv lhs_of th)
                                 "match_all_head: invalid th"
                  val u' = rhs_of th
                  val insts_u' = match_head bd_vars (id', env) (t, (u', groups))
                in
                  (* th': t(env) == u', and th: u == u'. *)
                  map (fn (inst', th') =>
                          (inst', transitive_list [th', meta_sym th])) insts_u'
                end
          in
            maps process_equiv u_equivs
          end

      (* Compare simp of t and u. Note we cannot guarantee that if
         there are no equivs then there are no matches betweeen t and
         u.
       *)
      and match_consts (id, env) (t, u) =
          if has_vars t orelse length (Term.add_tvars t []) > 0 then []
          else if t aconv u then [((id, env), refl tbl u)]
          else
            map (fn (id', th) => ((id', env), th)) (equiv_info tbl id (t, u))

      and match bd_vars (instsp as (_, (_, inst))) (t, u) =
          case check_type_term (t, u) instsp of
              NONE => []
            | SOME (instsp', t') =>
              let
                val inst_consts = match_consts instsp' (t', u)
              in
                if length inst_consts > 0 then inst_consts else
                case (t', u) of
                    (Var ((nm, i), _), _) =>
                    (case Vartab.lookup inst (nm, i) of
                         NONE =>
                         if member (op =) ["NUMC", "NUMCu", "FREE"] nm then
                           (* Special condition, match all rewritings. *)
                           match_all_head bd_vars instsp' (t', u)
                         else
                           update_inst bd_vars (nm, i) u instsp'
                       | SOME (_, u') => match bd_vars instsp' (u', u))
                  | (Abs (_, T, t'), Abs (nm, U, u')) =>
                    (case check_type (T, U) instsp' of
                         NONE => []
                       | SOME (instsp'' as (_, (tyinst', _))) =>
                         let
                           val bd_var =
                               (Variable.variant_frees ctxt bd_vars [(nm, U)])
                                   |> the_single |> Free
                           val t'' = Envir.subst_term_types tyinst' t'
                           val t_free = subst_bound (bd_var, t'')
                           val u_free = subst_bound (bd_var, u')
                           val insts' = match (bd_var :: bd_vars) instsp''
                                              (t_free, u_free)
                           fun process_inst (inst', th') =
                               (inst', Thm.abstract_rule
                                           nm (cert ctxt bd_var) th')
                         in
                           map process_inst insts'
                         end)
                  | (Free _, _) => []
                  | (Const _, _) => []
                  | _ =>  (* comb case. *)
                    match_all_head bd_vars instsp' (t', u)
              end
    in
      if at_head then
        case check_type_term (t, u) (id, env) of
            NONE => []
          | SOME ((id, env'), t') => match_head' [] (id, env') (t', u)
      else match [] (id, env) (t, u)
    end

val fo_rewrite_match = fo_rewrite_match_gen false
val fo_rewrite_match_head = fo_rewrite_match_gen true

(* Note similarity to match_list in fo_rewrite_match. *)
fun fo_rewrite_match_list tbl pairs instsp =
    case pairs of
        [] => [(instsp, [])]
      | (at_head, (t, u)) :: pairs' =>
        let
          val insts_t = fo_rewrite_match_gen at_head tbl (t, u) instsp
          fun process_inst_t (instsp', th) =
              let
                val insts_ts' = fo_rewrite_match_list tbl pairs' instsp'
              in
                map (apsnd (cons th)) insts_ts'
              end
        in
          maps process_inst_t insts_t
        end

(* Add rewrite rule t1 = t2 to tbl with new prim_id. *)
fun append_rewrite (t1, t2) (tbl as {lat, ...}) =
    let val (prim_id, lat') = BoxID.add_prim_id [] lat
    in tbl |> map_lat (K lat') |> add_rewrite [prim_id] (t1, t2) end

fun append_rewrite_thm eq_th (tbl as {lat, ...}) =
    let val (prim_id, lat') = BoxID.add_prim_id [] lat
    in tbl |> map_lat (K lat') |> add_rewrite_thm [prim_id] eq_th end

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

end  (* structure RewriteTable. *)

type rewrite_table = RewriteTable.rewrite_table
type rewrite_type = RewriteTable.rewrite_type

fun thm_order (th1, th2) = Term_Ord.term_ord (Thm.prop_of th1, Thm.prop_of th2)
fun thm_aconv (th1, th2) = Thm.prop_of th1 aconv Thm.prop_of th2
structure RewriteHeap =
Heap (
  type elem = box_id * thm
  val ord = prod_ord (list_ord int_ord) thm_order
);

(* A sub-program generating all rewrites of a given term. *)
signature REWRITE_ALL =
sig
  val rewrite_all: (box_id * thm) list -> term -> rewrite_table -> rewrite_table
end;

structure RewriteAll : REWRITE_ALL =
struct

open RewriteTable

(* Given an equality theorem A = B (with or without schematic
   variables), and a term C, produce all ways to apply the rewriting
   rule A -> B to get some C -> C'. Exclude those rules that are
   already in table. Produce instantiated version of th that justifies
   the equality.
 *)
fun rewrite_once (id, th) trm rtype =
    let
      val (lhs, rhs) =
          Thm.prop_of th |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      val tbl as {ctxt, ...} = table_of_rtype rtype
      val insts = (fo_rewrite_match_head tbl (lhs, trm) (id, fo_init))
                      |> replace_id_for_type rtype |> map fst
      fun process_inst tbl t (id', env) =
          let
            val rhs' = subst_term_norm env rhs
            val thy = theory_of tbl
          in
            if is_equiv id' tbl (t, rhs') then []
            else [(id', th |> subst_thm ctxt env
                           |> apply_to_thm (ACUtil.normalize_all_ac_full thy))]
          end
    in
      maps (process_inst tbl trm) insts
    end

fun rewrite_once_thms rrules trm rtype =
    maps (fn rule => rewrite_once rule trm rtype) rrules

fun init_rewrites rrules trm tbl =
    maps (fn t => rewrite_once_thms rrules t (SINGLE tbl))
         (Subterms.get_all_subterms (theory_of tbl) true trm)

fun rewrite_step rrules heap tbl =
    let
      val ((id, eq_th), heap') = RewriteHeap.min_elem heap
      val (lhs, rhs) =
          Thm.prop_of eq_th |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
    in
      if is_equiv id tbl (lhs, rhs) then (heap', tbl) else
      let
        val tbl' = add_rewrite_thm id eq_th tbl
        val tbl'' = append_rewrite_thm eq_th tbl
        val rtype = LAST (tbl'', id)
        val new_trms =
            get_new_terms (tbl, tbl') |> map snd |> distinct (op aconv)
        val updated_trms = get_reachable_terms true tbl [lhs, rhs]
        val revisit_trms =
            (get_all_terms tbl') |> filter (has_subterm updated_trms)
                                 |> subtract (op aconv) new_trms
        fun rewrite_init trm = rewrite_once_thms rrules trm (SINGLE tbl')
        fun rewrite_revisit trm = rewrite_once_thms rrules trm rtype
        val new_pairs =
            (maps rewrite_init new_trms @ maps rewrite_revisit revisit_trms)
                |> distinct (eq_pair (op =) thm_aconv)
      in
        (fold RewriteHeap.insert new_pairs heap', tbl')
      end
    end

fun rewrite_all rrules trm tbl =
    let
      val init_heap =
          RewriteHeap.empty
              |> fold RewriteHeap.insert (init_rewrites rrules trm tbl)
      fun loop heap tbl' =
          if RewriteHeap.is_empty heap then tbl'
          else let
            val (heap', tbl'') = rewrite_step rrules heap tbl'
          in
            loop heap' tbl''
          end
    in
      loop init_heap tbl
    end

end  (* structure RewriteAll. *)

(* Internal versions of first-order match without rewriting. *)
fun fo_table_match id tbl (t, u) =
    RewriteTable.fo_rewrite_match tbl (t, u) (id, fo_init)
fun fo_table_match_head id tbl (t, u) =
    RewriteTable.fo_rewrite_match_head tbl (t, u) (id, fo_init)
fun fo_table_match_list id tbl pairs =
    RewriteTable.fo_rewrite_match_list tbl pairs (id, fo_init)
