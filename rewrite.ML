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

type box_id = BoxID.box_id
val string_of_box_id = BoxID.string_of_box_id
val string_of_box_ids = string_of_list string_of_box_id

type box_lattice = BoxID.box_lattice
type id_inst = box_id * (Type.tyenv * Envir.tenv)
type id_inst_th = id_inst * thm
type id_inst_ths = id_inst * thm list

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
  val table_of_rewrite_type: rewrite_type -> rewrite_table
  val single_of_rewrite_type: rewrite_type -> rewrite_type

  (* Internal functions. Do not use except in unit test. *)
  val refl: rewrite_table -> term -> thm
  val add_equiv: box_id * thm -> bool -> rewrite_table -> rewrite_table
  val equiv_neighs: rewrite_table -> term -> (bool * (box_id * thm)) list
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
  val remove_unit: rewrite_table -> ac_item -> box_id -> conv
  val remove_unit_info: rewrite_table -> ac_item -> box_id * thm -> box_id * thm
  val reduce_equivs: rewrite_table -> (box_id * thm) list -> (box_id * thm) list
  val compute_head_equiv: rewrite_table -> term -> (box_id * thm) list
  val index_head_equiv: term -> rewrite_table -> rewrite_table
  val get_head_equiv: rewrite_table -> term -> (box_id * thm) list
  val get_head_equiv_with_t: rewrite_table -> term -> box_id * term ->
                             (box_id * thm) list
  val norm_ac_equiv: rewrite_table -> ac_item -> box_id -> term -> thm
  val norm_info: rewrite_table -> box_id * thm -> box_id * thm

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
  val is_subequiv: box_id -> rewrite_table -> term * term -> bool
  val equiv_info: rewrite_table -> box_id -> term * term -> (box_id * thm) list
  val subequiv_info:
      rewrite_table -> box_id -> term * term -> (box_id * thm) list
  val get_reachable_terms: bool -> rewrite_table -> term list -> term list
  val add_term: box_id * term -> rewrite_table -> rewrite_table
  val add_rewrite_thm: box_id -> thm -> rewrite_table -> rewrite_table
  val add_rewrite: box_id -> term * term -> rewrite_table -> rewrite_table
  val add_simp_rewrite: box_id -> term * term -> rewrite_table -> rewrite_table

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
  val get_new_terms: rewrite_table * rewrite_table -> (box_id * term) list
end;

structure RewriteTable : REWRITE_TABLE =
struct

type rewrite_table = {
  (* Specifies inheritance relations on primitive boxes. *)
  lat: BoxID.box_lattice,
  (* terms[t] is the list of ids at which t is present. *)
  terms: (box_id list) Termtab.table,
  (* equiv[a] is list of (trav, (id, th)), where trav indicates
     whether this edge is traversed for all_equiv and head_equiv, and
     where th is "a == a'" under id.
   *)
  equiv: ((bool * (box_id * thm)) list) Termtab.table,
  (* Index of reachability under equiv. *)
  all_equiv: ((box_id * thm) list) Termtab.table,
  (* Index of head equivs. *)
  head_equiv: ((box_id * thm) list) Termtab.table,
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
fun table_of_rewrite_type rtype = case rtype of SINGLE tbl => tbl
                                              | LAST (tbl, _) => tbl
fun single_of_rewrite_type rtype = case rtype of SINGLE tbl => SINGLE tbl
                                               | LAST (tbl, _) => SINGLE tbl

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
fun dest_subterms tbl = Subterms.dest_subterms (theory_of tbl)
fun list_subterms tbl = Subterms.list_subterms (theory_of tbl)
fun build_equiv {ctxt, ...} = Subterms.build_equiv ctxt
fun rearrange_subterms_th tbl th =
    case Subterms.get_head_ac_item (theory_of tbl) (rhs_of th) of
        NONE => th
      | SOME ac_itm =>
        th |> ACUtil.rearrange_assoc_rhs ac_itm
           |> apply_to_rhs (Subterms.rearrange_subterms (theory_of tbl) ac_itm)

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

fun print_equiv_val ctxt infos =
    print_infos ctxt (map snd (filter fst infos)) ^
    (if length (filter_out fst infos) = 0 then ""
     else " non_trav: " ^ (print_infos ctxt (map snd (filter_out fst infos))))

fun to_string {equiv, ctxt, ...} =
    to_string_table ctxt equiv (print_equiv_val ctxt)
fun to_string_full {terms, equiv, simp, subsimp, reps, ctxt, ...} =
    "Terms: " ^ (to_string_table ctxt terms string_of_box_ids) ^
    "\nequiv table:\n" ^ (to_string_table ctxt equiv (print_equiv_val ctxt)) ^
    "\nsimp table:\n" ^ (to_string_table ctxt simp (print_infos ctxt)) ^
    "\nsubsimp table:\n" ^ (to_string_table ctxt subsimp (print_infos ctxt)) ^
    "\nreps table:\n" ^ (to_string_table ctxt reps (print_infos ctxt))

(*** Certify using the current context. ***)
fun certify {ctxt, ...} t = cert ctxt t
fun refl tbl t = Thm.reflexive (certify tbl t)

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
    in
      {lat = lat', terms = clean terms I, equiv = clean equiv (fst o snd),
       all_equiv = clean all_equiv fst, head_equiv = clean head_equiv fst,
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
fun equiv_eq_better' tbl (trav, (id, th)) (trav', (id', th')) =
    if trav' andalso not trav then false
    else equiv_eq_better tbl (id, th) (id', th')

(* Remove extraneous ids for infos with equal terms. *)
fun reduce_equiv_info tbl info = max_partial (equiv_eq_better tbl) info

(* Add one way equivalence edge. Maintain the non-comparable property
   of the set of equivalence edges between any two nodes. cur_info is
   of form (trav, (id, t == t')).
 *)
fun add_equiv_raw (cur_info as (_, (_, th))) (tbl as {equiv, ...}) =
    let
      val t = lhs_of th
      val equiv_t = the_default [] (Termtab.lookup equiv t)
    in
      if is_rev_const_simp (theory_of tbl) th then tbl else
      if exists (fn info => equiv_eq_better' tbl info cur_info) equiv_t then
        tbl
      else
        tbl |> map_equiv (
          Termtab.update (
            t, equiv_t |> filter_out (equiv_eq_better' tbl cur_info)
                       |> cons cur_info))
    end

(* Add the given equivalence edge. *)
fun add_equiv (id, th) is_simp tbl =
    let
      val _ = assert (not (lhs_of th aconv rhs_of th)) "add_equiv: t == t'"
    in
      if is_simp then tbl |> add_equiv_raw (true, (id, th))
                          |> add_equiv_raw (false, (id, meta_sym th))
      else tbl |> add_equiv_raw (true, (id, th))
               |> add_equiv_raw (true, (id, meta_sym th))
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
      (* Each item in new / all is (use, (id, th)), where boolean use
         specifies whether the current node can be directly put into
         all_equiv.
       *)
      fun all_equiv_eq_better (use, (id, th)) (use', (id', th')) =
          equiv_eq_better tbl (id, th) (id', th') andalso
          not (use' andalso not use)
      fun has_all_equiv_eq_better infos info' =
          exists (fn info => all_equiv_eq_better info info') infos

      fun helper (new, all) =
          case new of
              [] => ([], all)
            | (_, (id, th)) :: rest =>
              let
                val t' = rhs_of th
                fun process_new (trav, (id', th')) =
                    (trav, merge_info tbl (id, th) (id', th'))
                val new' = (equiv_neighs tbl t')
                               |> map process_new
                               |> filter_out (has_all_equiv_eq_better all)
                val all' = new' @
                           (filter_out (has_all_equiv_eq_better new') all)
              in
                helper (rest @ new', all')
              end
      val init = (true, ([], refl tbl t))
    in
      snd (helper ([init], [init]))
          |> filter (fn (use, _) => use)
          |> map snd
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
      val (t', subs) = dest_subterms tbl t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (get_rewrite_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, build_equiv tbl equivs t'))
          |> map (apsnd (rearrange_subterms_th tbl))
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

(* Returns head representations of t under id, or under more
   restrictive assumptions. Not guaranteed to be non-redundant.
 *)
fun get_head_rep_with_id_th tbl (id, th) =
    get_head_rep_info tbl (rhs_of th) |> map (merge_info tbl (id, th))

(* Using the reps table for subterm simplification. *)
fun get_cached_subterm_rewrite_info {subsimp, ...} t =
    case Termtab.lookup subsimp t of
        NONE => []
      | SOME infos => infos

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
      val (t', subs) = dest_subterms tbl t
      val equivs = map (simplify id tbl) subs
    in
      build_equiv tbl equivs t' |> rearrange_subterms_th tbl
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
      val (t', subs) = dest_subterms tbl t
    in
      if length subs = 0 then [([], refl tbl t)] else
      (map (simplify_info tbl) subs)
          |> merge_simp_infos tbl
          |> map (fn (id, equivs) => (id, build_equiv tbl equivs t'))
          |> map (apsnd (rearrange_subterms_th tbl))
          |> reduce_simp_info tbl
    end

(* Exported equivalence function. *)
fun is_equiv id tbl (t1, t2) =
    if t1 aconv t2 then true else simp_val id tbl t1 aconv simp_val id tbl t2

fun is_subequiv id tbl (t1, t2) =
    if t1 aconv t2 then true
    else (rhs_of (subterm_simplify id tbl t1))
             aconv (rhs_of (subterm_simplify id tbl t2))

fun remove_unit tbl (ac_itm as {unit_val, ...}) id cu =
    let
      val u = Thm.term_of cu
      val us = ACUtil.dest_ac ac_itm u
      fun get_simp u' =
          let
            val simp_th = simplify id tbl u'
          in
            if rhs_of simp_th aconv unit_val then simp_th
            else refl tbl u'
          end
      val simps = map get_simp us
    in
      if exists (fn th => rhs_of th aconv unit_val) simps then
        simps |> ACUtil.comb_ac_equiv (theory_of tbl) ac_itm
              |> ACUtil.rearrange_subterms_rhs ac_itm
      else
        Thm.reflexive cu
    end

fun remove_unit_info tbl ac_itm (id, th) =
    (id, th |> apply_to_rhs (remove_unit tbl ac_itm id))

(* Combine terms on the rhs that are equiv to each other. *)
fun norm_ac_equiv tbl (ac_itm as {unit_val, ...}) id u =
    let
      val us = ACUtil.dest_ac ac_itm u
      val simp_ths = map (simplify id tbl) us
    in
      if length us = 1 then refl tbl u else
      if forall Thm.is_reflexive simp_ths then
        ACUtil.rearrange_subterms_rhs ac_itm (refl tbl u) else
      let
        (* prev_ths is a list of pairs (norm_th', simp_th'). *)
        fun norm_step simp_th prev_ths =
            let
              val simp = rhs_of simp_th
            in
              if (not (ACUtil.head_agrees ac_itm simp) andalso
                  in_table_raw tbl simp) orelse simp aconv unit_val
              then (simp_th, simp_th) :: prev_ths else
              let
                val u' = lhs_of simp_th
                fun is_equiv (_, simp_th') = (rhs_of simp_th') aconv simp
              in
                case find_first is_equiv prev_ths of
                    NONE => (refl tbl u', simp_th) :: prev_ths
                  | SOME (norm_th', simp_th') =>
                    if (rhs_of norm_th') aconv u' then
                      (refl tbl u', simp_th) :: prev_ths
                    else
                      (* norm_th': u1 -> u2, simp_th': u1 -> simp,
                         simp_th: u' -> simp. Need: u' -> u2.
                       *)
                      (transitive_list [simp_th, meta_sym simp_th',
                                        norm_th'], simp_th) :: prev_ths
              end
            end
        val norms = fold norm_step simp_ths [] |> rev |> map fst
      in
        norms |> ACUtil.comb_ac_equiv (theory_of tbl) ac_itm
              |> ACUtil.rearrange_subterms_rhs ac_itm
      end
    end

fun norm_info tbl (id, th) =
    case ACUtil.get_head_ac_item (theory_of tbl) (rhs_of th) of
        NONE => (id, th)
      | SOME ac_itm => let val th' = norm_ac_equiv tbl ac_itm id (rhs_of th)
                       in (id, transitive_list [th, th']) end

(* equivs is a list of (id, th). *)
fun reduce_equivs tbl equivs =
    let
      val thy = theory_of tbl
      val equiv_by_head =
          equivs |> map (fn (id, th) => (get_head (rhs_of th), (id, th)))
                 |> AList.group (op aconv)

      fun make_cache f ids (id, th) =
          let
            val u = rhs_of th
            val _ = assert (f aconv get_head u) "make_cache: wrong head"
            val opt_ac = ACUtil.get_head_ac_item thy u
            val args = case opt_ac of
                           NONE => Term.strip_comb u |> snd
                         | SOME ac_itm => ACUtil.dest_ac ac_itm u
            fun get_simp_args id' =
                case opt_ac of
                    NONE => map (rhs_of o simplify id' tbl) args
                  | SOME {unit_val, ...} =>
                    map (rhs_of o simplify id' tbl) args
                        |> filter_out (fn u' => u' aconv unit_val)
                        |> sort Term_Ord.fast_term_ord
            (* AList mapping id' to simp_args. *)
            val cache = ids |> filter (is_eq_ancestor tbl id)
                            |> map (fn id' => (id', get_simp_args id'))
          in
            ((id, th), cache)
          end

      fun lookup cache id' =
          the (AList.lookup (eq_list (op =)) cache id')
          handle Option.Option =>
                 raise AUTO2 "reduce_equivs: id not found in cache."

      fun cached_eq_better ((id, _), cache) ((id', _), cache') =
          is_eq_descendent tbl id' id andalso
          eq_list (op aconv) (lookup cache id', lookup cache' id')

      fun reduce_group (f, infos) =
          let
            val ids = map fst infos |> distinct (op =)
            val cached_infos = map (make_cache f ids) infos
          in
            max_partial cached_eq_better cached_infos |> map fst
          end
    in
      maps reduce_group equiv_by_head
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
      fun get_ac_head_equiv ac_itm (id, u) =
          let
            fun is_ac (ac_itm as {unit_val, ...}) u =
                ACUtil.head_agrees ac_itm u orelse u aconv unit_val
            val _ = assert (not (ACUtil.head_agrees ac_itm u))
                           "get_ac_head_equiv: t head agrees with ac_itm"
          in
            if in_table_raw tbl u then
              (get_all_equiv tbl u) |> filter (is_ac ac_itm o rhs_of o snd)
                                    |> merge_box_with_info tbl id
                                    |> reduce_equivs tbl
            else []
          end

      (* Expand AC equivs for a list of terms us. *)
      fun get_ac_head_equiv_list (ac_itm as {assoc_r, ...}) (id, us) =
          let
            (* Same order of assoc_r = true, reverse if assoc_r = false. *)
            fun step us =
                case us of
                    [] => raise AUTO2 "get_ac_head_equiv_list: empty list"
                  | [u] => (id, refl tbl u) :: get_ac_head_equiv ac_itm (id, u)
                  | u :: us' =>
                    let
                      val u_equivs =
                          (id, refl tbl u) :: get_ac_head_equiv ac_itm (id, u)
                      fun merge (id, th) (id', th') =
                          (merge_boxes tbl (id, id'),
                           (if assoc_r then [th, th'] else [th', th])
                               |> ACUtil.comb_ac_equiv thy ac_itm
                               |> ACUtil.rearrange_assoc_rhs ac_itm)
                      val expand_rest = step us'
                    in
                      maps (fn u_equiv =>
                               map (merge u_equiv) expand_rest) u_equivs
                           |> map (remove_unit_info tbl ac_itm)
                           |> reduce_equivs tbl
                    end
          in
            step (if assoc_r then us else rev us)
          end

      (* Second step: for those equivs that have AC functions as head,
         expand AC equivs for the arguments.
       *)
      fun process_equiv (id, th) =
          case ACUtil.get_head_ac_item thy (rhs_of th) of
              NONE => [(id, th)]
            | SOME (ac_itm as {fhead, ...}) =>
              (* Do not associate-expand conj and disj. *)
              if fhead aconv HOLogic.conj orelse fhead aconv HOLogic.disj then
                [(id, th)] else
              let
                val us = ACUtil.dest_ac ac_itm (rhs_of th)
                val us_equivs = get_ac_head_equiv_list ac_itm (id, us)
                fun process_us_equiv (id', th') =
                    (id', transitive_list [th, th'])
              in
                map process_us_equiv us_equivs
              end
    in
      (* Finally, reduce by comparing the list of arguments, ordered
         for non-AC functions and unordered for AC functions.
       *)
      all_equiv |> maps process_equiv
                |> reduce_equivs tbl
                |> map (norm_info tbl)
    end

fun index_head_equiv t tbl =
    tbl |> map_head_equiv (Termtab.update (t, compute_head_equiv tbl t))

fun get_head_equiv (tbl as {head_equiv, ...}) u =
    case Termtab.lookup head_equiv u of
        NONE => compute_head_equiv tbl u
      | SOME info => info

fun get_head_equiv_with_t tbl t (id, u) =
    let
      fun is_valid (_, th) =
          case t of
              Var _ => true
            | _ => Term.aconv_untyped (get_head (rhs_of th), get_head t)
    in
      (get_head_equiv tbl u)
          |> filter is_valid
          |> merge_box_with_info tbl id
          |> reduce_equivs tbl
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
                fun process_neigh (_, (id', th')) =
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
                                 |> map (fn (_, (_, th)) => rhs_of th)
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
fun add_rewrite_raw id th is_simp tbl =
    let
      val (t1, t2) = (lhs_of th, rhs_of th)
      val t1_rinfo = get_rewrite_info tbl t1
      val t2_rinfo = get_rewrite_info tbl t2
      val t1_news = t2_rinfo |> map (merge_info tbl (id, th))
      val t2_news = t1_rinfo |> map (merge_info tbl (id, meta_sym th))
    in
      tbl |> add_equiv (id, th) is_simp
          |> process_update_simp (t1_news @ t2_news)
          |> fold index_all_equiv (get_reachable_terms false tbl [t1, t2])
    end

(* Add equiv edges so tbl is consistent. That is, any two nodes that
   have the same simp should be connected in the simp graph. Also
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
             simplification.
           *)
          let
            val tbl' = tbl |> add_rewrite_raw id th false
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
        val imm_subtrms = list_subterms tbl t
        val id_subs = map (pair id) imm_subtrms
        val tbl' = tbl |> fold add_term' id_subs |> add_term_raw (id, t)
        val simps = get_subterm_rewrite_info tbl' t
      in
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
      val is_simp = if is_eq_term' eq_prop then false
                    else if is_simp_eq_term' eq_prop then true
                    else raise AUTO2 "add_rewrite_thm: not obj equality"
      val (t1, t2) = eq_prop |> HOLogic.dest_Trueprop |> dest_all_eq
      val meta_eq = if is_simp then to_meta_eq (from_simp_eq eq_th)
                    else to_meta_eq eq_th
    in
      if is_equiv id tbl (t1, t2) then tbl
      else
        tbl |> add_term' (id, t1) |> add_term' (id, t2)
            |> add_rewrite_raw id meta_eq is_simp
            |> complete_table_with_edges [(id, meta_eq)]
    end

(* Same as add_rewrite_thm, but with trivial assumed theorem. *)
fun add_rewrite id (t1, t2) tbl =
    if is_equiv id tbl (t1, t2) then tbl
    else add_rewrite_thm id (assume_eq (theory_of tbl) (t1, t2)) tbl

fun add_simp_rewrite id (t1, t2) tbl =
    if is_equiv id tbl (t1, t2) then tbl
    else add_rewrite_thm id (assume_simp_eq (theory_of tbl) (t1, t2)) tbl

(* If id1 is an eq_descendent of id2, both u1s and u2s have length
   greater than 1, such that u2s = c @ [v], u1s = c @ vs, and v ~
   f(vs) under id, then vs is marked as a group. It should not be
   matched under a single uninstantiated schematic variable. Note:
   currently weak version for efficiency.
 *)
fun detect_groups tbl (ac_itm as {unit_val, ...}) (id1, u1) (id2, u2) =
    if not (is_eq_descendent tbl id1 id2) then [] else
    let
      val u1s = ACUtil.dest_ac ac_itm u1
      val u2s = ACUtil.dest_ac ac_itm u2
    in
      if length u1s > length u2s andalso length u2s > 1 then
        let
          fun remove_eqs (u1s, u2s) =
              case u2s of
                  [] => (u1s, [])
                | u' :: us' =>
                  if member (op aconv) u1s u' then
                    remove_eqs (remove1 (op aconv) u' u1s, us')
                  else
                    apsnd (cons u') (remove_eqs (u1s, us'))
          val (u1s', u2s') = remove_eqs (u1s, u2s)
          val list_ac = ACUtil.list_ac ac_itm
        in
          case length u2s' of
              0 => if is_equiv id1 tbl (unit_val, list_ac u1s') then [u1s'] else
                   let
                     fun get_for u2' =
                         if is_equiv id1 tbl (u2', list_ac (u2' :: u1s')) then
                           [u2' :: u1s'] else []
                   in
                     maps get_for u2s
                   end
            | 1 => if is_equiv id1 tbl (the_single u2s', list_ac u1s')
                   then [u1s'] else []
            | _ => []
        end
      else []
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
      fun find_t1_untyped (id2, th2) =
          if Term.aconv_untyped (t1, rhs_of th2) then
            [(id2, meta_sym th2)]
          else []
    in
      (maps (fn s1 => maps (compare s1) simp2) simp1 @
       maps find_t1_untyped simp2)
          |> merge_box_with_info tbl id
          |> max_partial (id_is_eq_ancestor tbl)
    end

(* Return list of ids that are descendents of id at which t1 and t2
   are subterm equiv.
 *)
fun subequiv_info tbl id (t1, t2) =
    let
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
   hold, and th is (meta)-equality from the instantiation of t using
   env to u.
 *)
fun fo_rewrite_match_gen at_head (tbl as {ctxt, ...}) (t, u) (id, env) =
    let
      val thy = theory_of tbl
      val cert = certify tbl
      val _ = assert (not (has_vars u))
                     "fo_rewrite_match: u should not have schematic variables."

      (* Whether a term comes from an open term in u - test by
         checking whether any of the free bd_vars appears in u.
       *)
      fun is_open bd_vars u =
          (inter (op aconv) (map snd bd_vars)
                 (map Free (Term.add_frees u []))) <> []

      (* Check whether the given term is an uninstantiated schematic
         variable.
       *)
      fun is_uninst_var insts t =
          case t of
              Var (ixn, T) =>
              (case Envir.lookup1 insts (ixn, T) of
                   NONE => true | SOME _ => false)
            | _ => false

      (* If t is instantiated schematic, replace with concrete term. *)
      fun to_concrete bd_vars insts t =
          case t of
              Var (ixn, T) =>
              (case Envir.lookup1 insts (ixn, T) of
                   NONE => t | SOME u' => subst_atomic bd_vars u')
            | _ => t

      fun check_type (T, U) (id', (tyinsts,insts)) =
          [(id', (Sign.typ_match thy (T, U) tyinsts, insts))]
          handle Type.TYPE_MATCH => []

      (* aconv_untyped (t, u) = true. Match type and return u == u. *)
      fun check_type_th (t, u) instsp =
          map (rpair (refl tbl u))
              (check_type (fastype_of t, fastype_of u) instsp)

      (* Assign Var (ixn, T) to u. *)
      fun update_inst bd_vars (ixn,T) u (id', (tyinsts,insts)) =
          let
            val u_var = subst_atomic (map swap bd_vars) u
          in
            [((id', (Sign.typ_match thy (T, fastype_of u_var) tyinsts,
                     Vartab.update_new (ixn, (T, u_var)) insts)), refl tbl u)]
            handle Type.TYPE_MATCH => []
          end

      (* Return a list of (id', t') where t' is formed by removing
         units at id', and has a different head from t.
       *)
      fun remove_unit_t bd_vars insts id (t, U) =
          case ACUtil.get_typed_head_ac_item thy t U of
              NONE => []
            | SOME (ac_itm as {unit_val, ...}) =>
              let
                val targs = ACUtil.dest_ac ac_itm t
                fun simp_ids t' =
                    if Term.aconv_untyped (t', unit_val) then [[]] else
                    if is_TVar (fastype_of t') then []
                    else (simplify_info tbl t')
                             |> filter (fn (_, th) => rhs_of th aconv unit_val)
                             |> merge_box_with_info tbl id
                             |> map fst |> max_partial (is_eq_ancestor tbl)
                val arg_simp_ids =
                    map (simp_ids o to_concrete bd_vars insts) targs
                fun process_i i =
                    let
                      val merged =
                          (get_all_merges tbl (nth_drop i arg_simp_ids))
                              |> max_partial (is_eq_ancestor tbl)
                    in
                      map (rpair (nth targs i)) merged
                    end
                fun res_eq_better (id1, t1) (id2, t2) =
                    is_eq_ancestor tbl id1 id2 andalso
                    get_head t1 aconv get_head t2
              in
                maps process_i (0 upto (length targs - 1))
                     |> max_partial res_eq_better
              end

      (* Matching a list of terms. Return a list of (id, env, ths),
         where ths are equalities from instantiations of ts using env
         to us.
       *)
      fun match_list _ instsp ([], []) = [(instsp, [])]
        | match_list bd_vars instsp (t::ts', u::us') =
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
        | match_list _ _ _ = []

      (* Match a (non-AC) function. *)
      and match_comb bd_vars instsp (t, u) =
          let
            val (tf, targs) = Term.strip_comb t
            val (uf, uargs) = Term.strip_comb u
          in
            if Term.aconv_untyped (tf, uf) then
              let
                val instsps' = match_list bd_vars instsp (targs, uargs)
                fun process_inst (instsp', ths) =
                    (instsp', comb_equiv (cert uf, ths))
              in
                map process_inst instsps'
              end
            else []
          end

      (* Match two lists up to permutation. Return a list of ((id,
         env), ths) with the following property: ths are equalities
         from instantiated ts to a list us', such that after dest_ac
         the lists us' and us are permutations of each other.
       *)
      and match_multiset _ instsp _ _ ([], []) = [(instsp, [])]
        | match_multiset bd_vars (instsp as (id,(_,insts)))
                         (ac_itm as {unit_val, ...}) groups (t::ts', us) =
          let
            val range = 0 upto (length us - 1)

            (* Match with unit and consume no term in us. *)
            fun match_unit (instsp', th) =
                map (apsnd (cons th))
                    (match_multiset bd_vars instsp' ac_itm groups
                                    (ts', us))

            (* Match with and consume exactly one term in us. *)
            fun match_i i =
                if i > 0 andalso (nth us (i-1)) aconv (nth us i) then [] else
                let
                  val insts_t = match bd_vars instsp (t, nth us i)
                  fun process_inst_t (instsp', th) =
                      map (apsnd (cons th))
                          (match_multiset bd_vars instsp' ac_itm groups
                                          (ts', nth_drop i us))
                in
                  maps process_inst_t insts_t
                end

            (* Match ts' first, then match t. Used when t is an
               uninstantiated schematic variable, and there are
               concrete terms left in ts'.
             *)
            fun swap_last _ =
                map (apsnd (split_last #> swap #> uncurry cons))
                    (match_multiset bd_vars instsp ac_itm groups
                                    (ts' @ [t], us))

            (* Match with a subset of us. Only for uninstantiated
               schematic variables. Currently restrict to non-empty
               subsets.
             *)
            fun match_subset is =
                if length is = 0 then [] else
                let
                  val _ = assert (is_uninst_var insts t)
                                 "match_subset: t should be uninstantiated."
                  val cur_group = map (nth us) is
                in
                  if exists (fn grp => submultiset (op aconv) (grp, cur_group))
                            groups then [] else
                  let
                    val fi = ACUtil.list_ac ac_itm cur_group
                    val insts_t = match bd_vars instsp (t, fi)
                    fun process_inst_t (instsp', th) =
                        map (apsnd (cons th))
                            (match_multiset bd_vars instsp' ac_itm groups
                                            (ts', nth_drop_list is us))
                  in
                    maps process_inst_t insts_t
                  end
                end
          in
            case t of
                Var(ixn, T) =>
                (case Envir.lookup1 insts (ixn, T) of
                     NONE =>
                     if forall (is_uninst_var insts) ts' then
                       (* The remaining ones are all uninstantiated
                          schematic variables.
                        *)
                       if length ts' = 0 then
                         match_subset range
                       else if (#1 ixn) = "NUMC" orelse (#1 ixn) = "FREE" then
                         maps match_i range
                       else
                         maps match_subset (subsets range)
                     else
                       swap_last ()
                   | SOME u' =>
                     (* Deal with instantiated variables as in match. *)
                     let
                       val us' = u' |> subst_atomic bd_vars
                                    |> ACUtil.dest_ac ac_itm
                       val len_us' = length us'
                       val insts = match_multiset bd_vars instsp ac_itm groups
                                                  (us' @ ts', us)
                       fun process_inst (instsp', ths) =
                           let
                             val (th_us', th_rest) = chop len_us' ths
                             val th_u' = ACUtil.comb_ac_equiv thy ac_itm th_us'
                           in
                             (instsp', th_u' :: th_rest)
                           end
                     in
                       map process_inst insts
                     end)
              | _ =>
                (* If t is concrete, check whether t is equiv to unit. *)
                if has_vars t then maps match_i range
                else if Term.aconv_untyped (t, unit_val) then
                  maps match_unit (check_type_th (t, unit_val) instsp)
                else if not (is_TVar (fastype_of t)) andalso
                        simp_val id tbl t aconv unit_val then
                  match_unit (instsp, simplify id tbl t)
                else
                  maps match_i range
          end
        | match_multiset _ _ _ _ _ = []

      (* Match an AC function *)
      and match_ac_comb
              bd_vars ac_itm (instsp as (id,(_,insts))) (t, u) all_infos =
          let
            val targs = ACUtil.dest_ac ac_itm t
            val uargs = ACUtil.dest_ac ac_itm u
            val has_inst_var = exists (is_uninst_var insts) targs
            val groups = if has_inst_var then
                           maps (detect_groups tbl ac_itm (id, u)) all_infos
                                |> distinct (eq_list (op aconv))
                         else []
            val instsps' =
                match_multiset bd_vars instsp ac_itm groups (targs, uargs)
            fun process_inst (instsp', ths') =
                let
                  val th' = ths' |> ACUtil.comb_ac_equiv thy ac_itm
                                 |> ACUtil.rearrange_assoc_rhs ac_itm
                                 |> ACUtil.rearrange_subterms_rhs ac_itm
                  val _ = assert (rhs_of th' aconv u)
                                 "match_ac_comb: u must be in normalized"
                in
                  (instsp', th')
                end
          in
            map process_inst instsps'
          end

      (* Head must match explicitly. Schematic variables may appear in
         subterms of the left side.
       *)
      and match_head bd_vars (instsp as (id, (_,insts))) (t, u) all_infos =
          case (t, u) of
              (Var(ixn,T), _) =>
              (case Envir.lookup1 insts (ixn, T) of
                   NONE =>
                   if (#1 ixn) = "NUMC" andalso not (is_numc u) then [] else
                   if (#1 ixn) = "FREE" andalso not (Term.is_Free u) then []
                   else update_inst bd_vars (ixn,T) u instsp
                 | SOME u' => match_head bd_vars instsp
                                         (subst_atomic bd_vars u', u) all_infos)
            | (Free (a,_), Free (b,_)) =>
              if a = b then check_type_th (t, u) instsp else []
            | (Const (a,_), Const (b,_)) =>
              if a = b then check_type_th (t, u) instsp else []
            | (_ $ _, _) =>
              (case check_type (fastype_of t, fastype_of u) instsp of
                   [] => []
                 | [instsp'] =>
                   (case ACUtil.get_typed_head_ac_item thy t (fastype_of u) of
                        NONE => match_comb bd_vars instsp' (t, u)
                      | SOME ac_itm =>
                        let
                          val norm_th = norm_ac_equiv tbl ac_itm id u
                          val u' = rhs_of norm_th
                          fun process_inst (instsp'', th) =
                              (* th: t(env) == u', norm_th: u = u'. *)
                              (instsp'', transitive_list [th, meta_sym norm_th])
                        in
                          map process_inst
                              (match_ac_comb bd_vars ac_itm instsp' (t, u')
                                             all_infos)
                        end)
                 | _ => raise AUTO2 "check_type")
            | _ => []

      and match_all_head bd_vars (id, (env as (_, insts))) (t, u) =
          if is_open bd_vars u then match_head bd_vars (id, env) (t, u) [] else
          let
            val remove_unit_info =
                remove_unit_t bd_vars insts id (t, fastype_of u)
            fun get_u_equivs (id', t') = get_head_equiv_with_t tbl t' (id', u)
            val u_equivs =
                if exists (fn (id', _) => id' = id) remove_unit_info then
                  maps get_u_equivs remove_unit_info
                else
                  let
                    val equivs_on_t = get_u_equivs (id, t)
                  in
                    if length equivs_on_t = 0 then
                      maps get_u_equivs remove_unit_info
                    else equivs_on_t
                  end
            val infos = map (apsnd rhs_of) u_equivs
            fun process_equiv (id', th) =
                let
                  val _ = assert (u aconv lhs_of th)
                                 "match_all_head: invalid th"
                  val u' = rhs_of th
                  val insts_u' = match_head bd_vars (id', env) (t, u') infos
                in
                  (* th': t(env) == u', and th: u == u'. *)
                  map (fn (inst', th') =>
                          (inst', transitive_list [th', meta_sym th])) insts_u'
                end
          in
            maps process_equiv u_equivs
          end

      (* When t has no schematic variables (may have schematic type
         variables), try to directly find equiv with u. Note we cannot
         guarantee that if there are no equivs then there are no
         matches betweeen t and u.
       *)
      and match_consts (id, env) (t, u) =
          if has_vars t then [] else
          let
            val insts' = check_type (fastype_of t, fastype_of u) (id, env)
          in
            if length insts' = 0 then []
            else
              let
                val (_, env' as (tyinsts', _)) = the_single insts'
                val t' = Envir.subst_term_types tyinsts' t
              in
                map (fn (id', th) => ((id', env'), th))
                    (equiv_info tbl id (t', u))
              end
          end

      and match bd_vars (instsp as (_, (_,insts))) (t, u) =
          let
            val inst_consts = match_consts instsp (t, u)
          in
            if length inst_consts > 0 then inst_consts else
            case (t, u) of
                (Var(ixn,T), _) =>
                (case Envir.lookup1 insts (ixn, T) of
                     NONE => if (#1 ixn) = "NUMC" orelse (#1 ixn) = "FREE" then
                               (* Special condition, match all rewritings. *)
                               match_all_head bd_vars instsp (t, u)
                             else
                               update_inst bd_vars (ixn,T) u instsp
                   | SOME u' =>
                     match bd_vars instsp (subst_atomic bd_vars u', u))
              | (Abs(_,T,t'), Abs(nm,U,u')) =>
                let
                  val bd_var = Var ((Name.internal nm, length bd_vars), U)
                  val bd_free = Variable.variant_frees
                                    ctxt (map snd bd_vars) [(nm, U)]
                                    |> the_single |> Free
                  val t_free = subst_bound (bd_free, t')
                  val u_free = subst_bound (bd_free, u')
                  val insts' =
                      maps (fn (id', env') =>
                               match ((bd_var, bd_free) :: bd_vars) (id', env')
                                     (t_free, u_free))
                           (check_type (T, U) instsp)
                  fun process_inst (inst', th') =
                      (inst', Thm.abstract_rule nm (cert bd_free) th')
                in
                  map process_inst insts'
                end
              | (Free _, _) => []
              | (Const _, _) => []
              | _ =>  (* comb case. *)
                match_all_head bd_vars instsp (t, u)
          end
    in
      if at_head then match_head [] (id, env) (t, u) []
      else match [] (id, env) (t, u)
    end

val fo_rewrite_match = fo_rewrite_match_gen false
val fo_rewrite_match_head = fo_rewrite_match_gen true

(* Note similarity to match_list in fo_rewrite_match. *)
fun fo_rewrite_match_list (tbl as {ctxt, ...}) pairs instsp =
    let
      (* t: a = b with type bool, u is a term to head-match with a and
         then match with b.
       *)
      fun match_eq (t, u) pairs' =
          let
            val (lhs, rhs) = HOLogic.dest_eq t
            val insts_t = fo_rewrite_match_list
                              tbl [(true, (lhs, u)), (false, (rhs, u))] instsp
            fun process_inst_t (instsp', ths) =
                let
                  (* th1: lhs(env) == u, ths2: rhs(env) == u. *)
                  val (th1, th2) = the_pair ths
                  val th = to_obj_eq (transitive_list [th1, meta_sym th2])
                  (* th': (lhs(env) == rhs(env)) == TERM u. *)
                  val th' = make_eq_term_triv ctxt (th, u)
                  val insts_ts' = fo_rewrite_match_list tbl pairs' instsp'
                in
                  map (apsnd (cons th')) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end

      fun match at_head (t, u) th_f pairs' =
          let
            val insts_t = fo_rewrite_match_gen at_head tbl (t, u) instsp
            fun process_inst_t (instsp', th) =
                let
                  val th' = th_f th
                  val insts_ts' = fo_rewrite_match_list tbl pairs' instsp'
                in
                  map (apsnd (cons th')) insts_ts'
                end
          in
            maps process_inst_t insts_t
          end
    in
      case pairs of
          [] => [(instsp, [])]
        | (at_head, (t, u)) :: pairs' =>
          case t of
              Const (@{const_name Trueprop}, _) $ t' =>
              if is_eq_term t' then
                if not (is_Term u) then []
                else match_eq (t', Logic.dest_term u) pairs'
              else  (* usual case for t. *)
                if is_Trueprop u then
                  match at_head (t', HOLogic.dest_Trueprop u) make_trueprop_eq
                        pairs'
                else []
            | Const ("Pure.term", _) $ t' =>
              if is_Term u then
                match true (t', Logic.dest_term u) make_term_eq pairs'
              else []
            | _ => match at_head (t, u) I pairs'
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
  val rewrite_all: (box_id * thm) list -> term ->
                   RewriteTable.rewrite_table -> RewriteTable.rewrite_table
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
      val tbl as {ctxt, ...} = table_of_rewrite_type rtype
      val insts = (fo_rewrite_match_head tbl (lhs, trm) (id, fo_init))
                      |> replace_id_for_type rtype |> map fst
      fun process_inst tbl t (id', env) =
          let
            val rhs' = Envir.subst_term env rhs
          in
            if is_equiv id' tbl (t, rhs') then []
            else [(id', th |> subst_thm ctxt env
                           |> ACUtil.rearrange_ac_thm (theory_of tbl))]
          end
    in
      maps (process_inst tbl trm) insts
    end

fun rewrite_once_thms rrules trm rtype =
    maps (fn rule => rewrite_once rule trm rtype) rrules

fun init_rewrites rrules trm tbl =
    maps (fn t => rewrite_once_thms rrules t (SINGLE tbl))
         (Subterms.get_all_subterms (theory_of tbl) trm)

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
fun fo_table_match_list id tbl pairs =
    RewriteTable.fo_rewrite_match_list tbl pairs (id, fo_init)

(* Get list of ids where t1 and t2 are equiv. *)
fun equiv_ids id tbl (t1, t2) =
    RewriteTable.equiv_info tbl id (t1, t2) |> map fst

(* Get list of ids where t1 and t2 are subterm equiv. *)
fun subequiv_ids id tbl (t1, t2) =
    RewriteTable.subequiv_info tbl id (t1, t2) |> map fst
