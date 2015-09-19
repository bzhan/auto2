(* Definition of core proof steps (single-step change to proof
   state). Each proofstep is a function taking the index of the
   current box, known facts to consider (either in the current box or
   an ancestor box), and conclusion in the current box, and returns a
   list of updates to the proof status.
 *)
signature PROOFSTEP =
sig
  type proofstep_fn
  type proofstep
  type prfstep_filter
  datatype prfstep_descriptor = WithItem of term
                              | GetFact of term * thm
                              | GetShadow of int
                              | CreateCase of term list * term list
                              | Filter of prfstep_filter
  val WithFact: term -> prfstep_descriptor
  val WithGoal: term -> prfstep_descriptor
  val WithTerm: term -> prfstep_descriptor
  val string_of_desc: theory -> prfstep_descriptor -> string
  val string_of_descs: theory -> prfstep_descriptor list -> string
  val get_prfstep_fn: proofstep -> proofstep_fn
  val merged_id: rewrite_type -> box_item list -> box_id
  val apply_matchers: rewrite_table -> match_fn list -> term list ->
                      box_item list -> id_inst -> id_inst_ths list
  val get_insts_filt: match_fn list -> term list -> box_item list ->
                      rewrite_type -> prfstep_filter -> id_inst_ths list
  val get_insts: match_fn list -> term list -> box_item list -> rewrite_type ->
                 id_inst_ths list

  (* prfstep_filter *)
  val all_insts: prfstep_filter
  val id_filter: (box_id -> bool) -> prfstep_filter
  val neqt_filter: string -> term -> prfstep_filter
  val neqp_filter: string -> term -> prfstep_filter
  val not_numc_filter: string -> prfstep_filter
  val neq_filter: string -> string -> prfstep_filter
  val order_filter: string -> string -> prfstep_filter
  val order_filter_n: indexname -> indexname -> prfstep_filter
  val size1_filter: string -> prfstep_filter
  val not_type_filter: string -> typ -> prfstep_filter
  val unique_free_filter: string -> prfstep_filter
  val canonical_split_filter: string -> string -> string -> prfstep_filter
  val ac_atomic_filter: string -> string -> prfstep_filter
  val subset_var_filter: string -> string -> prfstep_filter

  (* First level proofstep writing functions. *)
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_pats: prfstep_descriptor list -> term list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> (term list * term list) list
  val retrieve_shadows: prfstep_descriptor list -> int list
  val gen_prfstep: theory -> string -> prfstep_descriptor list -> proofstep
  val prfstep_conv:
      theory -> string -> prfstep_descriptor list -> conv -> proofstep
  val prfstep_two_stage:
      theory -> string -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_custom:
      theory -> string -> prfstep_descriptor list -> Update.update_type list ->
      (id_inst_ths -> status -> Update.raw_update list) -> proofstep
  val prfstep_thm_fn:
      theory -> string -> prfstep_descriptor list -> Update.update_type list ->
      (Proof.context -> id_inst_ths -> thm) -> proofstep
end;

structure ProofStep : PROOFSTEP =
struct

open Box
open Update
open Status

type proofstep_fn = box_item list -> rewrite_type -> status -> raw_update list
type proofstep = {name: string, filt: pre_filter list,
                  res_types: update_type list, func: proofstep_fn}
type prfstep_filter = rewrite_table -> id_inst -> bool
datatype prfstep_descriptor = WithItem of term
                            | GetFact of term * thm
                            | GetShadow of int
                            | CreateCase of term list * term list
                            | Filter of prfstep_filter

fun WithFact t = WithItem (HOLogic.mk_Trueprop t)
fun WithGoal t = WithFact (get_neg t)
fun WithTerm t =
    let
      val _ = assert (type_of t <> @{typ prop})
                     "WithTerm: t should not be of type prop."
    in
      WithItem t
    end

fun string_of_desc thy desc =
    let
      val print = str o pretty_term_thy thy
    in
      case desc of
          WithItem t =>
          if fastype_of t = @{typ prop} then
            if is_Trueprop t andalso is_neg (HOLogic.dest_Trueprop t) then
              "WithGoal " ^ (print (get_neg' t))
            else
              "WithFact " ^ (print t)
          else
            "WithTerm " ^ (print t)
        | GetFact (t, th) =>
          if t aconv @{term False} then
            "GetResolve " ^ (name_of_thm th)
          else if is_neg t then
            "GetGoal (" ^ (print (get_neg t)) ^ ", " ^ (name_of_thm th) ^ ")"
          else
            "GetFact (" ^ (print t) ^ ", " ^ (name_of_thm th) ^ ")"
        | GetShadow n => if n = 1 then "Shadow first" else "Shadow second"
        | CreateCase (assums, concls) =>
          "CreateCase " ^ (string_of_list print assums) ^ ", " ^
          (string_of_list print concls)
        | Filter _ => "Filter (...)"
    end

fun string_of_descs thy descs =
    let
      fun is_filter desc = case desc of Filter _ => true | _ => false
      val (filts, non_filts) = filter_split is_filter descs
    in
      (cat_lines (map (string_of_desc thy) non_filts)) ^
      (if length filts > 0 then
         (" + " ^ (string_of_int (length filts)) ^ " filters") else "")
    end

fun get_prfstep_fn {func, ...} = func

fun merged_id rtype items =
    let
      val {lat, ...} = RewriteTable.table_of_rtype rtype
      fun merge items =
          case items of
              [] => []
            | {id, ...} :: items' => BoxID.merge_boxes lat (id, merge items')
    in
      merge items
    end

(* Apply the given matchers in sequence. *)
fun apply_matchers tbl matchers pats items (id, inst) =
    case matchers of
        [] => [((id, inst), [])]
      | matcher :: rest =>
        let
          val pat' = hd pats |> subst_term_norm inst
          val inst_th' = matcher pat' (hd items) tbl (id, inst)
          fun process_inst_th (inst', th) =
              let
                val insts_rest =
                    apply_matchers tbl rest (tl pats) (tl items) inst'
                fun append_th (inst'', ths) =
                    if pointer_eq (th, true_th) then (inst'', ths)
                    else (inst'', th :: ths)
              in
                map append_th insts_rest
              end
        in
          maps process_inst_th inst_th'
        end

(* Get ordered matchings between "pats" and "trms". *)
fun get_insts_filt matchers pats items rtype filt =
    if length pats <> length items then
      raise AUTO2 "get_insts_filt: wrong number of arguments"
    else let
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rtype rtype
    in
      (apply_matchers tbl matchers pats items (id, fo_init))
          |> filter (filt tbl o fst)
          |> RewriteTable.replace_id_for_type rtype
    end

fun get_insts matchers pats items rtype =
    get_insts_filt matchers pats items rtype (fn _ => fn _ => true)

(* prfstep_filter *)

val all_insts = fn _ => fn _ => true
fun id_filter f _ (id, _) = f id
fun neqt_filter s1 t2 tbl (id, inst) =
    not (RewriteTable.is_equiv id tbl (lookup_inst inst s1, t2))
fun neqp_filter s1 p2 tbl (id, inst) =
    (fo_table_match id tbl (subst_term_norm inst p2, lookup_inst inst s1))
        |> filter (fn ((id', _), _) => id = id')
        |> length |> equal 0
fun not_numc_filter s tbl (id, inst) =
    (fo_table_match id tbl (@{term_pat "?NUMC"}, lookup_inst inst s))
        |> filter (fn ((id', _), _) => id = id')
        |> length |> equal 0
fun neq_filter s1 s2 tbl (id, inst) =
    neqt_filter s1 (lookup_inst inst s2) tbl (id, inst)
fun order_filter s1 s2 _ (_, inst) =
    not (Term_Ord.termless (lookup_inst inst s2, lookup_inst inst s1))
fun order_filter_n idx1 idx2 _ (_, inst) =
    not (Term_Ord.termless (lookup_instn inst idx2, lookup_instn inst idx1))
fun size1_filter s1 tbl (id, inst) =
    size_of_term (RewriteTable.simp_val id tbl (lookup_inst inst s1)) = 1
fun not_type_filter s ty _ (_, inst) =
    not (Term.fastype_of (lookup_inst inst s) = ty)
fun unique_free_filter s tbl (_, inst) =
    let
      val s_val = lookup_inst inst s
    in
      if not (is_Free s_val) then false else
      let
        fun is_same_type_free t =
            is_Free t andalso fastype_of t = fastype_of s_val
        val same_type_frees =
            filter is_same_type_free (RewriteTable.get_all_terms tbl)
      in
        length same_type_frees = 1
      end
    end

fun canonical_split_filter fnm s1 s2 tbl (_, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "canonical_split_filter: ac_itm not found"
      | SOME ac_itm =>
        let
          val (A, B) = (lookup_inst inst s1, lookup_inst inst s2)
        in
          not (ACUtil.head_agrees ac_itm A) andalso
          forall (fn B => not (Term_Ord.termless (B, A)))
                 (ACUtil.dest_ac ac_itm B)
        end
fun ac_atomic_filter fnm s tbl (_, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "ac_atomic_filter: ac_itm not found"
      | SOME ac_itm => not (ACUtil.head_agrees ac_itm (lookup_inst inst s))
fun subset_var_filter s1 s2 _ (_, inst) =
    subset (op aconv) (map Var (Term.add_vars (lookup_inst inst s1) []),
                       map Var (Term.add_vars (lookup_inst inst s2) []))

(* First level proofstep writing functions. *)
fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val inst_new = subst_term_norm inst pat_r
      val th' = th |> subst_thm ctxt inst |> fold Thm.elim_implies ths
      val _ = if inst_new aconv (Thm.prop_of th') then () else
              raise AUTO2CT ("apply_pat_r: conclusion mismatch",
                             map (cert ctxt) [inst_new, Thm.prop_of th'])
    in
      th'
    end

fun retrieve_pats descs =
    maps (fn desc => case desc of WithItem t => [t] | _ => []) descs

fun retrieve_pats_r descs =
    maps (fn desc => case desc of GetFact (pat_r, th) =>
                                  [(HOLogic.mk_Trueprop pat_r, th)]
                                | _ => []) descs

fun retrieve_filts descs =
    let
      fun retrieve_filt desc =
          case desc of Filter filt => [filt] | _ => []
    in
      fold (curry (op andf2)) (maps retrieve_filt descs) all_insts
    end

fun retrieve_cases descs =
    let
      fun retrieve_case desc =
          case desc of CreateCase (assums, concls) =>
                       [(map HOLogic.mk_Trueprop assums,
                         map HOLogic.mk_Trueprop concls)]
                     | _ => []
    in
      maps retrieve_case descs
    end

fun retrieve_shadows descs =
    let
      fun retrieve_shadow desc =
          case desc of GetShadow n => [n] | _ => []
    in
      maps retrieve_shadow descs
    end

(* Create a proofstep from a list of proofstep descriptors. See
   datatype prfstep_descriptor for allowed types of descriptors.
 *)
fun gen_prfstep thy name descs =
    let
      val pats = retrieve_pats descs
      val pats_r = retrieve_pats_r descs
      val filt = retrieve_filts descs
      val cases = retrieve_cases descs
      val shadows = retrieve_shadows descs

      (* Verify that all schematic variables appearing in pats_r /
         cases appear in pats.
       *)
      val vars = map Var (fold Term.add_vars pats [])
      fun check_pat_r (pat_r, _) =
          subset (op aconv) (map Var (Term.add_vars pat_r []), vars)
      fun check_case (assums, concls) =
          subset (op aconv)
                 (map Var (fold Term.add_vars (assums @ concls) []), vars)
      val _ = assert (forall check_pat_r pats_r andalso forall check_case cases)
                     "gen_prfstep: new schematic variable in pats_r / cases."

      fun pats_r_to_update ctxt (inst_ths as ((id, _), _)) =
          let
            val ths = map (apply_pat_r ctxt inst_ths) pats_r
          in
            if length ths = 1 then thm_update thy (id, the_single ths)
            else AddItems {id = id, raw_items = map (thm_to_ritem thy) ths}
          end

      fun pat_updts ctxt insts =
          if length pats_r = 0 then [] else map (pats_r_to_update ctxt) insts

      fun case_to_update ((id, inst), _) (assums, concls) =
          AddBoxes {id = id, vars = [],
                    assums = map (subst_term_norm inst) assums,
                    concls = map (subst_term_norm inst) concls,
                    cb = null_callback}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases
      fun case_updts insts = maps cases_to_update insts

      fun shadow_to_update items ((id, _), _) n =
          if n = 1 then ShadowItem {id = id, item = nth items 0}
          else ShadowItem {id = id, item = nth items 1}
      fun shadows_to_update items inst =
          map (shadow_to_update items inst) shadows
      fun shadow_updts items insts = maps (shadows_to_update items) insts

      val res_types =
          (if exists (fn (t, _) => t aconv prop_False) pats_r then
             [RESOLVE_BOX] else []) @
          (if exists (fn (t, _) => not (t aconv prop_False)) pats_r then
             [ADD_ITEMS] else []) @
          (if length cases > 0 then [ADD_BOXES] else []) @
          (if length shadows > 0 then [SHADOW_ITEM] else [])

      val matcher_infos = map (ItemIO_Data.find_th_matcher thy) pats
      val matchers = map snd matcher_infos

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt matchers pats items rtype filt
          in
            pat_updts ctxt insts @ case_updts insts @ shadow_updts items insts
          end
    in
      {name = name, filt = map fst matcher_infos, res_types = res_types,
       func = prfstep}
    end

fun prfstep_conv thy name descs cv =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1 andalso
                      fastype_of (the_single pats) <> @{typ prop})
                     "prfstep_conv: should have exactly one term pattern."
      val filt = retrieve_filts descs
      val t = the_single pats
      val matcher_infos = map (ItemIO_Data.find_th_matcher thy) pats
      val matchers = map snd matcher_infos

      fun prfstep items rtype {ctxt, ...} =
          let
            val tbl = RewriteTable.table_of_rtype rtype
            val insts = get_insts_filt matchers pats items rtype filt
            fun inst_to_updt ((id, inst), _) =
                let
                  val ct = (subst_term_norm inst t) |> cert ctxt
                  val eq_th = (Conv.try_conv cv) ct
                  val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
                in
                  if lhs aconv rhs then
                    raise AUTO2CT (name ^ ": cv failed.", [ct])
                  else if RewriteTable.is_equiv id tbl (lhs, rhs) then []
                  else [thm_update thy (id, to_obj_eq eq_th)]
                end
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map fst matcher_infos, res_types = [ADD_ITEMS],
       func = prfstep}
    end

(* pat_r produces a trivial statement, which together with the item
   matching the main pattern are matched with the hypotheses of th2 to
   produce the final result.
 *)
fun prfstep_two_stage thy name descs th2 =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1)
                     "prfstep_two_stage: should have one pattern."
      val pats_r = retrieve_pats_r descs
      val _ = assert (length pats_r = 1)
                     "prfstep_two_stage: should have one result."
      val pat_r = the_single pats_r
      val filt = retrieve_filts descs

      val res_type = if Thm.nprems_of th2 = 2 andalso
                        Thm.concl_of th2 aconv prop_False then RESOLVE_BOX
                     else ADD_ITEMS
      val matcher_infos = map (ItemIO_Data.find_th_matcher thy) pats
      val matchers = map snd matcher_infos

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt matchers pats items rtype filt
            fun inst_to_updt (instsp as (id, _), ths) =
                let
                  val th = apply_pat_r ctxt (instsp, []) pat_r
                in
                  thm_update thy (id, (ths @ [th]) MRS th2)
                end
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map fst matcher_infos, res_types = [res_type],
       func = prfstep}
    end

fun prfstep_custom thy name descs res_types updt_fn =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      val matcher_infos = map (ItemIO_Data.find_th_matcher thy) pats
      val matchers = map snd matcher_infos

      fun prfstep items rtype st =
          let
            val insts = get_insts_filt matchers pats items rtype filt
            fun inst_to_updt inst_th = updt_fn inst_th st
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map fst matcher_infos, res_types = res_types,
       func = prfstep}
    end

fun prfstep_thm_fn thy name descs res_types thm_fn =
    prfstep_custom
        thy name descs res_types
        (fn ((id, inst), ths) => fn {ctxt, ...} =>
            [thm_update thy (id, thm_fn ctxt ((id, inst), ths))])

end  (* structure ProofStep *)

open ProofStep

(* Table of proofsteps, categorized by type. *)
datatype proofstep_table
  = ProofStepTable of {prfsteps: proofstep list, fixed_sc: int Symtab.table}

structure ProofStepData =
Theory_Data (
  type T = proofstep_table;
  val empty = ProofStepTable {prfsteps = [], fixed_sc = Symtab.empty};
  val extend = I;
  fun merge (ProofStepTable {prfsteps = l1, fixed_sc = sc1},
             ProofStepTable {prfsteps = l2, fixed_sc = sc2}) =
      ProofStepTable {prfsteps = Library.merge pointer_eq (l1, l2),
                      fixed_sc = Symtab.merge (op =) (sc1, sc2)}
)

signature PROOFSTEP_DATA =
sig
  val add_prfstep: proofstep -> theory -> theory
  val del_prfstep: string -> theory -> theory
  val del_prfstep_thm: thm -> theory -> theory
  val add_fixed_sc: string * int -> theory -> theory
  val get_prfsteps: theory -> proofstep list
  val get_fixed_sc: theory -> string -> int option

  val add_gen_prfstep: string * prfstep_descriptor list -> theory -> theory
  val add_prfstep_conv:
      string * prfstep_descriptor list * conv -> theory -> theory
  val add_prfstep_two_stage:
      string * prfstep_descriptor list * thm -> theory -> theory
  val add_prfstep_thm_fn:
      string * prfstep_descriptor list * Update.update_type list *
      (Proof.context -> id_inst_ths -> thm) -> theory -> theory

  (* Constructing conditional prfstep_descriptors. *)
  type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor
  val with_term: string -> pre_prfstep_descriptor
  val with_cond: string -> pre_prfstep_descriptor
  val with_conds: string list -> pre_prfstep_descriptor list
  val with_filt: prfstep_filter -> pre_prfstep_descriptor
  val with_filts: prfstep_filter list -> pre_prfstep_descriptor list
  val process_conds:
      thm -> theory -> pre_prfstep_descriptor list -> prfstep_descriptor list

  (* Second level proofstep writing functions. *)
  val add_and_print_prfstep:
      string -> prfstep_descriptor list -> theory -> theory
  val add_forward_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward1_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward2_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_resolve_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_known_fact: thm -> theory -> theory
  val add_forward_prfstep: thm -> theory -> theory
  val add_backward_prfstep: thm -> theory -> theory
  val add_backward1_prfstep: thm -> theory -> theory
  val add_backward2_prfstep: thm -> theory -> theory
  val add_resolve_prfstep: thm -> theory -> theory

  val add_rewrite_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
end;

structure ProofStep_Data : PROOFSTEP_DATA =
struct

fun add_prfstep (prfstep as {filt, ...}) =
    if length filt >= 1 andalso length filt <= 2 then
      ProofStepData.map (
        fn ProofStepTable {prfsteps, fixed_sc} =>
           ProofStepTable {prfsteps = prfstep :: prfsteps, fixed_sc = fixed_sc})
    else
      raise AUTO2 "add_proofstep: need 1 or 2 patterns."

(* Deleting a proofstep. For string inputs, try adding theory
   name. For theorem inputs, try all @-suffixes.
 *)
fun del_prfstep_pred pred = ProofStepData.map (
      fn ProofStepTable {prfsteps, fixed_sc} =>
         let
           val steps = prfsteps |> filter (pred o #name)
         in
           if length steps = 0 then raise AUTO2 "del_prfstep: not found" else
           let
             val _ = map (fn step => tracing ("Delete " ^ (#name step))) steps
           in
             ProofStepTable {
               prfsteps = prfsteps |> filter_out (pred o #name),
               fixed_sc = fixed_sc |> fold Symtab.delete_safe (map #name steps)}
           end
         end)

fun del_prfstep nm thy =
    if exists_string (equal ".") nm then del_prfstep_pred (equal nm) thy
    else del_prfstep_pred (equal nm orf equal
                                 ((Context.theory_name thy) ^ "." ^ nm)) thy

(* Delete all proofsteps for a given theorem. *)
fun del_prfstep_thm th =
    let val nm = name_of_thm th in
      del_prfstep_pred (equal nm orf is_prefix_str (nm ^ "@"))
    end

fun add_fixed_sc (nm, sc) = ProofStepData.map (
      fn ProofStepTable {prfsteps, fixed_sc} =>
         case find_first (equal nm o #name) prfsteps of
             NONE => raise AUTO2 ("add_fixed_sc: not found " ^ nm)
           | _ => ProofStepTable {
                   prfsteps = prfsteps,
                   fixed_sc = fixed_sc |> Symtab.update_new (nm, sc)})

fun get_prfsteps thy =
    let
      val ProofStepTable {prfsteps, ...} = ProofStepData.get thy
    in prfsteps end

fun get_fixed_sc thy nm =
    let val ProofStepTable {fixed_sc, ...} = ProofStepData.get thy in
      Symtab.lookup fixed_sc nm
    end

fun add_gen_prfstep (name, descs) thy =
    add_prfstep (gen_prfstep thy name descs) thy
fun add_prfstep_conv (name, descs, cv) thy =
    add_prfstep (prfstep_conv thy name descs cv) thy
fun add_prfstep_two_stage (name, descs, th2) thy =
    add_prfstep (prfstep_two_stage thy name descs th2) thy
fun add_prfstep_thm_fn (name, descs, res_types, thm_fn) thy =
    add_prfstep (prfstep_thm_fn thy name descs res_types thm_fn) thy

(* Constructing conditional prfstep_descriptors. *)

type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor

fun with_term str ctxt =
    let
      val t = Proof_Context.read_term_pattern ctxt str
      val _ = assert (length (Term.add_frees t []) = 0)
                     "with_term: should not contain free variable."
    in
      WithTerm t
    end

fun with_cond str ctxt =
    let
      val cond = Proof_Context.read_term_pattern ctxt str
      val (lhs, rhs) = cond |> HOLogic.dest_not |> HOLogic.dest_eq
                       handle TERM _ =>
                              raise AUTO2 "with_cond: not an inequality."
      val _ = assert (is_Var lhs) "with_cond: left side should be a variable."
      val ((nm, idx), _) = dest_Var lhs
      val _ = assert (idx = 0) "with_cond: cannot handle nonzero index."
      val _ = assert (length (Term.add_frees rhs []) = 0)
                     "with_cond: should not contain free variable."
    in
      if is_Var rhs then
        let
          val ((nm', idx'), _) = dest_Var rhs
          val _ = assert (idx' = 0) "with_cond: cannot handle nonzero index."
        in
          Filter (neq_filter nm nm')
        end
      else
        Filter (neqp_filter nm rhs)
    end
fun with_conds strs = map with_cond strs

fun with_filt filt = K (Filter filt)
fun with_filts filts = map with_filt filts

fun process_conds th thy conds =
    let
      val ctxt = (Proof_Context.init_global thy)
                     |> Variable.declare_term (Thm.prop_of th)
    in
      map (fn cond => cond ctxt) conds
    end

(* Second level proofstep writing functions. *)

fun add_and_print_prfstep nm descs thy =
    let val _ = writeln (nm ^ "\n" ^ (string_of_descs thy descs))
    in add_gen_prfstep (nm, descs) thy end

fun add_forward_prfstep_cond th conds thy =
    let
      (* Obtain list of WithTerm conditions. The total number of
         WithTerm conditions and fact/goal conditions must be at most
         two.
       *)
      val ctxt = Proof_Context.init_global thy
      val term_conds = maps (
            fn cond => case cond ctxt of WithItem t => [t] | _ => []) conds
      val _ = assert (length term_conds <= 2)
                     "More than two WithTerm conditions"

      (* First, convert to obj imp any extraneous meta imps. *)
      val max_fact_conds = 2 - length term_conds
      val th' = if Thm.nprems_of th > max_fact_conds then
                  th |> apply_to_thm (to_obj_conv_skip_n ctxt max_fact_conds)
                     |> Thm.put_name_hint (name_of_thm th ^ "@short")
                else th

      val (assums, concl) = strip_horn' th'
      val descs = (process_conds th' thy conds) @
                  (map WithFact assums @ [GetFact (concl, th')])
    in
      add_and_print_prfstep (name_of_thm th') descs thy
    end

fun add_backward_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward_th th) conds thy

fun add_backward1_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward1_th th) conds thy

fun add_backward2_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward2_th th) conds thy

fun add_resolve_prfstep_cond th conds thy =
    add_forward_prfstep_cond (to_contra_th th) conds thy

fun add_known_fact th =
    add_forward_prfstep_cond
        th [K (WithTerm (th |> Thm.concl_of |> HOLogic.dest_Trueprop))]
fun add_forward_prfstep th = add_forward_prfstep_cond th []
fun add_backward_prfstep th = add_backward_prfstep_cond th []
fun add_backward1_prfstep th = add_backward1_prfstep_cond th []
fun add_backward2_prfstep th = add_backward2_prfstep_cond th []
fun add_resolve_prfstep th = add_resolve_prfstep_cond th []

fun add_rewrite_rule_cond th conds thy =
    let
      val (lhs, rhs) = th |> strip_horn' |> snd |> HOLogic.dest_eq
      (* If rhs is of form ?n, create filter for ?n not already known
         to equal to left side.
       *)
      val neq_filt = case rhs of
                         Var ((nm, 0), _) => [with_filt (neqp_filter nm lhs)]
                       | _ => []
    in
      add_forward_prfstep_cond th ([K (WithTerm lhs)] @ neq_filt @ conds) thy
    end

fun add_rewrite_rule_back_cond th = add_rewrite_rule_cond (obj_sym_th th)
fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th
fun add_rewrite_rule_bidir_cond th conds =
    add_rewrite_rule_cond th conds #> add_rewrite_rule_back_cond th conds

end  (* structure ProofStep_Data. *)

open ProofStep_Data
