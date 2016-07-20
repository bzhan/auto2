(* Definition of type proofstep, and facility for adding basic proof
   steps.
 *)

val (PRIORITY_NORM, PRIORITY_URGENT,
     PRIORITY_SHADOW, PRIORITY_RESOLVE, PRIORITY_ADD) = (1, 2, 3, 4, 5)

signature PROOFSTEP =
sig
  datatype proofstep_fn
    = OneStep of rewrite_type -> status -> box_item -> Update.raw_update list
    | TwoStep of rewrite_type -> status -> box_item -> box_item ->
                 Update.raw_update list
  type proofstep
  type prfstep_filter
  datatype prfstep_descriptor = WithFact of term
                              | WithItem of string * term
                              | WithProperty of term
                              | GetFact of term * thm
                              | ShadowFirst | ShadowSecond
                              | CreateCase of term | CreateConcl of term
                              | Filter of prfstep_filter
  val is_relevant_to_properties: theory -> string list -> proofstep -> bool
  val apply_prfstep: rewrite_type -> status -> box_item list -> proofstep ->
                     Update.raw_update list
  val WithGoal: term -> prfstep_descriptor
  val WithTerm: term -> prfstep_descriptor
  val WithProp: term -> prfstep_descriptor
  val string_of_desc: theory -> prfstep_descriptor -> string
  val string_of_descs: theory -> prfstep_descriptor list -> string
  val get_insts_filt: match_arg -> box_item -> rewrite_type -> id_inst ->
                      prfstep_filter -> id_inst_th list
  val get_insts: match_arg -> box_item -> rewrite_type -> id_inst ->
                 id_inst_th list

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
  val ac_atomic_filter: string -> string -> prfstep_filter

  (* Standard descriptors *)
  val forward_descs: thm -> prfstep_descriptor list

  (* First level proofstep writing functions. *)
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_args: prfstep_descriptor list -> match_arg list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> term list
  val retrieve_shadows: prfstep_descriptor list -> int list
  val get_property_ths:
      rewrite_table -> id_inst -> match_arg list -> (box_id * thm list) list
  val prfstep_custom:
      string -> prfstep_descriptor list -> int ->
      (id_inst_ths -> box_item list -> status -> Update.raw_update list) ->
      proofstep
  val gen_prfstep: string -> prfstep_descriptor list -> proofstep
  val prfstep_pre_conv: string -> prfstep_descriptor list ->
                        (Proof.context -> conv) -> proofstep
  val prfstep_conv: string -> prfstep_descriptor list -> conv -> proofstep
  val name_of_eval_thm: thm -> string
  val prfsteps_eval_fun': thm list -> thm list -> proofstep list
  val prfsteps_eval_fun: thm list -> proofstep list
end;

structure ProofStep : PROOFSTEP =
struct

open Box
open Update
open Status

datatype proofstep_fn
  = OneStep of rewrite_type -> status -> box_item -> raw_update list
  | TwoStep of rewrite_type -> status -> box_item -> box_item -> raw_update list

type proofstep =
     {name: string, args: match_arg list, priority: int, func: proofstep_fn}

type prfstep_filter = rewrite_table -> id_inst -> bool

datatype prfstep_descriptor = WithFact of term
                            | WithItem of string * term
                            | WithProperty of term
                            | GetFact of term * thm
                            | ShadowFirst | ShadowSecond
                            | CreateCase of term | CreateConcl of term
                            | Filter of prfstep_filter

(* Check if the proof step is relevant to the given properties. *)
fun is_relevant_to_properties thy property_nms {args, ...} =
    let
      val pats =
          args |> filter (fn arg => case arg of TypedMatch _ => false
                                              | _ => true)
               |> map pat_of_match_arg
    in
      if exists Term.is_Var pats then true
      else length (inter (op =) property_nms
                         (pats |> filter (is_property_const thy)
                               |> get_property_names)) > 0
    end

fun apply_prfstep rtype st items {func, ...} =
    case func of
        OneStep f => f rtype st (the_single items)
      | TwoStep f => f rtype st (hd items) (nth items 1)

fun WithGoal t =
    let
      val _ = assert (type_of t = boolT) "WithGoal: pat should have type bool."
    in
      WithFact (get_neg t)
    end

fun WithTerm t = WithItem (TY_TERM, t)

fun WithProp t =
    let
      val _ = assert (type_of t = boolT) "WithProp: pat should have type bool."
    in
      WithItem (TY_PROP, t)
    end

fun string_of_desc thy desc =
    let
      val print = str o pretty_term_thy thy
    in
      case desc of
          WithFact t =>
          if is_neg t then "WithGoal " ^ (print (get_neg t))
          else "WithFact " ^ (print t)
        | WithItem (ty_str, t) =>
          if ty_str = TY_TERM then "WithTerm " ^ (print t)
          else "WithItem " ^ ty_str ^ " " ^ (print t)
        | WithProperty t => "WithProperty " ^ (print t)
        | GetFact (t, th) =>
          if t aconv @{term False} then
            "GetResolve " ^ (name_of_thm th)
          else if is_neg t then
            "GetGoal (" ^ (print (get_neg t)) ^ ", " ^ (name_of_thm th) ^ ")"
          else
            "GetFact (" ^ (print t) ^ ", " ^ (name_of_thm th) ^ ")"
        | ShadowFirst => "Shadow first" | ShadowSecond => "Shadow second"
        | CreateCase assum => "CreateCase " ^ (print assum)
        | CreateConcl concl => "CreateConcl " ^ (print concl)
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

(* Obtain list of incremental matches (taking into account rtype)
   between item and pattern specified by arg. Apply list of filters
   filt.
 *)
fun get_insts_filt arg item rtype (id, inst) filt =
    let
      val tbl = RewriteTable.table_of_rtype rtype
    in
      (ItemIO_Data.match_arg tbl arg item (id, inst))
          |> filter (filt tbl o fst)
          |> RewriteTable.replace_id_for_type rtype
    end

fun get_insts arg item rtype (id, inst) =
    get_insts_filt arg item rtype (id, inst) (K (K true))

(* prfstep_filter *)

val all_insts = fn _ => fn _ => true
fun id_filter f _ (id, _) = f id
fun neqt_filter s1 t2 tbl (id, inst) =
    not (RewriteTable.is_equiv id tbl (lookup_inst inst s1, t2))
fun neqp_filter s1 p2 tbl (id, inst) =
    (Matcher.rewrite_match
         tbl (subst_term_norm inst p2, lookup_inst inst s1) (id, fo_init))
        |> filter (fn ((id', _), _) => id = id')
        |> length |> equal 0
fun not_numc_filter s tbl (id, inst) =
    (Matcher.rewrite_match
         tbl (@{term_pat "?NUMC"}, lookup_inst inst s) (id, fo_init))
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

fun ac_atomic_filter fnm s tbl (_, inst) =
    let
      val thy = RewriteTable.theory_of tbl
      val pre_info =
          the (ACUtil.lookup_ac_data (RewriteTable.theory_of tbl) fnm)
      val s = lookup_inst inst s
      val ac_info = the (ACUtil.inst_ac_info thy (fastype_of s) pre_info)
    in
      length (ACUtil.dest_ac_l ac_info s) = 1
    end
    handle Option.Option => raise AUTO2 "ac_atomic_filter: ac_info not found"

(* Descriptors for applying th in forward direction (can be used in
   add_gen_prfstep.
 *)
fun forward_descs th =
    let
      val _ = assert (Thm.nprems_of th <= 2)
      val (prems, concl) = strip_horn' th
    in
      map WithFact prems @ [GetFact (concl, th)]
    end

(* First level proofstep writing functions. *)
fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val _ = assert (fastype_of pat_r = boolT)
                     "apply_pat_r: pat_r should be of type bool"

      (* Split into meta equalities (usually produced by term
         matching, not applied to th, and others (assumptions for th).
       *)
      val (eqs, ths') = ths |> filter_split is_meta_eq_thm
      val _ = assert (length ths' = Thm.nprems_of th)
                     "apply_pat_r: wrong number of assumptions."
      val obj_eqs = map to_obj_eq eqs

      val inst_new = subst_term_norm inst (HOLogic.mk_Trueprop pat_r)
      val th' = th |> subst_thm ctxt inst |> fold Thm.elim_implies ths'
      val _ = if inst_new aconv (Thm.prop_of th') then () else
              raise AUTO2CT ("apply_pat_r: conclusion mismatch",
                             map (cert ctxt) [inst_new, Thm.prop_of th'])
    in
      th' |> apply_to_thm (
        Conv.every_conv (map (fn eq => rewr_obj_eq_top ctxt eq) obj_eqs))
    end

fun retrieve_args descs =
    maps (fn desc => case desc of
                         WithFact t => [PropMatch t]
                       | WithItem (ty_str, t) => [TypedMatch (ty_str, t)]
                       | WithProperty t => [PropertyMatch t]
                       | _ => [])
         descs

fun retrieve_pats_r descs =
    maps (fn desc => case desc of
                         GetFact (pat_r, th) => [(pat_r, th)]
                       | _ => [])
         descs

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
          case desc of
              CreateCase assum => [HOLogic.mk_Trueprop assum]
            | CreateConcl concl => [HOLogic.mk_Trueprop (get_neg concl)]
            | _ => []
    in
      maps retrieve_case descs
    end

fun retrieve_shadows descs =
    let
      fun retrieve_shadow desc =
          case desc of ShadowFirst => [0] | ShadowSecond => [1] | _ => []
    in
      maps retrieve_shadow descs
    end

(* Given list of PropertyMatch arguments, attempt to find the
   corresponding theorems in the property table. Return the list of
   theorems for each possible (mutually non-comparable) box IDs.
 *)
fun get_property_ths (tbl as {lat, ...}) (id, inst) property_args =
    if length property_args = 0 then
      [(id, [])]
    else let
      val property_args' = map (subst_arg inst) property_args
      fun process_p_arg p_arg =
          case p_arg of
              PropertyMatch prop => RewriteTable.get_property tbl (id, prop)
            | _ => raise AUTO2 "get_property_ths: wrong kind of arg."
      val p_ths = map process_p_arg property_args'
    in
      if exists (fn lst => length lst = 0) p_ths then []
      else p_ths |> BoxID.get_all_merges_info lat
                 |> max_partial (BoxID.id_is_eq_ancestor lat)
    end

(* Creates a proofstep with specified patterns and filters (in descs),
   and a custom function converting any instantiations into updates.
 *)
fun prfstep_custom name descs priority updt_fn =
    let
      val args = retrieve_args descs
      val item_args = filter_out is_property_match args
      val property_args = filter is_property_match args
      val filt = retrieve_filts descs

      (* Processing an instantiation after matching the one or two
         main matchers: apply filters, remove trivial True from
         matchings, find properties, and replace ids based on rtype.
       *)
      fun process_inst rtype ((id, inst), ths) =
          let
            val tbl = RewriteTable.table_of_rtype rtype
          in
            if not (filt tbl (id, inst)) then [] else
            (get_property_ths tbl (id, inst) property_args)
                |> map (fn (id', p_ths) => ((id', inst), p_ths @ ths))
                |> RewriteTable.replace_id_for_type rtype
          end
    in
      if length item_args = 1 then
        let
          val arg = the_single item_args
          fun prfstep rtype st item =
              let
                val tbl = RewriteTable.table_of_rtype rtype
                val inst_ths =
                    (ItemIO_Data.match_arg tbl arg item ([], fo_init))
                        |> map (fn (inst, th) => (inst, [th]))
                        |> maps (process_inst rtype)
              in
                maps (fn inst_th => updt_fn inst_th [item] st) inst_ths
              end
        in
          {name = name, args = args, priority = priority,
           func = OneStep prfstep}
        end
      else if length item_args = 2 then
        let
          val (arg1, arg2) = the_pair item_args
          fun prfstep1 rtype st item1 =
              let
                val tbl = RewriteTable.table_of_rtype rtype
                val inst_ths =
                    ItemIO_Data.match_arg tbl arg1 item1 ([], fo_init)

                fun process_inst1 item2 ((id, inst), th) =
                    let
                      val arg2' = subst_arg inst arg2
                      val inst_ths' =
                          (ItemIO_Data.match_arg tbl arg2' item2 (id, inst))
                              |> map (fn (inst', th') => (inst', [th, th']))
                              |> maps (process_inst rtype)
                    in
                      maps (fn inst' => updt_fn inst' [item1, item2] st)
                           inst_ths'
                    end
              in
                fn item2 => maps (process_inst1 item2) inst_ths
              end
        in
          {name = name, args = args, priority = priority,
           func = TwoStep prfstep1}
        end
      else
        raise AUTO2 "prfstep_custom: must have 1 or 2 patterns."
    end

(* Create a proofstep from a list of proofstep descriptors. See
   datatype prfstep_descriptor for allowed types of descriptors.
 *)
fun gen_prfstep name descs =
    let
      val args = retrieve_args descs
      val pats_r = retrieve_pats_r descs
      val cases = retrieve_cases descs
      val shadows = retrieve_shadows descs
      val input_descs =
          filter (fn desc => case desc of WithFact _ => true
                                        | WithItem _ => true
                                        | WithProperty _ => true
                                        | Filter _ => true
                                        | _ => false) descs

      (* Verify that all schematic variables appearing in pats_r /
         cases appear in pats.
       *)
      val pats = map pat_of_match_arg args
      val vars = map Var (fold Term.add_vars pats [])
      fun check_pat_r (pat_r, _) =
          subset (op aconv) (map Var (Term.add_vars pat_r []), vars)
      fun check_case assum =
          subset (op aconv) (map Var (Term.add_vars assum []), vars)
      val _ = assert (forall check_pat_r pats_r andalso forall check_case cases)
                     "gen_prfstep: new schematic variable in pats_r / cases."

      fun pats_r_to_update ctxt (inst_ths as ((id, _), _)) =
          if length pats_r = 0 then [] else
          let
            val ths = map (apply_pat_r ctxt inst_ths) pats_r
          in
            if length ths = 1 then [thm_update (id, the_single ths)]
            else [AddItems {id = id, raw_items = map thm_to_ritem ths}]
          end

      fun case_to_update ((id, inst), _) assum =
          AddBoxes {
            id = id, inits = [InitAssum (subst_term_norm inst assum)], cbs = []}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases

      fun shadow_to_update items ((id, _), _) n =
          ShadowItem {id = id, item = nth items n}
      fun shadows_to_update items inst =
          map (shadow_to_update items inst) shadows

      val priority =
          if length shadows > 0 then PRIORITY_SHADOW
          else if exists (fn (t, _) => t aconv bool_False) pats_r
          then PRIORITY_RESOLVE else PRIORITY_ADD

      fun updt_fn inst_th items {ctxt, ...} =
          pats_r_to_update ctxt inst_th @ cases_to_update inst_th @
          shadows_to_update items inst_th
    in
      prfstep_custom name input_descs priority updt_fn
    end

fun prfstep_pre_conv name descs pre_cv =
    let
      val args = retrieve_args descs
      val _ = case args of
                  [TypedMatch ("TERM", _)] => ()
                | _ => raise AUTO2 ("prfstep_conv: should have exactly one " ^
                                    "term pattern.")
      val filt = retrieve_filts descs

      fun prfstep rtype {ctxt, ...} item =
          let
            val tbl = RewriteTable.table_of_rtype rtype
            val inst_ths =
                get_insts_filt (the_single args) item rtype ([], fo_init) filt
            fun inst_to_updt ((id, _), eq1) =
                (* Here eq1 is meta_eq from pat(inst) to item. *)
                let
                  val ct = Thm.lhs_of eq1
                  val err = (name ^ ": cv failed.", [ct])
                  val eq_th = pre_cv ctxt ct
                              handle CTERM _ => raise AUTO2CT err
                in
                  if Thm.is_reflexive eq_th then [] else
                  if RewriteTable.is_equiv id tbl (rhs_of eq1, rhs_of eq_th)
                  then []
                  else [thm_update (id, to_obj_eq (
                                      transitive_list [meta_sym eq1, eq_th]))]
                end
          in
            maps inst_to_updt inst_ths
          end
    in
      {name = name, args = args, priority = PRIORITY_ADD,
       func = OneStep prfstep}
    end

fun prfstep_conv name descs cv = prfstep_pre_conv name descs (K cv)

(* Apply rewriting using ths in the top_conv order. When ths is the
   set of simp rules of a certain function, this conversion expands
   the function fully.
 *)
fun eval_fun_conv ths ctxt ct =
    let
      fun eval_conv ct =
          Conv.repeat_conv (Conv.first_conv (map rewr_obj_eq ths)) ct
    in
      Conv.top_conv (K eval_conv) ctxt ct
    end

fun name_of_eval_thm th = (name_of_thm th) ^ "@eval"

(* Match the left side of each desc_ths. On each match, fully expand
   using eval_fun_conv on the list of theorems ths.
 *)
fun prfsteps_eval_fun' desc_ths ths =
    let
      fun get_prfstep th =
          prfstep_pre_conv (name_of_eval_thm th)
                           [WithTerm (th |> prop_of' |> HOLogic.dest_eq |> fst)]
                           (eval_fun_conv ths)
    in
      map get_prfstep desc_ths
    end

fun prfsteps_eval_fun ths = prfsteps_eval_fun' ths ths

end  (* structure ProofStep *)

open ProofStep

(* Table of proofsteps, categorized by type. *)
datatype proofstep_table
  = ProofStepTable of
    {prfsteps: proofstep Symtab.table, sorted_prfsteps: proofstep list,
     fixed_sc: int Symtab.table, reserved_names: string list}

fun prfstep_ord ({priority, ...}, {priority = priority', ...}) =
    int_ord (priority, priority')

structure ProofStepData =
Generic_Data (
  type T = proofstep_table;
  val empty = ProofStepTable {prfsteps = Symtab.empty, sorted_prfsteps = [],
                              fixed_sc = Symtab.empty, reserved_names = []};
  val extend = I;
  fun merge (
    ProofStepTable {prfsteps = p1, sorted_prfsteps = sp1, fixed_sc = sc1,
                    reserved_names = r1},
    ProofStepTable {prfsteps = p2, sorted_prfsteps = sp2, fixed_sc = sc2,
                    reserved_names = r2}) =
      ProofStepTable {
        prfsteps = Symtab.merge (op pointer_eq) (p1, p2),
        sorted_prfsteps = sort prfstep_ord (
          Library.merge (op pointer_eq) (sp1, sp2)),
        fixed_sc = Symtab.merge (op =) (sc1, sc2),
        reserved_names = Library.merge (op =) (r1, r2)}
)

signature PROOFSTEP_DATA =
sig
  val proofstep_data_of: Proof.context -> ProofStepData.T
  val map_theory_proofsteps:
      (Proof.context -> Proof.context) -> theory -> theory
  val map_generic_proofsteps:
      (Proof.context -> Proof.context) -> Context.generic -> Context.generic
  val map_proofstep_data_ctxt:
      (ProofStepData.T -> ProofStepData.T) -> Proof.context -> Proof.context
  val map_proofstep_data:
      (ProofStepData.T -> ProofStepData.T) -> theory -> theory

  val add_prfstep: proofstep -> theory -> theory
  val add_prfstep_ctxt: proofstep -> Proof.context -> Proof.context
  val del_prfstep: string -> theory -> theory
  val del_prfstep_thm: thm -> theory -> theory
  val add_fixed_sc_ctxt: string * int -> Proof.context -> Proof.context
  val add_fixed_sc: string * int -> theory -> theory
  val get_prfstep_by_name: Proof.context -> string -> proofstep
  val get_prfsteps: Proof.context -> proofstep list
  val get_fixed_sc: Proof.context -> string -> int option
  val add_reserved_name: string -> theory -> theory
  val is_reserved_name: Proof.context -> string -> bool

  val add_prfstep_custom:
      (string * prfstep_descriptor list * int *
       (id_inst_ths -> box_item list -> status -> Update.raw_update list)) ->
      theory -> theory

  val add_gen_prfstep: string * prfstep_descriptor list -> theory -> theory
  val add_gen_prfstep_ctxt:
      string * prfstep_descriptor list -> Proof.context -> Proof.context
  val add_prfstep_pre_conv: string * prfstep_descriptor list *
                            (Proof.context -> conv) -> theory -> theory
  val add_prfstep_conv:
      string * prfstep_descriptor list * conv -> theory -> theory

  (* Constructing conditional prfstep_descriptors. *)
  type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor
  val with_term: string -> pre_prfstep_descriptor
  val with_cond: string -> pre_prfstep_descriptor
  val with_conds: string list -> pre_prfstep_descriptor list
  val with_filt: prfstep_filter -> pre_prfstep_descriptor
  val with_filts: prfstep_filter list -> pre_prfstep_descriptor list

  (* Second level proofstep writing functions. *)
  val backward_th: thm -> thm
  val to_contra_th: thm -> thm
  val add_and_print_prfstep_ctxt:
      string -> prfstep_descriptor list -> Proof.context -> Proof.context
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
  val add_forward_prfstep: thm -> theory -> theory
  val add_backward_prfstep: thm -> theory -> theory
  val add_backward1_prfstep: thm -> theory -> theory
  val add_backward2_prfstep: thm -> theory -> theory
  val add_resolve_prfstep: thm -> theory -> theory

  val add_forward_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_backward_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_backward1_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_backward2_prfstep_ctxt: thm -> Proof.context -> Proof.context
  val add_resolve_prfstep_ctxt: thm -> Proof.context -> Proof.context

  val add_rewrite_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory

  val add_rewrite_rule_ctxt: thm -> Proof.context -> Proof.context
  val add_rewrite_rule_back_ctxt: thm -> Proof.context -> Proof.context
  val add_rewrite_rule_bidir_ctxt: thm -> Proof.context -> Proof.context

  val add_eval_fun_prfsteps': thm list -> thm list -> theory -> theory
  val add_eval_fun_prfsteps: thm list -> theory -> theory

  val setup_attrib:
      (thm -> Proof.context -> Proof.context) -> attribute context_parser
end;

structure ProofStep_Data : PROOFSTEP_DATA =
struct

fun proofstep_data_of ctxt = ProofStepData.get (Context.Proof ctxt)

fun map_theory_proofsteps f thy =
    let
      val ctxt' = f (Proof_Context.init_global thy)
      val thy' = Proof_Context.theory_of ctxt'
    in
      Context.theory_map (ProofStepData.map (K (proofstep_data_of ctxt'))) thy'
    end

fun map_generic_proofsteps f =
    Context.mapping
        (map_theory_proofsteps (f o Context_Position.not_really)) I

fun map_proofstep_data_ctxt f =
    Context.proof_map (ProofStepData.map f)

val map_proofstep_data = map_theory_proofsteps o map_proofstep_data_ctxt

fun add_prfstep_ctxt (prfstep as {args, ...}) =
    if length (filter_out is_property_match args) >= 1 andalso
       length (filter_out is_property_match args) <= 2 then
      map_proofstep_data_ctxt (
        fn ProofStepTable {
            prfsteps, sorted_prfsteps, fixed_sc, reserved_names} =>
           if member (op =) reserved_names (#name prfstep) then
             raise AUTO2 ("add_prfstep: name " ^ (#name prfstep) ^
                          " is reserved.")
           else
             ProofStepTable {
               prfsteps = Symtab.update_new (#name prfstep, prfstep) prfsteps,
               sorted_prfsteps = sort prfstep_ord (sorted_prfsteps @ [prfstep]),
               fixed_sc = fixed_sc, reserved_names = reserved_names})
    else
      raise AUTO2 "add_proofstep: need 1 or 2 patterns."

val add_prfstep = map_theory_proofsteps o add_prfstep_ctxt

(* Deleting a proofstep. For string inputs, try adding theory
   name. For theorem inputs, try all @-suffixes.
 *)
fun del_prfstep_pred pred =
    map_proofstep_data (
      fn ProofStepTable {prfsteps, sorted_prfsteps, fixed_sc, reserved_names} =>
         let
           val keys = Symtab.keys prfsteps
           val to_delete = filter pred keys
           fun eq_name (key, {name, ...}) = (key = name)
         in
           if length to_delete = 0 then raise AUTO2 "del_prfstep: not found"
           else let
             val _ = map (fn name => tracing ("Delete " ^ name)) to_delete
           in
             ProofStepTable {
               prfsteps = prfsteps |> fold Symtab.delete to_delete,
               sorted_prfsteps = sorted_prfsteps |> subtract eq_name to_delete,
               fixed_sc = fixed_sc |> fold Symtab.delete_safe to_delete,
               reserved_names = reserved_names}
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

fun add_fixed_sc_ctxt (nm, sc) =
    map_proofstep_data_ctxt (
      fn ProofStepTable {prfsteps, sorted_prfsteps, fixed_sc, reserved_names} =>
         case find_first (equal nm) (Symtab.keys prfsteps) of
             NONE => raise AUTO2 ("add_fixed_sc: not found " ^ nm)
           | _ => ProofStepTable {
                   prfsteps = prfsteps, sorted_prfsteps = sorted_prfsteps,
                   fixed_sc = fixed_sc |> Symtab.update_new (nm, sc),
                   reserved_names = reserved_names})

val add_fixed_sc = map_theory_proofsteps o add_fixed_sc_ctxt

fun get_prfstep_by_name ctxt name =
    let
      val ProofStepTable {prfsteps, ...} = proofstep_data_of ctxt
    in
      case Symtab.lookup prfsteps name of
          NONE => raise AUTO2 ("get_prfstep_by_name: not found " ^ name)
        | SOME prfstep => prfstep
    end

fun get_prfsteps ctxt =
    let
      val ProofStepTable {sorted_prfsteps, ...} = proofstep_data_of ctxt
    in
      sorted_prfsteps
    end

fun get_fixed_sc ctxt nm =
    let val ProofStepTable {fixed_sc, ...} = proofstep_data_of ctxt in
      Symtab.lookup fixed_sc nm
    end

fun add_reserved_name nm =
    map_proofstep_data (
      fn ProofStepTable {prfsteps, sorted_prfsteps, fixed_sc, reserved_names} =>
         if member (op =) reserved_names nm orelse
            Symtab.defined prfsteps nm then
           raise AUTO2 ("add_reserved_name: " ^ nm ^ " already used")
         else
           ProofStepTable {
             prfsteps = prfsteps, sorted_prfsteps = sorted_prfsteps,
             fixed_sc = fixed_sc, reserved_names = nm :: reserved_names})

fun is_reserved_name ctxt nm =
    let
      val ProofStepTable {reserved_names, ...} = proofstep_data_of ctxt
    in
      member (op =) reserved_names nm
    end

fun add_prfstep_custom (name, descs, priority, updt_fn) =
    add_prfstep (prfstep_custom name descs priority updt_fn)
fun add_gen_prfstep (name, descs) = add_prfstep (gen_prfstep name descs)
fun add_gen_prfstep_ctxt (name, descs) =
    add_prfstep_ctxt (gen_prfstep name descs)
fun add_prfstep_pre_conv (name, descs, pre_cv) =
    add_prfstep (prfstep_pre_conv name descs pre_cv)
fun add_prfstep_conv (name, descs, cv) =
    add_prfstep (prfstep_conv name descs cv)

(* Constructing conditional prfstep_descriptors. *)

type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor

fun with_term str ctxt =
    let
      val t = read_pat ctxt str
      val _ = assert (length (Term.add_frees t []) = 0)
                     "with_term: should not contain free variable."
    in
      WithTerm t
    end

fun with_cond str ctxt =
    let
      val cond = read_pat ctxt str
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

(* Second level proofstep writing functions. *)

fun add_and_print_prfstep_ctxt nm descs ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val _ = writeln (nm ^ "\n" ^ (string_of_descs thy descs))
    in
      add_gen_prfstep_ctxt (nm, descs) ctxt
    end

(* Obtain the first several premises of th that are properties. *)
fun get_property_prems th =
    let
      val thy = Thm.theory_of_thm th
    in
      th |> Thm.prems_of |> filter_first_split (is_property_prem' thy) |> fst
    end

fun add_forward_prfstep_cond_ctxt th conds ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val ctxt' = ctxt |> Variable.declare_term (Thm.prop_of th)

      (* Instantiate conds with ctxt, and divide into two classes. *)
      fun classify_conds cond =
          case cond of
              WithItem ("TERM", _) => true
            | Filter _ => false
            | _ => raise AUTO2 "add_forward_prfstep: unexpected cond."

      val (term_conds, filt_conds) =
          conds |> map (fn cond => cond ctxt')
                |> filter_split classify_conds

      (* The total number of WithTerm conditions and fact/goal
         conditions must be at most two.
       *)
      val _ = assert (length term_conds <= 2)
                     "More than two WithTerm conditions"

      (* Get list of assumptions to be obtained from the property table. *)
      val p_assums = get_property_prems th
      val p_conds = map (WithProperty o HOLogic.dest_Trueprop) p_assums
      val p_count = length p_conds

      (* Convert to obj imp any extraneous meta imps. *)
      val max_fact_conds = 2 - length term_conds
      val th' =
          th |> apply_to_thm (to_obj_conv_on_horn ctxt)
             |> (if Thm.nprems_of th - p_count > max_fact_conds then
                   apply_to_thm (
                     skip_n_conv (p_count + max_fact_conds) (to_obj_conv ctxt))
                 else I)
             |> Thm.has_name_hint th ? Thm.put_name_hint (Thm.get_name_hint th)
      val (assums, concl) =
          th' |> strip_horn'
              |> apfst (snd o filter_first_split (is_property_prem thy))

      (* Extract the list of patterns to be matched. By default, place
         matching on terms first.
       *)
      fun extract_term_cond cond =
          case cond of
              WithItem ("TERM", t) => t
            | _ => raise AUTO2 "extract_term_cond"

      val pats = map extract_term_cond term_conds @ assums
      val match_descs = term_conds @ map WithFact assums
      val _ = assert (length pats > 0 andalso length pats <= 2)
                     "add_forward_prfstep"
      val _ = assert (is_pattern (HOLogic.mk_tuple pats))
                     "add_forward_prfstep: invalid patterns."

    in
      (* Switch two assumptions if necessary. *)
      if length pats = 2 andalso
         not (Matcher.get_pattern_order thy (the_pair pats)) then
        let
          val _ = writeln ("Switching two patterns.")
          val swap_prems_cv = Conv.rewr_conv @{thm swap_prems_eq}
          val th'' =
              if length assums = 1 then th'
              else th' |> apply_to_thm (skip_n_conv p_count swap_prems_cv)
                       |> update_name_of_thm th' ""
          val swap_match_descs = [nth match_descs 1, hd match_descs]
          val descs = p_conds @ swap_match_descs @ filt_conds @
                      [GetFact (concl, th'')]
        in
          add_and_print_prfstep_ctxt (name_of_thm th') descs ctxt
        end
      else
        let
          val descs = p_conds @ match_descs @ filt_conds @
                      [GetFact (concl, th')]
        in
          add_and_print_prfstep_ctxt (name_of_thm th') descs ctxt
        end
    end

fun add_forward_prfstep_cond th conds =
    map_theory_proofsteps (add_forward_prfstep_cond_ctxt th conds)

(* Convert theorems of the form A1 ==> ... ==> An ==> C to A1 & ... &
   An ==> C. If keep_last = true, the last assumption is kept in
   implication form.
 *)
fun atomize_conj_cv keep_last ct =
    if length (Logic.strip_imp_prems (Thm.term_of ct)) <=
       (if keep_last then 2 else 1) then
      Conv.all_conv ct
    else
      ((Conv.arg_conv (atomize_conj_cv keep_last))
           then_conv (if keep_last then Conv.rewr_conv @{thm atomize_conjL2}
                      else Conv.rewr_conv @{thm HOL.atomize_conjL})) ct

val try_nn_cancel = Conv.try_conv (rewr_obj_eq nn_cancel_th)

(* From A ==> B obtain ~B ==> ~A. From A ==> B ==> C obtain ~C ==> ~(A
   & B), etc.
 *)
fun backward_th th =
    let
      val to_skip =
          Int.min (length (get_property_prems th), Thm.nprems_of th - 1)
      val cv = (atomize_conj_cv false)
                   then_conv (Conv.rewr_conv @{thm backward_conv})
                   then_conv (horn_conv try_nn_cancel)
    in
      th |> to_obj_conv_on_horn_th
         |> apply_to_thm (skip_n_conv to_skip cv)
         |> update_name_of_thm th "@back"
    end

(* From A ==> B ==> C obtain ~C ==> B ==> ~A. From A ==> B ==> C ==> D
   obtain ~D ==> C ==> ~(A & B), etc.
 *)
fun backward1_th th =
    let
      val to_skip =
          Int.min (length (get_property_prems th), Thm.nprems_of th - 2)
      val cv = (atomize_conj_cv true)
                   then_conv (Conv.rewr_conv @{thm backward1_conv})
                   then_conv (horn_conv try_nn_cancel)
    in
      th |> to_obj_conv_on_horn_th
         |> apply_to_thm (skip_n_conv to_skip cv)
         |> update_name_of_thm th "@back1"
    end

(* From A ==> B ==> C obtain ~C ==> A ==> ~B. From A ==> B ==> C ==> D
   obtain ~D ==> A ==> ~(B & C), etc.
 *)
fun backward2_th th =
    let
      val to_skip =
          Int.min (length (get_property_prems th), Thm.nprems_of th - 2)
      val cv = (Conv.arg_conv (atomize_conj_cv false))
                   then_conv (Conv.rewr_conv @{thm backward2_conv})
                   then_conv (horn_conv try_nn_cancel)
    in
      th |> to_obj_conv_on_horn_th
         |> apply_to_thm (skip_n_conv to_skip cv)
         |> update_name_of_thm th "@back2"
    end

fun to_contra_th th =
    let
      val to_skip = length (get_property_prems th)
      val rewr_th =
          case Thm.nprems_of th - to_skip of
              0 => if is_neg (HOLogic.dest_Trueprop (Thm.concl_of th)) then
                     @{thm to_contra_form'}
                   else @{thm to_contra_form}
            | 1 => @{thm resolve_conv}
            | _ => raise AUTO2 "to_contra_th: too many hypothesis in th."
      val cv = Conv.rewr_conv rewr_th then_conv (horn_conv try_nn_cancel)
    in
      th |> to_obj_conv_on_horn_th
         |> apply_to_thm (skip_n_conv to_skip cv)
         |> update_name_of_thm th "@res"
    end

fun add_backward_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward_th th) conds thy

fun add_backward1_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward1_th th) conds thy

fun add_backward2_prfstep_cond th conds thy =
    add_forward_prfstep_cond (backward2_th th) conds thy

fun add_resolve_prfstep_cond th conds thy =
    add_forward_prfstep_cond (to_contra_th th) conds thy

fun add_forward_prfstep th = add_forward_prfstep_cond th []
fun add_backward_prfstep th = add_backward_prfstep_cond th []
fun add_backward1_prfstep th = add_backward1_prfstep_cond th []
fun add_backward2_prfstep th = add_backward2_prfstep_cond th []
fun add_resolve_prfstep th = add_resolve_prfstep_cond th []

fun add_forward_prfstep_ctxt th = add_forward_prfstep_cond_ctxt th []
fun add_backward_prfstep_ctxt th =
    add_forward_prfstep_cond_ctxt (backward_th th) []
fun add_backward1_prfstep_ctxt th =
    add_forward_prfstep_cond_ctxt (backward1_th th) []
fun add_backward2_prfstep_ctxt th =
    add_forward_prfstep_cond_ctxt (backward2_th th) []
fun add_resolve_prfstep_ctxt th =
    add_forward_prfstep_cond_ctxt (to_contra_th th) []

fun add_rewrite_rule_cond_ctxt th conds ctxt =
    let
      val (lhs, rhs) = th |> strip_horn' |> snd |> HOLogic.dest_eq
      (* If rhs is of form ?n, create filter for ?n not already known
         to equal to left side.
       *)
      val neq_filt = case rhs of
                         Var ((nm, 0), _) => [with_filt (neqp_filter nm lhs)]
                       | _ => []
    in
      add_forward_prfstep_cond_ctxt
          th ([K (WithTerm lhs)] @ neq_filt @ conds) ctxt
    end

fun add_rewrite_rule_cond th conds =
    map_theory_proofsteps (add_rewrite_rule_cond_ctxt th conds)

fun add_rewrite_rule_back_cond th = add_rewrite_rule_cond (obj_sym_th th)
fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th
fun add_rewrite_rule_bidir_cond th conds =
    add_rewrite_rule_cond th conds #> add_rewrite_rule_back_cond th conds

fun add_rewrite_rule_ctxt th = add_rewrite_rule_cond_ctxt th []
fun add_rewrite_rule_back_ctxt th =
    add_rewrite_rule_cond_ctxt (obj_sym_th th) []
fun add_rewrite_rule_bidir_ctxt th =
    add_rewrite_rule_ctxt th #> add_rewrite_rule_back_ctxt th

fun add_eval_fun_prfsteps' desc_ths ths thy =
    let
      fun write_eval_thm th =
          writeln ((name_of_eval_thm th) ^ "\n" ^
                   (th |> Thm.prop_of |> pretty_term_thy thy |> str))
      val _ = map write_eval_thm desc_ths
    in
      fold add_prfstep (prfsteps_eval_fun' desc_ths ths) thy
    end

fun add_eval_fun_prfsteps ths = add_eval_fun_prfsteps' ths ths

fun setup_attrib f = Attrib.add_del
  (Thm.declaration_attribute (fn th => map_generic_proofsteps (f th)))
  (Thm.declaration_attribute (
      fn _ => fn _ => raise AUTO2 "del_step: not implemented."))

end  (* structure ProofStep_Data. *)

open ProofStep_Data
