(* Definition of type proofstep, and facility for adding basic proof
   steps.
 *)

val (PRIORITY_NORM, PRIORITY_URGENT,
     PRIORITY_SHADOW, PRIORITY_RESOLVE, PRIORITY_ADD) = (1, 2, 3, 4, 5)

datatype proofstep_fn
  = OneStep of rewrite_type -> status -> box_item -> raw_update list
  | TwoStep of rewrite_type -> status -> box_item -> box_item -> raw_update list

type proofstep =
     {name: string, args: match_arg list, priority: int, func: proofstep_fn}

type prfstep_filter = rewrite_table -> id_inst -> bool

datatype prfstep_descriptor = WithFact of term
                            | WithItem of string * term
                            | WithProperty of term
                            | WithWellForm of term * term
                            | GetFact of term * thm
                            | ShadowFirst | ShadowSecond
                            | CreateCase of term | CreateConcl of term
                            | Filter of prfstep_filter

signature PROOFSTEP =
sig
  val eq_prfstep: proofstep * proofstep -> bool
  val apply_prfstep: rewrite_type -> status -> box_item list -> proofstep ->
                     raw_update list
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
  val neq_filter: term -> prfstep_filter
  val order_filter: string -> string -> prfstep_filter
  val size1_filter: string -> prfstep_filter
  val not_type_filter: string -> typ -> prfstep_filter
  val unique_free_filter: string -> prfstep_filter

  (* First level proofstep writing functions. *)
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_args: prfstep_descriptor list -> match_arg list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> term list
  val retrieve_shadows: prfstep_descriptor list -> int list
  val has_shadows_desc: prfstep_descriptor list -> bool
  val get_side_ths:
      rewrite_table -> id_inst -> match_arg list -> (box_id * thm list) list
  val prfstep_custom:
      string -> prfstep_descriptor list -> int ->
      (id_inst_ths -> box_item list -> status -> raw_update list) -> proofstep
  val gen_prfstep: string -> prfstep_descriptor list -> proofstep
  val prfstep_pre_conv: string -> prfstep_descriptor list ->
                        (Proof.context -> conv) -> proofstep
  val prfstep_conv: string -> prfstep_descriptor list -> conv -> proofstep
  val prfsteps_eval_fun': thm list -> thm list -> proofstep list
  val prfsteps_eval_fun: thm list -> proofstep list
end;

structure ProofStep : PROOFSTEP =
struct

open Base
open UtilLogic

fun eq_prfstep (prfstep1, prfstep2) = (#name prfstep1 = #name prfstep2)

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
        | WithWellForm (_, req) => "WithWellForm " ^ (print req)
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
      (ItemIO.match_arg tbl arg item (id, inst))
          |> RewriteTable.filter_id_for_type rtype
          |> filter (filt tbl o fst)
          |> RewriteTable.replace_id_for_type rtype
    end

fun get_insts arg item rtype (id, inst) =
    get_insts_filt arg item rtype (id, inst) (K (K true))

(* prfstep_filter *)

val all_insts = fn _ => fn _ => true

fun neq_filter cond tbl (id, inst) =
    let
      val (lhs, rhs) =
          cond |> dest_not |> dest_eq
          handle Fail "dest_not" => raise Fail "neq_filter: not an inequality."
               | Fail "dest_eq" => raise Fail "neq_filter: not an inequality."
      val _ = assert (null (Term.add_frees cond []))
                     "neq_filter: should not contain free variable."

      val {ctxt, ...} = tbl
      val t1 = subst_term_norm inst lhs
      val t2 = subst_term_norm inst rhs
    in
      if has_vars t1 andalso has_vars t2 then true
      else if has_vars t1 then
        (Matcher.rewrite_match tbl (t1, cert ctxt t2) (id, fo_init))
            |> filter (fn ((id', _), _) => id = id')
            |> length |> equal 0
      else if has_vars t2 then
        (Matcher.rewrite_match tbl (t2, cert ctxt t1) (id, fo_init))
            |> filter (fn ((id', _), _) => id = id')
            |> length |> equal 0
      else
        not (RewriteTable.is_equiv_t id tbl (t1, t2))
    end

fun order_filter s1 s2 _ (_, inst) =
    not (Term_Ord.termless (lookup_inst inst s2, lookup_inst inst s1))

fun size1_filter s1 tbl (id, inst) =
    size_of_term (RewriteTable.simp_val_t id tbl (lookup_inst inst s1)) = 1

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
            filter is_same_type_free
                   (map Thm.term_of (RewriteTable.get_all_terms tbl))
      in
        length same_type_frees = 1
      end
    end

(* First level proofstep writing functions. *)
fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val _ = assert (fastype_of pat_r = boolT)
                     "apply_pat_r: pat_r should be of type bool"

      (* Split into meta equalities (usually produced by term
         matching, not applied to th, and others (assumptions for th).
       *)
      val (eqs, ths') = ths |> filter_split (is_meta_eq o Thm.prop_of)
      val _ = assert (length ths' = Thm.nprems_of th)
                     "apply_pat_r: wrong number of assumptions."
      val obj_eqs = map to_obj_eq eqs

      val inst_new = subst_term_norm inst (mk_Trueprop pat_r)
      val th' = th |> subst_thm ctxt inst |> fold Thm.elim_implies ths'
      val _ = if inst_new aconv (Thm.prop_of th') then () else
              raise Fail "apply_pat_r: conclusion mismatch"
    in
      th' |> apply_to_thm (
        Conv.every_conv (map (fn eq => rewr_obj_eq_top ctxt eq) obj_eqs))
    end

fun retrieve_args descs =
    maps (fn desc => case desc of
                         WithFact t => [PropMatch t]
                       | WithItem (ty_str, t) => [TypedMatch (ty_str, t)]
                       | WithProperty t => [PropertyMatch t]
                       | WithWellForm t => [WellFormMatch t]
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
              CreateCase assum => [mk_Trueprop assum]
            | CreateConcl concl => [mk_Trueprop (get_neg concl)]
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

fun has_shadows_desc descs = length (retrieve_shadows descs) > 0

(* Given list of PropertyMatch and WellFormMatch arguments, attempt to
   find the corresponding theorems in the rewrite table. Return the
   list of theorems for each possible (mutually non-comparable) box
   IDs.
 *)
fun get_side_ths (tbl as {lat, ...}) (id, inst) side_args =
    if null side_args then
      [(id, [])]
    else let
      val side_args' = map (ItemIO.subst_arg inst) side_args
      fun process_side_arg side_arg =
          case side_arg of
              PropertyMatch prop =>
              RewriteTable.get_property_t tbl (id, prop)
            | WellFormMatch (t, req) =>
              (RewriteTable.get_wellform_t tbl (id, t))
                  |> filter (fn (_, th) => prop_of' th aconv req)
            | _ => raise Fail "get_side_ths: wrong kind of arg."
      val side_ths = map process_side_arg side_args'
    in
      if exists null side_ths then []
      else side_ths |> BoxID.get_all_merges_info lat
                    |> max_partial (BoxID.id_is_eq_ancestor lat)
    end

(* Creates a proofstep with specified patterns and filters (in descs),
   and a custom function converting any instantiations into updates.
 *)
fun prfstep_custom name descs priority updt_fn =
    let
      val args = retrieve_args descs
      val (item_args, side_args) = filter_split ItemIO.is_ordinary_match args
      val filt = retrieve_filts descs
      val shadows = retrieve_shadows descs

      (* Processing an instantiation after matching the one or two
         main matchers: apply filters, remove trivial True from
         matchings, find properties, and replace ids based on rtype.
       *)
      fun process_inst rtype ((id, inst), ths) =
          let
            val tbl = RewriteTable.table_of_rtype rtype
          in
            (get_side_ths tbl (id, inst) side_args)
                |> map (fn (id', p_ths) => ((id', inst), p_ths @ ths))
                |> RewriteTable.filter_id_for_type rtype
                |> filter (filt tbl o fst)
                |> RewriteTable.replace_id_for_type rtype
          end

      fun shadow_to_update items ((id, _), _) n =
          ShadowItem {id = id, item = nth items n}
    in
      if length item_args = 1 then
        let
          val arg = the_single item_args
          fun prfstep rtype st item =
              let
                val tbl = RewriteTable.table_of_rtype rtype
                val inst_ths = (ItemIO.match_arg tbl arg item ([], fo_init))
                                |> map (fn (inst, th) => (inst, [th]))
                                |> maps (process_inst rtype)

                fun process_inst inst_th =
                    updt_fn inst_th [item] st @
                    map (shadow_to_update [item] inst_th) shadows
              in
                maps process_inst inst_ths
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
                val inst_ths = ItemIO.match_arg tbl arg1 item1 ([], fo_init)

                fun process_inst1 item2 ((id, inst), th) =
                    let
                      val arg2' = ItemIO.subst_arg inst arg2
                      val inst_ths' =
                          (ItemIO.match_arg tbl arg2' item2 (id, inst))
                              |> map (fn (inst', th') => (inst', [th, th']))
                              |> maps (process_inst rtype)

                      fun process_inst inst_th' =
                          updt_fn inst_th' [item1, item2] st @
                          map (shadow_to_update [item1, item2] inst_th') shadows
                    in
                      maps process_inst inst_ths'
                    end
              in
                fn item2 => maps (process_inst1 item2) inst_ths
              end
        in
          {name = name, args = args, priority = priority,
           func = TwoStep prfstep1}
        end
      else
        raise Fail "prfstep_custom: must have 1 or 2 patterns."
    end

(* Create a proofstep from a list of proofstep descriptors. See
   datatype prfstep_descriptor for allowed types of descriptors.
 *)
fun gen_prfstep name descs =
    let
      val args = retrieve_args descs
      val pats_r = retrieve_pats_r descs
      val cases = retrieve_cases descs
      val input_descs =
          filter (fn desc => case desc of GetFact _ => false
                                        | CreateCase _ => false
                                        | CreateConcl _ => false
                                        | _ => true) descs

      (* Verify that all schematic variables appearing in pats_r /
         cases appear in pats.
       *)
      val pats = map ItemIO.pat_of_match_arg args
      val vars = map Var (fold Term.add_vars pats [])
      fun check_pat_r (pat_r, _) =
          subset (op aconv) (map Var (Term.add_vars pat_r []), vars)
      fun check_case assum =
          subset (op aconv) (map Var (Term.add_vars assum []), vars)
      val _ = assert (forall check_pat_r pats_r andalso forall check_case cases)
                     "gen_prfstep: new schematic variable in pats_r / cases."

      fun pats_r_to_update ctxt (inst_ths as ((id, _), _)) =
          if null pats_r then [] else
          let
            val ths = map (apply_pat_r ctxt inst_ths) pats_r
          in
            if length ths = 1 then [Update.thm_update (id, the_single ths)]
            else [AddItems {id = id, sc = NONE,
                            raw_items = map Update.thm_to_ritem ths}]
          end

      fun case_to_update ((id, inst), _) assum =
          AddBoxes {id = id, sc = NONE,
                    inits = [InitAssum (subst_term_norm inst assum)]}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases

      val priority =
          if has_shadows_desc descs then PRIORITY_SHADOW else
          if exists (fn (t, _) => t aconv bFalse) pats_r then PRIORITY_RESOLVE
          else PRIORITY_ADD

      fun updt_fn inst_th _ {ctxt, ...} =
          pats_r_to_update ctxt inst_th @ cases_to_update inst_th
    in
      prfstep_custom name input_descs priority updt_fn
    end

fun prfstep_pre_conv name descs pre_cv =
    let
      val args = retrieve_args descs
      val _ = case args of
                  [TypedMatch ("TERM", _)] => ()
                | _ => raise Fail ("prfstep_conv: should have exactly one " ^
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
                  val err = name ^ ": cv failed."
                  val eq_th = pre_cv ctxt ct
                              handle CTERM _ => raise Fail err
                in
                  if Thm.is_reflexive eq_th then [] else
                  if RewriteTable.is_equiv
                         id tbl (Thm.rhs_of eq1, Thm.rhs_of eq_th)
                  then []
                  else let
                    val th = to_obj_eq (transitive_list [meta_sym eq1, eq_th])
                  in
                    [Update.thm_update (id, th)]
                  end
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

(* Match the left side of each desc_ths. On each match, fully expand
   using eval_fun_conv on the list of theorems ths.
 *)
fun prfsteps_eval_fun' desc_ths ths =
    let
      fun get_prfstep th =
          prfstep_pre_conv ((name_of_thm th) ^ "@eval")
                           [WithTerm (th |> prop_of' |> dest_eq |> fst)]
                           (eval_fun_conv ths)
    in
      map get_prfstep desc_ths
    end

fun prfsteps_eval_fun ths = prfsteps_eval_fun' ths ths

end  (* structure ProofStep *)

(* Table of proofsteps, categorized by type. *)
datatype proofstep_table
  = ProofStepTable of
    {prfsteps: proofstep Symtab.table, sorted_prfsteps: proofstep list,
     fixed_sc: int Symtab.table}

signature PROOFSTEP_DATA =
sig
  val add_prfstep_gnrc: proofstep -> Context.generic -> Context.generic
  val add_prfstep: proofstep -> theory -> theory
  val del_prfstep_pred_gnrc:
      (string -> bool) -> Context.generic -> Context.generic
  val del_prfstep_pred: (string -> bool) -> theory -> theory
  val del_prfstep: string -> theory -> theory
  val del_prfstep_thm: thm -> theory -> theory
  val del_prfstep_thm_str: string -> thm -> theory -> theory
  val add_fixed_sc_gnrc: string * int -> Context.generic -> Context.generic
  val add_fixed_sc: string * int -> theory -> theory
  val get_prfstep_by_name: Proof.context -> string -> proofstep
  val get_prfsteps: Proof.context -> proofstep list
  val get_fixed_sc: Proof.context -> string -> int option

  val add_prfstep_custom:
      (string * prfstep_descriptor list * int *
       (id_inst_ths -> box_item list -> status -> raw_update list)) ->
      theory -> theory
  val add_prfstep_custom_gnrc:
      (string * prfstep_descriptor list * int *
       (id_inst_ths -> box_item list -> status -> raw_update list)) ->
      Context.generic -> Context.generic

  val add_gen_prfstep: string * prfstep_descriptor list -> theory -> theory
  val add_gen_prfstep_gnrc:
      string * prfstep_descriptor list -> Context.generic -> Context.generic
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
  datatype prfstep_mode = MODE_FORWARD | MODE_FORWARD' | MODE_BACKWARD
                          | MODE_BACKWARD1 | MODE_BACKWARD2 | MODE_RESOLVE
  val add_and_print_prfstep_gnrc:
      string -> prfstep_descriptor list -> Context.generic -> Context.generic
  val add_prfstep_check_req_gnrc:
      string * string -> Context.generic -> Context.generic
  val add_prfstep_check_req: string * string -> theory -> theory
  val add_forward_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward'_prfstep_cond:
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
  val add_forward'_prfstep: thm -> theory -> theory
  val add_backward_prfstep: thm -> theory -> theory
  val add_backward1_prfstep: thm -> theory -> theory
  val add_backward2_prfstep: thm -> theory -> theory
  val add_resolve_prfstep: thm -> theory -> theory

  val add_forward_prfstep_cond_gnrc:
      thm -> pre_prfstep_descriptor list -> Context.generic -> Context.generic
  val add_forward_prfstep_gnrc: thm -> Context.generic -> Context.generic
  val add_forward'_prfstep_gnrc: thm -> Context.generic -> Context.generic
  val add_backward_prfstep_gnrc: thm -> Context.generic -> Context.generic
  val add_backward1_prfstep_gnrc: thm -> Context.generic -> Context.generic
  val add_backward2_prfstep_gnrc: thm -> Context.generic -> Context.generic
  val add_resolve_prfstep_gnrc: thm -> Context.generic -> Context.generic

  val add_rewrite_rule_cond_gnrc:
      thm -> pre_prfstep_descriptor list -> Context.generic -> Context.generic
  val add_rewrite_iff_rule_cond_gnrc:
      thm -> pre_prfstep_descriptor list -> Context.generic -> Context.generic

  val add_rewrite_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_rule_back_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_rule_bidir_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_iff_rule_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_iff_rule_back_gnrc: thm -> Context.generic -> Context.generic
  val add_rewrite_iff_rule_bidir_gnrc: thm -> Context.generic -> Context.generic

  val add_rewrite_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_iff_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_iff_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_iff_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory

  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory
  val add_rewrite_iff_rule: thm -> theory -> theory
  val add_rewrite_iff_back_rule: thm -> theory -> theory
  val add_rewrite_iff_bidir_rule: thm -> theory -> theory

  val add_eval_fun_prfsteps': thm list -> thm list -> theory -> theory
  val add_eval_fun_prfsteps: thm list -> theory -> theory

  val setup_attrib:
      (thm -> Context.generic -> Context.generic) -> attribute context_parser
end;

structure ProofStep_Data : PROOFSTEP_DATA =
struct

open Base
open UtilLogic
open ProofStep

fun prfstep_ord ({priority, ...}, {priority = priority', ...}) =
    int_ord (priority, priority')

structure Data = Generic_Data (
  type T = proofstep_table;
  val empty = ProofStepTable {
        prfsteps = Symtab.empty, sorted_prfsteps = [], fixed_sc = Symtab.empty};
  val extend = I;
  fun merge (
    ProofStepTable {prfsteps = p1, sorted_prfsteps = sp1, fixed_sc = sc1},
    ProofStepTable {prfsteps = p2, sorted_prfsteps = sp2, fixed_sc = sc2}) =
      ProofStepTable {
        prfsteps = Symtab.merge eq_prfstep (p1, p2),
        sorted_prfsteps = sort prfstep_ord (Library.merge eq_prfstep (sp1, sp2)),
        fixed_sc = Symtab.merge (op =) (sc1, sc2)}
)

fun proofstep_data_of ctxt = Data.get (Context.Proof ctxt)

fun add_prfstep_gnrc (prfstep as {args, ...}) =
    if length (filter_out ItemIO.is_side_match args) >= 1 andalso
       length (filter_out ItemIO.is_side_match args) <= 2 then
      Data.map (
        fn ProofStepTable {
            prfsteps, sorted_prfsteps, fixed_sc} =>
           if is_prefix_str "$" (#name prfstep) then
             error "Add prfstep: names beginning with $ is reserved."
           else
             ProofStepTable {
               prfsteps = Symtab.update_new (#name prfstep, prfstep) prfsteps,
               sorted_prfsteps = sort prfstep_ord (sorted_prfsteps @ [prfstep]),
               fixed_sc = fixed_sc})
    else
      error "add_proofstep: need 1 or 2 patterns."

val add_prfstep = Context.theory_map o add_prfstep_gnrc

(* Deleting a proofstep. For string inputs, try adding theory
   name. For theorem inputs, try all @-suffixes.
 *)
fun del_prfstep_pred_gnrc pred =
    Data.map (
      fn ProofStepTable {prfsteps, sorted_prfsteps, fixed_sc} =>
         let
           val keys = Symtab.keys prfsteps
           val to_delete = filter pred keys
           fun eq_name (key, {name, ...}) = (key = name)
         in
           if null to_delete then
             error "Delete prfstep: not found"
           else let
             val _ = writeln (cat_lines (map (fn name => "Delete " ^ name)
                                             to_delete))
           in
             ProofStepTable {
               prfsteps = prfsteps |> fold Symtab.delete to_delete,
               sorted_prfsteps = sorted_prfsteps |> subtract eq_name to_delete,
               fixed_sc = fixed_sc |> fold Symtab.delete_safe to_delete}
           end
         end)

val del_prfstep_pred = Context.theory_map o del_prfstep_pred_gnrc

fun del_prfstep nm thy =
    del_prfstep_pred (equal nm) thy

(* Delete all proofsteps for a given theorem. *)
fun del_prfstep_thm th =
    let
      val nm = name_of_thm th
    in
      del_prfstep_pred (equal nm orf is_prefix_str (nm ^ "@"))
    end

(* Delete proofsteps for a given theorem, with the given postfix. *)
fun del_prfstep_thm_str str th =
    del_prfstep_pred (equal (name_of_thm th ^ str))

fun add_fixed_sc_gnrc (nm, sc) =
    Data.map (
      fn ProofStepTable {prfsteps, sorted_prfsteps, fixed_sc} =>
         case find_first (equal nm) (Symtab.keys prfsteps) of
             NONE => error ("Add fixed sc: not found " ^ nm)
           | _ => ProofStepTable {
                   prfsteps = prfsteps, sorted_prfsteps = sorted_prfsteps,
                   fixed_sc = fixed_sc |> Symtab.update_new (nm, sc)})

val add_fixed_sc = Context.theory_map o add_fixed_sc_gnrc

fun get_prfstep_by_name ctxt name =
    let
      val ProofStepTable {prfsteps, ...} = proofstep_data_of ctxt
    in
      case Symtab.lookup prfsteps name of
          NONE => raise Fail ("get_prfstep_by_name: not found " ^ name)
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

fun add_prfstep_custom (name, descs, priority, updt_fn) =
    add_prfstep (prfstep_custom name descs priority updt_fn)
fun add_prfstep_custom_gnrc (name, descs, priority, updt_fn) =
    add_prfstep_gnrc (prfstep_custom name descs priority updt_fn)
fun add_gen_prfstep (name, descs) = add_prfstep (gen_prfstep name descs)
fun add_gen_prfstep_gnrc (name, descs) =
    add_prfstep_gnrc (gen_prfstep name descs)
fun add_prfstep_pre_conv (name, descs, pre_cv) =
    add_prfstep (prfstep_pre_conv name descs pre_cv)
fun add_prfstep_conv (name, descs, cv) =
    add_prfstep (prfstep_conv name descs cv)

(* Constructing conditional prfstep_descriptors. *)

type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor

fun with_term str ctxt =
    let
      val t = Proof_Context.read_term_pattern ctxt str
      val _ = assert (null (Term.add_frees t []))
                     "with_term: should not contain free variable."
    in
      WithTerm t
    end

fun with_cond str ctxt =
    Filter (neq_filter (Proof_Context.read_term_pattern ctxt str))

fun with_conds strs = map with_cond strs

fun with_filt filt = K (Filter filt)
fun with_filts filts = map with_filt filts

(* Second level proofstep writing functions. *)

fun add_and_print_prfstep_gnrc nm descs gnrc =
    let
      val thy = Context.theory_of gnrc
      val _ = writeln (nm ^ "\n" ^ (string_of_descs thy descs))
    in
      add_gen_prfstep_gnrc (nm, descs) gnrc
    end

(* Add a proofstep checking a requirement. *)
fun add_prfstep_check_req_gnrc (t_str, req_str) gnrc =
    let
      val ctxt = Context.proof_of gnrc
      val t = Proof_Context.read_term_pattern ctxt t_str
      val f = Term.head_of t
      val vars = map Free (Term.add_frees t [])
      val _ = assert (Term.is_Const f)
                     "add_prfstep_check_req: head must be Const."
      val (nm, _) = Term.dest_Const f
      val ctxt' = fold declare_free_term vars ctxt
      val req = Proof_Context.read_term_pattern ctxt' req_str

      fun get_subst var =
          case var of Free (nm, T) => (var, Var ((nm,0),T))
                    | _ => raise Fail "add_prfstep_check_req"
      val subst = map get_subst vars
      val t' = Term.subst_atomic subst t
      val req' = Term.subst_atomic subst req
    in
      add_and_print_prfstep_gnrc
          (nm ^ "_case") [WithTerm t', CreateConcl req'] gnrc
    end

val add_prfstep_check_req = Context.theory_map o add_prfstep_check_req_gnrc

datatype prfstep_mode = MODE_FORWARD | MODE_FORWARD' | MODE_BACKWARD
                        | MODE_BACKWARD1 | MODE_BACKWARD2 | MODE_RESOLVE

(* Maximum number of term matches for the given mode. *)
fun max_term_matches mode =
    case mode of
        MODE_FORWARD => 2
      | MODE_FORWARD' => 1
      | MODE_BACKWARD => 1
      | MODE_RESOLVE => 1
      | _ => 0

(* Obtain the first several premises of th that are either properties
   or wellformed-ness data. ts is the list of term matches.
 *)
fun get_side_prems thy mode ts th =
    let
      val (prems, concl) = strip_horn' th
      val _ = assert (length ts <= max_term_matches mode)
                     "get_side_prems: too many term matches."

      (* Helper function. Consider the case where the first n premises
         are side conditions. Find the additional terms to match
         against for each mode.
       *)
      fun additional_matches n =
          let
            val prems' = drop n prems
          in
            case mode of
                MODE_FORWARD => take (2 - length ts) prems'
              | MODE_FORWARD' =>
                if null ts andalso length prems' >= 2 then
                  [hd prems', List.last prems']
                else [List.last prems']
              | MODE_BACKWARD => [get_neg concl]
              | MODE_BACKWARD1 => [get_neg concl, List.last prems']
              | MODE_BACKWARD2 => [get_neg concl, hd prems']
              | MODE_RESOLVE =>
                if null ts andalso length prems' > 0 then
                  [get_neg concl, List.last prems']
                else [get_neg concl]
          end

      (* Determine whether t is a valid side premises, relative to the
         matches ts'. If yes, return the corresponding side
         matching. Otherwise return NONE.
       *)
      fun to_side_prems ts' t =
          case WellForm.is_subterm_wellform_data thy t ts' of
              SOME (t, req) => SOME (WithWellForm (t, req))
            | NONE => if Property.is_property_prem thy t then SOME (WithProperty t)
                      else NONE

      (* Attempt to convert the first n premises to side matchings. *)
      fun to_side_prems_n n =
          let
            val ts' = additional_matches n @ ts
            val side_prems' = prems |> take n
                                    |> map (to_side_prems ts')
          in
            if forall is_some side_prems' then
              SOME (map the side_prems')
            else NONE
          end

      (* Minimum number of premises for the given mode. *)
      val min_prems =
          case mode of
              MODE_FORWARD => 1 - length ts
            | MODE_FORWARD' => 1
            | MODE_BACKWARD => 1
            | MODE_BACKWARD1 => 2
            | MODE_BACKWARD2 => 2
            | MODE_RESOLVE => 0

      val _ = assert (length prems >= min_prems)
                     "get_side_prems: too few premises."
      val to_test = rev (0 upto (length prems - min_prems))
    in
      (* Always succeeds at 0. *)
      the (get_first to_side_prems_n to_test)
    end

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
           then_conv (if keep_last then Conv.rewr_conv atomize_conjL2_th
                      else Conv.rewr_conv atomize_conjL_th)) ct

(* Swap the last premise to become the first. *)
fun swap_prem_to_front ct =
    let
      val n = length (Logic.strip_imp_prems (Thm.term_of ct))
    in
      if n < 2 then
        Conv.all_conv ct
      else if n = 2 then
        Conv.rewr_conv Drule.swap_prems_eq ct
      else
        ((Conv.arg_conv swap_prem_to_front)
             then_conv (Conv.rewr_conv Drule.swap_prems_eq)) ct
    end

fun is_def_eq t =
    if not (is_eq_term t) then false
    else let
      val (lhs, rhs) = dest_eq t
    in
      Term.is_Var lhs andalso not (Term.is_Var rhs) andalso
      not (is_subterm lhs rhs)
    end

fun swap_one_eq_to_front ct =
    case Thm.term_of ct of
        Const ("Pure.imp", _) $ A $ _ =>
        if is_eq_term' A andalso is_def_eq (dest_Trueprop A) then
          Conv.arg1_conv to_meta_eq_cv ct
        else
          ((Conv.arg_conv swap_one_eq_to_front)
               then_conv (Conv.rewr_conv Drule.swap_prems_eq)) ct
      | _ => Conv.no_conv ct

(* Post-processing of the given theorem according to mode. *)
fun post_process_th ctxt mode side_count ts th =
    case mode of
        MODE_FORWARD =>
        let
          val to_skip = side_count + (2 - length ts)
        in
          th |> apply_to_thm (skip_n_conv to_skip (to_obj_conv ctxt))
             |> update_name_of_thm th ""
        end
      | MODE_FORWARD' =>
        let
          val cv =
              swap_prem_to_front
                  then_conv (skip_n_conv (2 - length ts) (to_obj_conv ctxt))
        in
          th |> apply_to_thm (skip_n_conv side_count cv)
             |> update_name_of_thm th ""
        end
      | MODE_BACKWARD =>
        let
          val cv = (atomize_conj_cv false)
                       then_conv (Conv.rewr_conv backward_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
                       then_conv (reduce_boolify ctxt)
        in
          th |> apply_to_thm (skip_n_conv side_count cv)
             |> update_name_of_thm th "@back"
        end
      | MODE_BACKWARD1 =>
        let
          val cv = (atomize_conj_cv true)
                       then_conv (Conv.rewr_conv backward1_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
                       then_conv (reduce_boolify ctxt)
        in
          th |> apply_to_thm (skip_n_conv side_count cv)
             |> update_name_of_thm th "@back1"
        end
      | MODE_BACKWARD2 =>
        let
          val cv = (Conv.arg_conv (atomize_conj_cv false))
                       then_conv (Conv.rewr_conv backward2_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
                       then_conv (reduce_boolify ctxt)
        in
          th |> apply_to_thm (skip_n_conv side_count cv)
             |> update_name_of_thm th "@back2"
        end
      | MODE_RESOLVE =>
        let
          val rewr_th =
              case Thm.nprems_of th - side_count of
                  0 => if is_neg (concl_of' th) then to_contra_form_th'
                       else to_contra_form_th
                | 1 => resolve_conv_th
                | _ => raise Fail "resolve: too many hypothesis in th."
          val cv = (Conv.rewr_conv rewr_th)
                       then_conv (horn_conv try_nn_cancel_cv)
                       then_conv (reduce_boolify ctxt)
        in
          th |> apply_to_thm (skip_n_conv side_count cv)
             |> update_name_of_thm th "@res"
        end

(* Add basic proofstep for the given theorem and mode. *)
fun add_basic_prfstep_cond_gnrc th mode conds gnrc =
    let
      val thy = Context.theory_of gnrc
      val ctxt = Context.proof_of gnrc
      val ctxt' = ctxt |> Variable.declare_term (Thm.prop_of th)

      (* Intermediate form, with definitional eqs in front. *)
      val th_defs = th |> apply_to_thm (to_obj_conv_on_horn ctxt')
                       |> apply_to_thm (Conv.repeat_conv swap_one_eq_to_front)

      (* List of definitions used. *)
      val def_subst = th_defs |> Thm.prems_of |> filter is_meta_eq
                              |> map Logic.dest_equals
      fun print_def_subst (lhs, rhs) =
          writeln ("Apply def " ^ (lhs |> pretty_term ctxt' |> str) ^ " = " ^
                   (rhs |> pretty_term ctxt' |> str))
      val _ = map print_def_subst def_subst

      fun def_subst_fun cond =
          case cond of
              WithItem ("TERM", t) =>
              WithItem ("TERM", fold (fn pair => Term.subst_atomic [pair])
                                     def_subst t)
            | _ => cond

      val th = th_defs |> meta_use_vardefs
                       |> update_name_of_thm th ""
    in
      if null conds andalso mode = MODE_FORWARD andalso
         Property.can_add_property_update th thy then
        Property.add_property_update_gnrc th gnrc
      else let
        fun is_term_cond cond =
            case cond of WithItem ("TERM", _) => true | _ => false

        fun extract_term_cond cond =
            case cond of
                WithItem ("TERM", t) => t | _ => raise Fail "extract_term_cond"

        (* Instantiate each element of conds with ctxt', then separate
           into term and other (filter and shadow) conds.
         *)
        val (term_conds, filt_conds) =
            conds |> map (fn cond => cond ctxt')
                  |> filter_split is_term_cond
                  |> apfst (map def_subst_fun)

        (* Get list of assumptions to be obtained from either the
           property table or the wellform table.
         *)
        val ts = map extract_term_cond term_conds
        val side_prems = get_side_prems thy mode ts th
        val side_count = length side_prems
        val th' = th |> post_process_th ctxt' mode side_count ts

        val (assums, concl) =
            th' |> strip_horn' |> apfst (drop side_count)
        val pats = map extract_term_cond term_conds @ assums
        val match_descs = term_conds @ map WithFact assums
        val _ = assert (is_pattern_list pats)
                       "add_basic_prfstep: invalid patterns."
        val _ = assert (length pats > 0 andalso length pats <= 2)
                       "add_basic_prfstep: invalid number of patterns."
      in
        (* Switch two assumptions if necessary. *)
        if length pats = 2 andalso not (is_pattern (hd pats)) then
          let
            val _ = writeln "Switching two patterns."
            val swap_prems_cv = Conv.rewr_conv Drule.swap_prems_eq
            val th'' =
                if length assums = 1 then th'
                else th' |> apply_to_thm (skip_n_conv side_count swap_prems_cv)
                         |> update_name_of_thm th' ""
            val swap_match_descs = [nth match_descs 1, hd match_descs]
            val descs = side_prems @ swap_match_descs @ filt_conds @
                        [GetFact (concl, th'')]
          in
            add_and_print_prfstep_gnrc (name_of_thm th') descs gnrc
          end
        else
          let
            val descs = side_prems @ match_descs @ filt_conds @
                        [GetFact (concl, th')]
          in
            add_and_print_prfstep_gnrc (name_of_thm th') descs gnrc
          end
      end
    end

fun add_forward_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_FORWARD

fun add_forward'_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_FORWARD'

fun add_backward_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_BACKWARD

fun add_backward1_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_BACKWARD1

fun add_backward2_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_BACKWARD2

fun add_resolve_prfstep_cond_gnrc th =
    add_basic_prfstep_cond_gnrc th MODE_RESOLVE

fun add_forward_prfstep_gnrc th = add_forward_prfstep_cond_gnrc th []
fun add_forward'_prfstep_gnrc th = add_forward_prfstep_cond_gnrc th []
fun add_backward_prfstep_gnrc th = add_backward_prfstep_cond_gnrc th []
fun add_backward1_prfstep_gnrc th = add_backward1_prfstep_cond_gnrc th []
fun add_backward2_prfstep_gnrc th = add_backward2_prfstep_cond_gnrc th []
fun add_resolve_prfstep_gnrc th = add_resolve_prfstep_cond_gnrc th []

val add_forward_prfstep_cond =
    Context.theory_map oo add_forward_prfstep_cond_gnrc

val add_forward'_prfstep_cond =
    Context.theory_map oo add_forward'_prfstep_cond_gnrc

val add_backward_prfstep_cond =
    Context.theory_map oo add_backward_prfstep_cond_gnrc

val add_backward1_prfstep_cond =
    Context.theory_map oo add_backward1_prfstep_cond_gnrc

val add_backward2_prfstep_cond =
    Context.theory_map oo add_backward2_prfstep_cond_gnrc

val add_resolve_prfstep_cond =
    Context.theory_map oo add_resolve_prfstep_cond_gnrc

fun add_forward_prfstep th = add_forward_prfstep_cond th []
fun add_forward'_prfstep th = add_forward'_prfstep_cond th []
fun add_backward_prfstep th = add_backward_prfstep_cond th []
fun add_backward1_prfstep th = add_backward1_prfstep_cond th []
fun add_backward2_prfstep th = add_backward2_prfstep_cond th []
fun add_resolve_prfstep th = add_resolve_prfstep_cond th []

fun add_rewrite_eq_rule_cond_gnrc th conds gnrc =
    let
      val th = if is_meta_eq (Thm.concl_of th) then to_obj_eq_th th else th
      val (lhs, _) = th |> concl_of' |> strip_conj |> hd |> dest_eq
    in
      gnrc |> add_forward_prfstep_cond_gnrc th (K (WithTerm lhs) :: conds)
    end

fun add_rewrite_iff_rule_cond_gnrc th conds gnrc =
    let
      val th = if is_meta_eq (Thm.concl_of th) orelse
                  is_eq_term_non_iff (concl_of' th) then to_obj_eq_iff_th th
               else th
      val (lhs, _) = th |> concl_of' |> dest_eq
      val _ = assert (fastype_of lhs = boolT)
                     "add_rewrite_iff: argument not of type bool."

      val ctxt = Context.proof_of gnrc
      val forward_th = th |> equiv_forward_th
      val nforward_th = th |> inv_backward_th
                           |> apply_to_thm (horn_conv try_nn_cancel_cv)
                           |> apply_to_thm (reduce_boolify ctxt)
                           |> update_name_of_thm th "@invbackward"
    in
      gnrc |> add_basic_prfstep_cond_gnrc forward_th MODE_FORWARD' conds
           |> add_basic_prfstep_cond_gnrc nforward_th MODE_FORWARD' conds
    end

fun add_rewrite_rule_cond_gnrc th conds gnrc =
    let
      val th = if is_meta_eq (Thm.concl_of th) then to_obj_eq_th th else th
      val (lhs, _) = th |> concl_of' |> strip_conj |> hd |> dest_eq
    in
      if not unique_bool andalso fastype_of lhs = boolT then
        add_rewrite_iff_rule_cond_gnrc th conds gnrc
      else
        add_rewrite_eq_rule_cond_gnrc th conds gnrc
    end

fun add_rewrite_rule_back_cond_gnrc th conds =
    add_rewrite_rule_cond_gnrc (obj_sym_th th) conds

fun add_rewrite_rule_bidir_cond_gnrc th conds =
    (add_rewrite_rule_cond_gnrc th conds)
        #> add_rewrite_rule_back_cond_gnrc th conds

fun add_rewrite_iff_rule_back_cond_gnrc th conds =
    add_rewrite_iff_rule_cond_gnrc (obj_sym_th th) conds

fun add_rewrite_iff_rule_bidir_cond_gnrc th conds =
    (add_rewrite_iff_rule_cond_gnrc th conds)
        #> add_rewrite_iff_rule_back_cond_gnrc th conds

fun add_rewrite_rule_gnrc th = add_rewrite_rule_cond_gnrc th []
fun add_rewrite_rule_back_gnrc th = add_rewrite_rule_back_cond_gnrc th []
fun add_rewrite_rule_bidir_gnrc th = add_rewrite_rule_bidir_cond_gnrc th []
fun add_rewrite_iff_rule_gnrc th = add_rewrite_iff_rule_cond_gnrc th []
fun add_rewrite_iff_rule_back_gnrc th =
    add_rewrite_iff_rule_back_cond_gnrc th []
fun add_rewrite_iff_rule_bidir_gnrc th =
    add_rewrite_iff_rule_bidir_cond_gnrc th []

val add_rewrite_rule_cond =
    Context.theory_map oo add_rewrite_rule_cond_gnrc

val add_rewrite_rule_back_cond =
    Context.theory_map oo add_rewrite_rule_back_cond_gnrc

val add_rewrite_rule_bidir_cond =
    Context.theory_map oo add_rewrite_rule_bidir_cond_gnrc

val add_rewrite_iff_rule_cond =
    Context.theory_map oo add_rewrite_iff_rule_cond_gnrc

val add_rewrite_iff_rule_back_cond =
    Context.theory_map oo add_rewrite_iff_rule_back_cond_gnrc

val add_rewrite_iff_rule_bidir_cond =
    Context.theory_map oo add_rewrite_iff_rule_bidir_cond_gnrc

fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th
fun add_rewrite_iff_rule th = add_rewrite_iff_rule_cond th []
fun add_rewrite_iff_back_rule th = add_rewrite_iff_rule_back_cond th []
fun add_rewrite_iff_bidir_rule th = add_rewrite_iff_rule_bidir_cond th []

fun add_eval_fun_prfsteps' desc_ths ths thy =
    let
      fun eval_thm_to_str th =
          (name_of_thm th) ^ ": " ^
          (th |> Thm.prop_of |> pretty_term_thy thy |> str)
      val _ = writeln (cat_lines (map eval_thm_to_str desc_ths))
    in
      fold add_prfstep (prfsteps_eval_fun' desc_ths ths) thy
    end

fun add_eval_fun_prfsteps ths = add_eval_fun_prfsteps' ths ths

fun setup_attrib f =
    Attrib.add_del
        (Thm.declaration_attribute (
            fn th => fn gnrc =>
               case gnrc of Context.Theory _ => f th gnrc | _ => gnrc))
        (Thm.declaration_attribute (
            fn _ => fn _ => raise Fail "del_step: not implemented."))

end  (* structure ProofStep_Data. *)
