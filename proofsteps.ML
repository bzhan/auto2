(* Definition of core proof steps (single-step change to proof
   state). Each proofstep is a function taking the index of the
   current box, known facts to consider (either in the current box or
   an ancestor box), and conclusion in the current box, and returns a
   list of updates to the proof status.
 *)
signature PROOFSTEP =
sig
  type pre_filter
  type proofstep_fn
  type proofstep
  type prfstep_filter
  datatype prfstep_descriptor = WithFact of term
                              | WithGoal of term
                              | WithTerm of term
                              | GetFact of term * thm
                              | GetGoal of term * thm
                              | GetResolve of thm
                              | CreateCase of term list * term list
                              | Filter of prfstep_filter
  val string_of_desc: theory -> prfstep_descriptor -> string
  val string_of_descs: theory -> prfstep_descriptor list -> string
  val get_prfstep_fn: proofstep -> proofstep_fn
  val merged_id: RewriteTable.rewrite_type -> box_item list -> box_id
  val get_insts_filt: term list -> box_item list -> RewriteTable.rewrite_type ->
                      prfstep_filter -> id_inst_ths list
  val get_insts: term list -> box_item list -> RewriteTable.rewrite_type ->
                 id_inst_ths list

  (* prfstep_filter *)
  val all_insts: prfstep_filter
  val id_filter: (box_id -> bool) -> prfstep_filter
  val neqt_filter: string -> term -> prfstep_filter
  val neqp_filter: string -> term -> prfstep_filter
  val neq_filter: string -> string -> prfstep_filter
  val order_filter: string -> string -> prfstep_filter
  val order_filter_n: indexname -> indexname -> prfstep_filter
  val size1_filter: string -> prfstep_filter
  val unique_free_filter: string -> prfstep_filter
  val canonical_split_filter: string -> string -> string -> prfstep_filter
  val ac_atomic_filter: string -> string -> prfstep_filter
  val term_neq_filter: string -> string -> string -> prfstep_filter
  val subset_var_filter: string -> string -> prfstep_filter

  (* pre_filter *)
  val no_prereq: pre_filter
  val pat_prereq: term -> pre_filter

  (* First level proofstep writing functions. *)
  val preprocess_thm: term list -> term * thm -> term * thm
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_pats: prfstep_descriptor list -> term list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> (term list * term list) list
  val gen_prfstep: string -> prfstep_descriptor list -> proofstep
  val prfstep_thm: string -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_conv:
      string -> bool -> prfstep_descriptor list -> conv -> proofstep
  val prfstep_rrule: bool -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_two_stage: string -> prfstep_descriptor list -> thm -> proofstep
  val prfstep_thm_fn: string -> prfstep_descriptor list ->
                      (Proof.context -> id_inst_ths -> thm) -> proofstep
  val prfstep_custom:
      string -> prfstep_descriptor list ->
      (id_inst_ths -> Status.status -> Update.raw_update list) -> proofstep
end;

structure ProofStep : PROOFSTEP =
struct

open Box
open Update
open Status

type pre_filter = RewriteTable.rewrite_type -> box_item -> bool
type proofstep_fn = box_item list -> RewriteTable.rewrite_type ->
                    status -> raw_update list
type proofstep = {name: string, filt: pre_filter list, func: proofstep_fn}
type prfstep_filter = RewriteTable.rewrite_table -> id_inst -> bool
datatype prfstep_descriptor = WithFact of term
                            | WithGoal of term
                            | WithTerm of term
                            | GetFact of term * thm
                            | GetGoal of term * thm
                            | GetResolve of thm
                            | CreateCase of term list * term list
                            | Filter of prfstep_filter

fun string_of_desc thy desc =
    let val print = str o pretty_term_thy thy in
      case desc of
          WithFact t => "WithFact " ^ (print t)
        | WithGoal t => "WithGoal " ^ (print t)
        | WithTerm t => "WithTerm " ^ (print t)
        | GetFact (t, th) => "GetFact (" ^ (print t) ^ ", " ^
                             (name_of_thm th) ^ ")"
        | GetGoal (t, th) => "GetGoal (" ^ (print t) ^ ", " ^
                             (name_of_thm th) ^ ")"
        | GetResolve th => "GetResolve " ^ (name_of_thm th)
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
      val {lat, ...} = RewriteTable.table_of_rewrite_type rtype
      fun merge items =
          case items of
              [] => []
            | {id, ...} :: items' => BoxID.merge_boxes lat (id, merge items')
    in
      merge items
    end

(* Get ordered matchings between "pats" and "trms". *)
fun get_insts_filt pats items rtype filt =
    if length pats <> length items then
      raise AUTO2 "get_insts_filt: wrong number of arguments"
    else if exists has_vars (map get_fact items) then [] else
    let
      val trms = map get_fact items
      val pairs = map (pair false) (pats ~~ trms)
      val id = merged_id rtype items
      val tbl = RewriteTable.table_of_rewrite_type rtype
      val insts = (fo_table_match_list id tbl pairs)
                      |> filter (filt tbl o fst)
                      |> RewriteTable.replace_id_for_type rtype
      val items_th = map get_thm items
      fun get_prev_ths (inst, ths) =
          (inst, map elim_eq_thm (map meta_sym ths ~~ items_th))
    in
      map get_prev_ths insts
    end

fun get_insts pats items rtype =
    get_insts_filt pats items rtype (fn _ => fn _ => true)

(* prfstep_filter *)

val all_insts = fn _ => fn _ => true
fun id_filter f _ (id, _) = f id
fun neqt_filter s1 t2 tbl (id, inst) =
    not (RewriteTable.is_equiv id tbl (lookup_inst inst s1, t2))
fun neqp_filter s1 p2 tbl (id, inst) =
    (fo_table_match_list id tbl [(false, (p2, lookup_inst inst s1))])
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
fun term_neq_filter fnm s1 s2 tbl (id, inst) =
    case lookup_ac_data (RewriteTable.theory_of tbl) fnm of
        NONE => raise AUTO2 "term_neq_filter: ac_itm not found"
      | SOME ac_itm =>
        let
          val (A, B) = (lookup_inst inst s1, lookup_inst inst s2)
          val Bs = ACUtil.dest_ac ac_itm B
        in
          not (exists (fn B' => RewriteTable.is_equiv id tbl (A, B')) Bs)
        end
fun subset_var_filter s1 s2 _ (_, inst) =
    subset (op aconv) (map Var (Term.add_vars (lookup_inst inst s1) []),
                       map Var (Term.add_vars (lookup_inst inst s2) []))

(* pre_filter *)

val no_prereq = fn _ => fn _ => true
fun pat_prereq pat rtype item =
    let
      val pat' = if is_eq_term' pat then @{term_pat "TERM ?x"} else pat
      val rtype' = RewriteTable.single_of_rewrite_type rtype
    in
      case get_insts [pat'] [item] rtype' of
          [] => false | _ => true
    end

(* First level proofstep writing functions. *)

(* Preprocessing a theorem: write theorem th into the form [hyps] ==>
   false, match pats @ [~ pat_r] (with prop type) with hyps. Finally
   convert the ending of theorem from hyp_n -> false to ~hyp_n. The
   result is a theorem [pats] ==> pat_r.
 *)
fun preprocess_thm pats (pat_r, th) =
    let
      val pat_r_false = pat_r aconv @{prop "False"}
      val pats' = filter_out is_Term pats
      val pat_r' = if is_simp_eq_term' pat_r then from_simp_eq_term' pat_r
                   else pat_r
      val prop_pats = if pat_r_false then pats' else pats' @ [get_neg' pat_r']
      val th' = rewrite_thm_to_contra_form th
      val prems_th' = Thm.prems_of th'
    in
      if eq_set (op aconv) (prop_pats, prems_th') then
        let
          val th'' = th' |> rotate_prems_conv_thm prop_pats
                         |> not pat_r_false ? rewrite_thm_from_contra_form
                         |> is_simp_eq_term' pat_r ? to_simp_eq
          val _ = if pat_r aconv (Thm.concl_of th'') then () else
                  raise AUTO2CT ("preprocess_thm: conclusion mismatch",
                                 map (cert_thy (Thm.theory_of_thm th))
                                     [pat_r, Thm.prop_of th''])
        in
          (pat_r, th'')
        end
      else
        let
          val thy = Thm.theory_of_thm th
          val _ = tracing ("Given in proofstep: " ^
                           (prop_pats |> pretty_terms_thy thy |> str) ^
                           "\nIn theorem: " ^
                           (prems_th' |> pretty_terms_thy thy |> str))
        in
          raise AUTO2 "preprocess_thm: premises do not agree."
        end
    end

fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val inst_new = Envir.subst_term inst pat_r
      val ths' = ths |> filter_out (is_Term o Thm.prop_of)
      val th' = th |> subst_thm ctxt inst |> fold Thm.elim_implies ths'
      val _ = if inst_new aconv (Thm.prop_of th') then () else
              raise AUTO2CT ("apply_pat_r: conclusion mismatch",
                             map (cert ctxt) [inst_new, Thm.prop_of th'])
    in
      th'
    end

fun retrieve_pats descs =
    let
      fun retrieve_pat desc =
          case desc of
              WithFact pat => [HOLogic.mk_Trueprop pat]
            | WithGoal pat => [HOLogic.mk_Trueprop (get_neg pat)]
            | WithTerm t => [Logic.mk_term t]
            | _ => []
    in
      maps retrieve_pat descs
    end

fun retrieve_pats_r descs =
    let
      fun retrieve_pat_r desc =
          case desc of
              GetFact (pat_r, th) => [(HOLogic.mk_Trueprop pat_r, th)]
            | GetGoal (pat_r, th) => [(HOLogic.mk_Trueprop (get_neg pat_r), th)]
            | GetResolve th => [(@{prop "False"}, th)]
            | _ => []
    in
      maps retrieve_pat_r descs
    end

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

(* Parameters: patterns for facts, optional pattern for conclusion,
   patterns for list of new facts.
 *)
fun gen_prfstep name descs =
    let
      val pats = retrieve_pats descs
      val pats_r = retrieve_pats_r descs |> map (preprocess_thm pats)
      val filt = retrieve_filts descs
      val cases = retrieve_cases descs

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
            if length ths = 1 then thm_update (id, the_single ths)
            else AddItems {id = id, raw_items = map Fact ths}
          end

      fun pat_updts ctxt insts =
          if length pats_r = 0 then [] else map (pats_r_to_update ctxt) insts

      fun case_to_update ((id, inst), _) (assums, concls) =
          AddBoxes {id = id, freevars = [],
                    assums = map (Envir.subst_term inst) assums,
                    concls = map (Envir.subst_term inst) concls,
                    cb = null_callback}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases
      fun case_updts insts = maps cases_to_update insts

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
          in
            pat_updts ctxt insts @ case_updts insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_thm name descs th =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype _ =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt ((id, _), ths) =
                thm_update (id, ths MRS th)
                handle THM (err, _, _) =>
                       raise AUTO2CT (name ^ ": MRS failed with message " ^
                                      err, map Thm.cprop_of ths)
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_conv name is_simp descs cv =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1 andalso is_Term (the_single pats))
                     "prfstep_conv: should have exactly one term pattern."
      val filt = retrieve_filts descs
      fun prfstep items rtype {ctxt, ...} =
          let
            val tbl = RewriteTable.table_of_rewrite_type rtype
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt ((id, _), ths) =
                let
                  val ct = ths |> the_single |> Thm.prop_of |> Logic.dest_term
                               |> cert ctxt
                  val eq_th = (Conv.try_conv cv) ct
                  val (lhs, rhs) = Logic.dest_equals (Thm.prop_of eq_th)
                in
                  if lhs aconv rhs then
                    raise AUTO2CT (name ^ ": cv failed.", [ct])
                  else if RewriteTable.is_equiv id tbl (lhs, rhs) then []
                  else [thm_update (
                           id, eq_th |> to_obj_eq |> is_simp ? to_simp_eq)]
                end
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_rrule is_simp descs rrule =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1 andalso is_Term (the_single pats))
                     "prfstep_rrule: should have exactly one term pattern."
      val pat = Logic.dest_term (the_single pats)
      val (lhs, rhs) =
          HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of rrule))
      val name = name_of_thm rrule
      val lhs_vars = map Var (Term.add_vars lhs [])
      val rhs_vars = map Var (Term.add_vars rhs [])
      val err_new_var =
          "prfstep_rrule: new schematic variables on the rewritten side."
    in
      if Term.aconv_untyped (pat, lhs) then
        let
          val _ = assert (subset (op aconv) (rhs_vars, lhs_vars)) err_new_var
        in
          prfstep_conv name is_simp descs (rewr_obj_eq rrule)
        end
      else if Term.aconv_untyped (pat, rhs) then
        let
          val _ = assert (subset (op aconv) (lhs_vars, rhs_vars)) err_new_var
        in
          prfstep_conv (name ^ "@sym") is_simp descs
                       (rewr_obj_eq (obj_sym rrule))
        end
      else raise AUTO2CT (
          "prfstep_rrule: pattern does not equal either side of rrule.",
          [Thm.cprop_of rrule])
    end

(* pat_r produces a trivial statement, which together with the item
   matching the main pattern are matched with the hypotheses of th2 to
   produce the final result.
 *)
fun prfstep_two_stage name descs th2 =
    let
      val pats = retrieve_pats descs
      val _ = assert (length pats = 1)
                     "prfstep_two_stage: should have one pattern."
      val pats_r = retrieve_pats_r descs |> map (preprocess_thm [])
      val _ = assert (length pats_r = 1)
                     "prfstep_two_stage: should have one result."
      val pat_r = the_single pats_r
      val filt = retrieve_filts descs

      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt (instsp as (id, _), ths) =
                let
                  val th = apply_pat_r ctxt (instsp, []) pat_r
                in
                  thm_update (id, (ths @ [th]) MRS th2)
                end
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_thm_fn name descs thm_fn =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype {ctxt, ...} =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt (inst_th as ((id, _), _)) =
                thm_update (id, thm_fn ctxt inst_th)
          in
            map inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

fun prfstep_custom name descs updt_fn =
    let
      val pats = retrieve_pats descs
      val filt = retrieve_filts descs
      fun prfstep items rtype st =
          let
            val insts = get_insts_filt pats items rtype filt
            fun inst_to_updt inst_th = updt_fn inst_th st
          in
            maps inst_to_updt insts
          end
    in
      {name = name, filt = map pat_prereq pats, func = prfstep}
    end

end  (* structure ProofStep *)

open ProofStep

(* Table of proofsteps, categorized by type. *)
datatype proofstep_table
  = ProofStepTable of {
    step_a: proofstep list,
    step_aa: proofstep list,
    fixed_sc: int Symtab.table}

val empty_proofstep_table =
    ProofStepTable {step_a = [], step_aa = [], fixed_sc = Symtab.empty}

fun merge_table (ProofStepTable {step_a = a1, step_aa = aa1, fixed_sc = sc1},
                 ProofStepTable {step_a = a2, step_aa = aa2, fixed_sc = sc2}) =
    ProofStepTable {step_a = merge pointer_eq (a1, a2),
                    step_aa = merge pointer_eq (aa1, aa2),
                    fixed_sc = Symtab.merge (op =) (sc1, sc2)}

(* Table associated to the current theory. *)
structure ProofStepData =
Theory_Data (
  type T = proofstep_table;
  val empty = empty_proofstep_table;
  val extend = I;
  val merge = merge_table
)

signature PROOFSTEP_DATA =
sig
  val add_prfstep: proofstep -> theory -> theory
  val del_prfstep: string -> theory -> theory
  val del_prfstep_thm: thm -> theory -> theory
  val add_fixed_sc: string * int -> theory -> theory
  val get_step_a: theory -> proofstep list
  val get_step_aa: theory -> proofstep list
  val get_fixed_sc: theory -> string -> int option

  val add_gen_prfstep: string * prfstep_descriptor list -> theory -> theory
  val add_prfstep_thm:
      string * prfstep_descriptor list * thm -> theory -> theory
  val add_prfstep_conv:
      string * prfstep_descriptor list * conv -> theory -> theory
  val add_prfstep_two_stage:
      string * prfstep_descriptor list * thm -> theory -> theory
  val add_prfstep_thm_fn:
      string * prfstep_descriptor list * (Proof.context -> id_inst_ths -> thm)
      -> theory -> theory
  val add_prfstep_rewrite: prfstep_descriptor list * thm -> theory -> theory
  val add_prfstep_simp: prfstep_descriptor list * thm -> theory -> theory

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
  val add_simp_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_simp_rule: thm -> theory -> theory
end;

structure ProofStep_Data : PROOFSTEP_DATA =
struct

fun add_prfstep (prfstep as {filt, ...}) = ProofStepData.map (
      fn ProofStepTable {step_a, step_aa, fixed_sc} =>
         case length filt of
             1 => ProofStepTable {step_a = prfstep :: step_a, step_aa = step_aa,
                                  fixed_sc = fixed_sc}
           | 2 => ProofStepTable {step_a = step_a, step_aa = prfstep :: step_aa,
                                  fixed_sc = fixed_sc}
           | _ => raise AUTO2 "add_proofstep: need 1 or 2 patterns.")

(* Deleting a proofstep. For string inputs, try adding theory
   name. For theorem inputs, try all @-suffixes.
 *)
fun del_prfstep_pred pred = ProofStepData.map (
      fn ProofStepTable {step_a, step_aa, fixed_sc} =>
         let
           val steps = (step_a @ step_aa) |> filter (pred o #name)
         in
           if length steps = 0 then raise AUTO2 "del_prfstep: not found" else
           let
             val _ = map (fn step => tracing ("Delete " ^ (#name step))) steps
           in
             ProofStepTable {
               step_a = step_a |> filter_out (pred o #name),
               step_aa = step_aa |> filter_out (pred o #name),
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
      fn ProofStepTable {step_a, step_aa, fixed_sc} =>
         case find_first (equal nm o #name) (step_a @ step_aa) of
             NONE => raise AUTO2 ("add_fixed_sc: not found " ^ nm)
           | _ => ProofStepTable {
                   step_a = step_a, step_aa = step_aa,
                   fixed_sc = fixed_sc |> Symtab.update_new (nm, sc)})

fun get_step_a thy =
    let val ProofStepTable {step_a, ...} = ProofStepData.get thy in step_a end
fun get_step_aa thy =
    let val ProofStepTable {step_aa, ...} = ProofStepData.get thy in step_aa end
fun get_fixed_sc thy nm =
    let val ProofStepTable {fixed_sc, ...} = ProofStepData.get thy in
      Symtab.lookup fixed_sc nm
    end

fun add_gen_prfstep (name, descs) = add_prfstep (gen_prfstep name descs)
fun add_prfstep_thm (name, descs, th) = add_prfstep (prfstep_thm name descs th)
fun add_prfstep_conv (name, descs, cv) =
    add_prfstep (prfstep_conv name false descs cv)
fun add_prfstep_two_stage (name, descs, th2) =
    add_prfstep (prfstep_two_stage name descs th2)
fun add_prfstep_thm_fn (name, descs, thm_fn) =
    add_prfstep (prfstep_thm_fn name descs thm_fn)
fun add_prfstep_rewrite (descs, rrule) =
    add_prfstep (prfstep_rrule false descs rrule)
fun add_prfstep_simp (descs, rrule) =
    add_prfstep (prfstep_rrule true descs rrule)

(* Constructing conditional prfstep_descriptors. *)

type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor
fun with_term str ctxt =
    WithTerm (Proof_Context.read_term_pattern ctxt str)
fun with_cond str ctxt =
    let
      val cond = Proof_Context.read_term_pattern ctxt str
      val (lhs, rhs) = cond |> HOLogic.dest_not |> HOLogic.dest_eq
                       handle TERM _ =>
                              raise AUTO2 "with_cond: not an inequality."
      val _ = assert (is_Var lhs) "with_cond: left side should be a variable."
      val ((nm, idx), _) = dest_Var lhs
      val _ = assert (idx = 0) "with_cond: cannot handle nonzero index."
    in
      if is_Var rhs then
        let
          val ((nm', idx'), _) = dest_Var rhs
          val _ = assert (idx' = 0) "with_cond: cannot handle nonzero index."
          val _ = tracing ("neq_filter on " ^ nm ^ " and " ^ nm')
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
      (* First convert to obj anything after two meta imps. *)
      val ctxt = Proof_Context.init_global thy
      val th' = if Thm.nprems_of th > 2 then
                  th |> apply_to_thm (
                    Conv.arg_conv (Conv.arg_conv (to_obj_conv ctxt)))
                     |> Thm.put_name_hint (name_of_thm th ^ "@short")
                else th
      val (assums, concl) = strip_horn' th'
      val descs = (map WithFact assums @ [GetFact (concl, th')]) @
                  (process_conds th' thy conds)
    in
      add_and_print_prfstep (name_of_thm th') descs thy
    end

fun add_backward_prfstep_cond th conds thy =
    let
      val (assums, concl) = strip_horn' th
      val _ = assert (length assums = 1)
                     "Theorem should have exactly one assumption."
      val descs = [WithGoal concl, GetGoal (the_single assums, th)] @
                  (process_conds th thy conds)
    in
      add_and_print_prfstep ((name_of_thm th) ^ "@back") descs thy
    end

fun add_backward1_prfstep_cond th conds thy =
    let
      val (assums, concl) = strip_horn' th
      val _ = assert (length assums = 2)
                     "Theorem should have exactly two assumptions."
      val (assum1, assum2) = the_pair assums
      val descs = [WithFact assum2, WithGoal concl, GetGoal (assum1, th)] @
                  (process_conds th thy conds)
    in
      add_and_print_prfstep ((name_of_thm th) ^ "@back1") descs thy
    end

fun add_backward2_prfstep_cond th conds thy =
    let
      val (assums, concl) = strip_horn' th
      val _ = assert (length assums = 2)
                     "Theorem should have exactly two assumptions."
      val (assum1, assum2) = the_pair assums
      val descs = [WithFact assum1, WithGoal concl, GetGoal (assum2, th)] @
                  (process_conds th thy conds)
    in
      add_and_print_prfstep ((name_of_thm th) ^ "@back2") descs thy
    end

fun add_resolve_prfstep_cond th conds thy =
    let
      val (assums, concl) = strip_horn' th
      val _ = assert (length assums <= 1)
                     "Theorem should have at most one assumption."
      val descs = (map WithFact assums @ [WithGoal concl, GetResolve th]) @
                  (process_conds th thy conds)
    in
      add_and_print_prfstep ((name_of_thm th) ^ "@res") descs thy
    end

fun add_known_fact th =
    add_forward_prfstep_cond
        th [K (WithTerm (th |> Thm.prop_of |> HOLogic.dest_Trueprop))]
fun add_forward_prfstep th = add_forward_prfstep_cond th []
fun add_backward_prfstep th = add_backward_prfstep_cond th []
fun add_backward1_prfstep th = add_backward1_prfstep_cond th []
fun add_backward2_prfstep th = add_backward2_prfstep_cond th []
fun add_resolve_prfstep th = add_resolve_prfstep_cond th []

fun add_rewrite_rule_cond th conds thy =
    let
      val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th))
      val descs = [WithTerm lhs] @ (process_conds th thy conds)
      val _ = writeln ((name_of_thm th) ^ "\n" ^ (string_of_descs thy descs) ^
                       "\n = " ^ (pretty_term_thy thy rhs |> str))
    in
      add_prfstep_rewrite (descs, th) thy
    end

fun add_rewrite_rule_back_cond th conds thy =
    let
      val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th))
      val descs = [WithTerm rhs] @ (process_conds th thy conds)
      val _ = writeln ((name_of_thm th) ^ "\n" ^ (string_of_descs thy descs) ^
                       "\n = " ^ (pretty_term_thy thy lhs |> str))
    in
      add_prfstep_rewrite (descs, th) thy
    end

fun add_simp_rule_cond th conds thy =
    let
      val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th))
      val descs = [WithTerm lhs] @ (process_conds th thy conds)
      val _ = writeln ((name_of_thm th) ^ "\n" ^ (string_of_descs thy descs) ^
                       "\n simp= " ^ (pretty_term_thy thy rhs |> str))
    in
      add_prfstep_simp (descs, th) thy
    end

fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th
fun add_rewrite_rule_bidir_cond th conds =
    add_rewrite_rule_cond th conds #> add_rewrite_rule_back_cond th conds
fun add_simp_rule th = add_simp_rule_cond th []

end  (* structure ProofStep_Data. *)

open ProofStep_Data

type mut_update = box_id * state_val -> RewriteTable.rewrite_type -> box_item ->
                  Status.status -> (box_id * state_val) list
type mut_concl = box_id * state_val -> Status.status -> Update.raw_update list
type mut_eq_better = state_val -> state_val -> bool

(* Table of proofsteps on mutable states. *)
datatype mut_step_table
  = MutStepTable of {
    step_updt: mut_update Symtab.table,
    step_concl: mut_concl Symtab.table,
    eq_better: mut_eq_better Symtab.table}

val empty_mut_step_table =
    MutStepTable {step_updt = Symtab.empty, step_concl = Symtab.empty,
                  eq_better = Symtab.empty}

fun merge_mut_step_table (
  MutStepTable {step_updt = u1, step_concl = c1, eq_better = e1},
  MutStepTable {step_updt = u2, step_concl = c2, eq_better = e2}) =
    MutStepTable {step_updt = Symtab.merge pointer_eq (u1, u2),
                  step_concl = Symtab.merge pointer_eq (c1, c2),
                  eq_better = Symtab.merge pointer_eq (e1, e2)}

structure MutStepData =
Theory_Data (
  type T = mut_step_table;
  val empty = empty_mut_step_table;
  val extend = I;
  val merge = merge_mut_step_table
)

(* Proofsteps on mutable states. *)
signature MUT_PROOFSTEP =
sig
  val add_mut_update: string * mut_update -> theory -> theory
  val add_mut_concl: string * mut_concl -> theory -> theory
  val add_mut_eq_better: string * mut_eq_better -> theory -> theory
  val get_mut_update: theory -> string -> mut_update
  val get_mut_concl: theory -> string -> mut_concl
  val get_mut_eq_better: theory -> string -> mut_eq_better
  val compare_eq_better: Status.status -> mut_eq_better -> box_id * state_val ->
                         box_id * state_val -> bool
end;

structure Mut_ProofStep : MUT_PROOFSTEP =
struct

open Status

fun add_mut_update (s, updt_fn) = MutStepData.map (
      fn MutStepTable {step_updt, step_concl, eq_better} =>
         MutStepTable {step_updt = step_updt |> Symtab.update_new (s, updt_fn),
                       step_concl = step_concl, eq_better = eq_better})

fun add_mut_concl (s, concl_fn) = MutStepData.map (
      fn MutStepTable {step_updt, step_concl, eq_better} =>
         MutStepTable {
           step_updt = step_updt, eq_better = eq_better,
           step_concl = step_concl |> Symtab.update_new (s, concl_fn)})

fun add_mut_eq_better (s, eq_better_fn) = MutStepData.map (
      fn MutStepTable {step_updt, step_concl, eq_better} =>
         MutStepTable {
           step_updt = step_updt, step_concl = step_concl,
           eq_better = eq_better |> Symtab.update_new (s, eq_better_fn)})

fun get_mut_update thy s =
    let val MutStepTable {step_updt, ...} = MutStepData.get thy in
      case Symtab.lookup step_updt s of
          NONE => raise AUTO2 "get_mut_update: not found"
        | SOME updt_fn => updt_fn
    end

fun get_mut_concl thy s =
    let val MutStepTable {step_concl, ...} = MutStepData.get thy in
      case Symtab.lookup step_concl s of
          NONE => raise AUTO2 "get_mut_concl: not found"
        | SOME concl_fn => concl_fn
    end

fun get_mut_eq_better thy s =
    let val MutStepTable {eq_better, ...} = MutStepData.get thy in
      case Symtab.lookup eq_better s of
          NONE => raise AUTO2 "get_mut_eq_better: not found"
        | SOME eq_better_fn => eq_better_fn
    end

(* Whether (id1, sval1) is equal or better than (id2, sval2). *)
fun compare_eq_better st eq_better_fn (id1, sval1) (id2, sval2) =
    if Status.is_eq_ancestor st id1 id2 then eq_better_fn sval1 sval2 else false

end;  (* structure Mut_ProofStep *)

open Mut_ProofStep
