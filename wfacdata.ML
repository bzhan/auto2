(* Associative-commutative operations on wellformed terms. *)

type wfac_inst_info = {
  cfhead: cterm, assoc_l_cv: wfconv, assoc_r_cv: wfconv}

(* Generator for wfac_inst_info. *)
type wfac_info = theory -> term -> wfac_inst_info option

(* Register of generators of wfac_inst_info. *)
structure WfACData =
Theory_Data (
  type T = wfac_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

type wfac_info_constr = {
  assoc_l_th: thm,
  assoc_r_th: thm
}

(* Algebraic manipulations. *)
structure AlgData =
Theory_Data (
  type T = (thm -> (term list * wfconv) option) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

(* Under each predicate is a list of predicates it shadows. *)
structure AlgShadowData =
Theory_Data (
  type T = (term list) Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  val merge = Termtab.merge_list (op aconv)
)

type alg_inst_info = box_id * (term * term list * wfconv)

structure AlgInstData =
Proof_Data (
  type T = alg_inst_info list;
  fun init _ = [];
)

signature WF_ACUTIL =
sig
  val inst_ac_info: theory -> term -> wfac_info_constr -> wfac_inst_info option
  val add_wf_ac_data: string * wfac_info -> theory -> theory
  val find_inst_ac_info: theory -> term -> wfac_inst_info option
  val head_agrees: wfac_inst_info -> term -> bool
  val constr_ac_info: wfac_info_constr -> wfac_info
  val normalize_assoc_gen: bool -> wfac_inst_info -> wfconv
  val normalize_assoc_l: wfac_inst_info -> wfconv
  val normalize_assoc_r: wfac_inst_info -> wfconv

  val add_alg_data:
      string * (thm -> (term list * wfconv) option) -> theory -> theory
  val lookup_alg_inst_info: Proof.context -> term -> alg_inst_info list
  val add_alg_shadow_data: term * term -> theory -> theory
  val alg_inst_info_better:
      BoxID.box_lattice -> Proof.context -> box_id * (term * 'a * 'b) ->
      box_id * (term * 'a * 'b) -> bool
  val add_alg_inst_info:
      BoxID.box_lattice -> box_id * thm -> Proof.context -> Proof.context
end;

functor WfACUtil(Base:UTIL_BASE) : WF_ACUTIL =
struct

structure UtilLogic = UtilLogic(Base)
structure WfTerm = WfTerm(Base)
open Base
open UtilLogic
fun (wfcv1 then_wfconv wfcv2) = WfTerm.then_wfconv (wfcv1, wfcv2)

(* Instantiate an ac_info for the given term. *)
fun inst_ac_info thy t {assoc_l_th, assoc_r_th} =
    let
      val fhead = dest_binop_head t

      (* Get pattern for the left side. *)
      val pat_l = assoc_l_th |> concl_of' |> dest_arg1 |> dest_arg1
      val pat_head = dest_binop_head pat_l
      val cfhead = cert_thy thy fhead
      val inst = pattern_fo_match_thy thy (pat_head, fhead)
      val assoc_l_th' = subst_thm_thy thy inst assoc_l_th
      val assoc_r_th' = subst_thm_thy thy inst assoc_r_th
    in
      SOME {cfhead = cfhead,
            assoc_l_cv = WfTerm.rewr_obj_eq [fhead] assoc_l_th',
            assoc_r_cv = WfTerm.rewr_obj_eq [fhead] assoc_r_th'}
    end
    handle Pattern.MATCH => NONE
         | AUTO2 "dest_binop: invalid input" => NONE

fun add_wf_ac_data (nm, info) thy =
    WfACData.map (Symtab.update_new (nm, info)) thy
    handle Symtab.DUP _ => raise AUTO2 "add_wf_ac_data: info already exists."

fun find_inst_ac_info thy t =
    let
      val data = Symtab.dest (WfACData.get thy)
      fun try_inst (_, f) = f thy t
    in
      get_first try_inst data
    end

fun head_agrees {cfhead, ...} = is_head (Thm.term_of cfhead)

fun constr_ac_info constr thy t =
    inst_ac_info thy t constr

fun normalize_assoc_gen assoc_r ac_info wft =
    let
      val {assoc_l_cv, assoc_r_cv, ...} = ac_info
      val assoc_cv = if assoc_r then assoc_r_cv else assoc_l_cv

      (* First rewrite into form a * (...) for assoc_r = true, or
         (...) * a for assoc_r = false, then rewrite the remaining
         parts.
       *)
      fun normalize wft =
          if head_agrees ac_info (WfTerm.term_of wft) then
            ((WfTerm.repeat_conv assoc_cv)
                 then_wfconv (if assoc_r then WfTerm.arg_conv normalize
                              else WfTerm.arg1_conv normalize)) wft
          else
            WfTerm.all_conv wft
    in
      normalize wft
    end

val normalize_assoc_l = normalize_assoc_gen false
val normalize_assoc_r = normalize_assoc_gen true

(* Algebraic manipulations. *)

fun add_alg_data (nm, info) thy =
    AlgData.map (Symtab.update_new (nm, info)) thy
    handle Symtab.DUP _ => raise AUTO2 "add_alg_data: info already exists."

(* Returns the list of alg_inst_infos that is about structure G. *)
fun lookup_alg_inst_info ctxt G =
    filter (fn (_, (prop, _, _)) => dest_arg prop aconv G)
           (AlgInstData.get ctxt)

fun add_alg_shadow_data (t1, t2) =
    AlgShadowData.map (Termtab.insert_list (op aconv) (t1, t2))

(* Determine whether t1 shadows t2. *)
fun lookup_alg_shadow_data (t1, t2) thy =
    let
      val data = AlgShadowData.get thy
      val t1_shadows = Termtab.lookup_list data t1
    in
      member (op aconv) t1_shadows t2
    end

(* Whether the first alg_inst_info is able to shadow the
   second. Currently, we allow shadowing only if prop = prop' and id
   is an eq_ancestor of id'.
 *)
fun alg_inst_info_better lat ctxt (id, (prop, _, _)) (id', (prop', _, _)) =
    if not (BoxID.is_eq_ancestor lat id id') then false
    else if prop aconv prop' then true
    else let
      val thy = Proof_Context.theory_of ctxt
      val (f1, G1) = Term.dest_comb prop
      val (f2, G2) = Term.dest_comb prop'
    in
      G1 aconv G2 andalso lookup_alg_shadow_data (f1, f2) thy
    end

(* Given the (id, th) pair, instantiate wfconvs using theory data, and
   add them to context data.
 *)
fun add_alg_inst_info lat (id, th) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val alg_data = (AlgData.get thy) |> Symtab.dest |> map snd
      val inst_infos = maps (fn f => the_list (f th)) alg_data

      fun info_map inst_info infos =
          let
            val (fheads, wfcv) = inst_info
            val new_info = (id, (prop_of' th, fheads, wfcv))
            val comp = alg_inst_info_better lat ctxt
          in
            if exists (fn info => comp info new_info) infos then infos
            else infos |> filter_out (comp new_info)
                       |> cons new_info
          end

      fun add_inst_info inst_info ctxt =
          AlgInstData.map (info_map inst_info) ctxt
    in
      fold add_inst_info inst_infos ctxt
    end

end  (* structure WfACUtil. *)
