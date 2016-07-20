(* Normalizing a given theorem. *)

type normalizer = Proof.context -> raw_item -> raw_item list

(* Keeps list of normalizers. *)
structure NormData =
Theory_Data (
  type T = normalizer Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

signature NORMALIZER =
sig
  val add_normalizer: string * normalizer -> theory -> theory
  val add_th_normalizer:
      string * (Proof.context -> thm -> thm list) -> theory -> theory
  val add_eq_th_normalizer: thm -> theory -> theory
  val get_normalizers: theory -> (string * normalizer) list
  val normalize: Proof.context -> raw_item -> raw_item list
end;

structure Normalizer : NORMALIZER =
struct

fun add_normalizer (nm, norm_fun) =
    NormData.map (Symtab.update_new (nm, norm_fun))

(* Apply norm_fun: thm -> thm list to any PROP item. *)
fun th_normalizer norm_fun ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if ty_str = "PROP" then
          map Update.thm_to_ritem (norm_fun ctxt th)
        else [ritem]

fun add_th_normalizer (nm, norm_fun) =
    add_normalizer (nm, th_normalizer norm_fun)

fun eq_th_normalizer eq_th ctxt ritem =
    case ritem of
        Handler _ => [ritem]
      | Fact (ty_str, _, th) =>
        if member (op =) ["PROP", "EQ", "PROPERTY"] ty_str then
          [Update.thm_to_ritem (apply_to_thm' (rewr_obj_eq_top ctxt eq_th) th)]
        else [ritem]

fun add_eq_th_normalizer eq_th thy =
    let
      val _ = writeln ("Normalizing using equation " ^
                       (pretty_term_thy thy (Thm.prop_of eq_th) |> str))
    in
      add_normalizer (name_of_thm eq_th, eq_th_normalizer eq_th) thy
    end

fun get_normalizers thy = Symtab.dest (NormData.get thy)

fun normalize ctxt ritem =
    let
      val norms = get_normalizers (Proof_Context.theory_of ctxt)
      fun apply_norm (_, norm_fun) ritems = maps (norm_fun ctxt) ritems
      val norm_once = fold apply_norm norms [ritem]
    in
      case norm_once of
          [ritem'] => if eq_ritem (ritem, ritem') then [ritem']
                      else normalize ctxt ritem'
        | _ => maps (normalize ctxt) norm_once
    end

end  (* structure Normalizer. *)

open Normalizer
