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
  val get_normalizers: theory -> (string * normalizer) list
  val normalize: Proof.context -> raw_item -> raw_item list
  val normalize_keep: Proof.context -> raw_item -> raw_item list
end;

functor Normalizer(Base:UTIL_BASE) : NORMALIZER =
struct

structure UtilLogic = UtilLogic(Base)
structure BoxItem = BoxItem(Base)
structure Update = Update(Base)
open UtilLogic

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

fun get_normalizers thy = Symtab.dest (NormData.get thy)

fun normalize ctxt ritem =
    let
      val norms = get_normalizers (Proof_Context.theory_of ctxt)
      fun apply_norm (_, norm_fun) ritems = maps (norm_fun ctxt) ritems
      val norm_once = fold apply_norm norms [ritem]
    in
      case norm_once of
          [ritem'] => if BoxItem.eq_ritem (ritem, ritem') then [ritem']
                      else normalize ctxt ritem'
        | _ => maps (normalize ctxt) norm_once
    end

(* Perform normalization, but keep the original ritem. *)
fun normalize_keep ctxt ritem =
    let
      val norm_ritems = normalize ctxt ritem
    in
      if length norm_ritems = 1 then norm_ritems
      else ritem :: norm_ritems
    end

end  (* structure Normalizer. *)
