(* Definition of scripts. *)

infixr 0 THEN
infixr 1 WITH

signature SCRIPT =
sig
  datatype script
    = Script_Task of {vars: term list, assums: term list, concls: term list,
                      subs: script list, cb: Update.resolve_callback,
                      end_vars: term list}
    | Script_Info of {prfstep: proofstep, source: (string * term) list,
                      end_vars: term list}
  type scripts = script list
  type pre_scripts = Proof.context -> scripts
  val no_script: pre_scripts
  val get_end_vars: scripts -> term list
  val get_all_vars: scripts -> term list
  val CASE: string -> pre_scripts
  val OBTAIN: string -> pre_scripts
  val THEN: pre_scripts * pre_scripts -> pre_scripts
  val WITH: pre_scripts * pre_scripts -> pre_scripts
end

structure Script : SCRIPT =
struct

datatype script
  = Script_Task of {vars: term list, assums: term list, concls: term list,
                    subs: script list, cb: Update.resolve_callback,
                    end_vars: term list}
  | Script_Info of {prfstep: proofstep, source: (string * term) list,
                    end_vars: term list}
type scripts = script list
type pre_scripts = Proof.context -> scripts

val no_script = K []

fun get_end_vars_single s =
    case s of
        Script_Task {end_vars, ...} => end_vars
      | Script_Info {end_vars, ...} => end_vars

fun get_end_vars scrpt = maps get_end_vars_single scrpt

fun get_all_vars_single s =
    case s of
        Script_Task {vars, subs, end_vars, ...} =>
        vars @ end_vars @ get_all_vars subs
      | Script_Info {end_vars, ...} => end_vars

and get_all_vars scrpt = maps get_all_vars_single scrpt |> distinct (op aconv)

fun CASE str ctxt =
    [Script_Task {vars = [],
                  assums = [HOLogic.mk_Trueprop (Syntax.read_term ctxt str)],
                  concls = [], subs = [], cb = Update.null_callback,
                  end_vars = []}]

fun OBTAIN str ctxt =
    [Script_Task {vars = [], assums = [], subs = [],
                  concls = [HOLogic.mk_Trueprop (Syntax.read_term ctxt str)],
                  cb = Update.null_callback, end_vars = []}]

fun (s1 THEN s2) ctxt =
    let
      val s1' = s1 ctxt
      val ctxt' = ctxt |> fold declare_free_term (get_end_vars s1')
    in
      s1' @ (s2 ctxt')
    end

fun (s1 WITH s2) ctxt =
    case s1 ctxt of
        [Script_Task {vars, assums, concls, subs = _, cb, end_vars}] =>
        let
          val ctxt' = ctxt |> fold declare_free_term (vars @ end_vars)
          val s2' = s2 ctxt'
        in
          [Script_Task {vars = vars, assums = assums, concls = concls,
                        subs = s2', cb = cb, end_vars = end_vars}]
        end
      | _ => raise AUTO2 "WITH: first argument should be single script."

end  (* structure Script. *)

open Script
