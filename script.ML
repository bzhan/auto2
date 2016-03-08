(* Definition of scripts. *)

infixr 0 THEN
infixr 1 WITH

signature SCRIPT =
sig
  datatype script
    = Script_Task of {inits: Update.init_info list, subs: script list,
                      cb: (box_id * thm) * status -> Update.raw_update list,
                      end_vars: term list}
  type scripts = script list
  type pre_scripts = Proof.context -> scripts
  val update_callback: (box_id * thm) * status -> Update.raw_update list
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
  = Script_Task of {inits: Update.init_info list, subs: script list,
                    cb: (box_id * thm) * status -> Update.raw_update list,
                    end_vars: term list}
type scripts = script list
type pre_scripts = Proof.context -> scripts

fun update_callback ((id, th), _) = [Update.thm_update (id, th)]
val no_script = K []
fun get_end_vars_single (Script_Task {end_vars, ...}) = end_vars
fun get_end_vars scrpt = maps get_end_vars_single scrpt

fun get_all_vars_single (Script_Task {inits, subs, end_vars, ...}) =
    maps Update.dest_init_var inits @ end_vars @ get_all_vars subs

and get_all_vars scrpt = maps get_all_vars_single scrpt |> distinct (op aconv)

fun CASE str ctxt =
    [Script_Task {inits = [Update.InitAssum (
                              HOLogic.mk_Trueprop (read_term ctxt str))],
                  subs = [], cb = update_callback, end_vars = []}]

fun OBTAIN str ctxt =
    let
      val t = read_term ctxt str
      val init_infos = Update.extract_init_infos t
      val vars = maps Update.dest_init_var init_infos
      val nms = map (fst o Term.dest_Free) vars
      val _ = if not (exists (Variable.is_fixed ctxt) nms) then () else
              let val _ = warning ("Error in " ^ str) in
                raise AUTO2 "OBTAIN: variable name(s) already used."
              end
    in
      [Script_Task {inits = init_infos, subs = [], cb = update_callback,
                    end_vars = []}]
    end

fun (s1 THEN s2) ctxt =
    let
      val s1' = s1 ctxt
      val ctxt' = ctxt |> fold declare_free_term (get_end_vars s1')
    in
      s1' @ (s2 ctxt')
    end

fun (s1 WITH s2) ctxt =
    case s1 ctxt of
        [Script_Task {inits, subs = _, cb, end_vars}] =>
        let
          val vars = maps Update.dest_init_var inits
          val ctxt' = ctxt |> fold declare_free_term (vars @ end_vars)
          val s2' = s2 ctxt'
        in
          [Script_Task {inits = inits, subs = s2', cb = cb,
                        end_vars = end_vars}]
        end
      | _ => raise AUTO2 "WITH: first argument should be single script."

end  (* structure Script. *)

open Script
