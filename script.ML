(* Definition of scripts. *)

infixr 0 THEN
infixr 1 WITH

datatype script
  = Script_Task of {inits: init_info list, subs: script list,
                    cb: (box_id * thm) * status -> raw_update list,
                    end_vars: term list}
type scripts = script list
type pre_scripts = Proof.context -> scripts

signature SCRIPT =
sig
  val update_callback: (box_id * thm) * status -> raw_update list
  val no_script: pre_scripts
  val get_end_vars: scripts -> term list
  val get_all_vars: scripts -> term list
  val check_new_vars: Proof.context -> string list -> term -> unit
  val CASE: string -> pre_scripts
  val HAVE: string -> pre_scripts
  val THEN: pre_scripts * pre_scripts -> pre_scripts
  val WITH: pre_scripts * pre_scripts -> pre_scripts
end

functor Script(Base:UTIL_BASE) : SCRIPT =
struct

structure UtilLogic = UtilLogic(Base)
structure Update = Update(Base)
open Base
open UtilLogic

fun update_callback ((id, th), _) = [Update.thm_update (id, th)]
val no_script = K []
fun get_end_vars_single (Script_Task {end_vars, ...}) = end_vars
fun get_end_vars scrpt = maps get_end_vars_single scrpt

fun get_all_vars_single (Script_Task {inits, subs, end_vars, ...}) =
    maps Update.dest_init_var inits @ end_vars @ get_all_vars subs

and get_all_vars scrpt = maps get_all_vars_single scrpt |> distinct (op aconv)

(* Check for unexpected new variables in script. *)
fun check_new_vars ctxt nms t =
    let
      val new_nms = (subtract (op =) nms (Term.add_free_names t []))
                        |> filter_out (Variable.is_fixed ctxt)
    in
      if length new_nms = 0 then () else let
        val _ = trace_t_ctxt ctxt "At" t
        val _ = tracing ("Variable " ^ commas new_nms)
      in
        raise AUTO2 "unexpected new variable names."
      end
    end

fun CASE str ctxt =
    let
      val t = read_term ctxt str
      val _ = check_new_vars ctxt [] t
    in
      [Script_Task {inits = [InitAssum (mk_Trueprop t)],
                    subs = [], cb = update_callback, end_vars = []}]
    end

(* Given str in the form !x_1 ... x_k. P_1 --> ... --> P_n --> Q,
   create box with initial variables x_1 to x_k, and initial
   assumptions P_1 to P_n and ~Q. The variables x_1 ... x_k should be
   reserved beforehand and not used when this line is executed.
 *)
fun HAVE str ctxt =
    let
      val t = read_term ctxt str
      val init_infos =
          map (fn (is_var, t) => if is_var then InitVar t
                                 else InitAssum (mk_Trueprop t))
              (extract_init_infos t)
      val vars = maps Update.dest_init_var init_infos
      val nms = map (fst o Term.dest_Free) vars
      val _ = check_new_vars ctxt nms t
    in
      if exists (Variable.is_fixed ctxt) nms then
        let
          val to_print = filter (Variable.is_fixed ctxt) nms
          val _ = trace_t_ctxt ctxt "At" t
          val _ = tracing ("Variables " ^ commas to_print)
        in
          raise AUTO2 "HAVE: variable name(s) already used."
        end
      else
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
