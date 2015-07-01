(* Definition of scripts. *)

infixr 0 THEN
infixr 1 WITH

signature SCRIPT =
sig
  datatype script
    = Script_Task of {assums: term list, concls: term list, subs: script list,
                      cb: Update.resolve_callback}
    | Script_Info of {prfstep: proofstep, source: term list}
  type scripts = script list
  type pre_scripts = Proof.context -> scripts * Proof.context
  val no_script: pre_scripts
  val CASE: string -> pre_scripts
  val OBTAIN: string -> pre_scripts
  val THEN: pre_scripts * pre_scripts -> pre_scripts
  val WITH: pre_scripts * pre_scripts -> pre_scripts
  val CHOOSE: string -> pre_scripts
  val CHOOSES: string list -> pre_scripts
end

structure Script : SCRIPT =
struct

datatype script
  = Script_Task of {assums: term list, concls: term list, subs: script list,
                    cb: Update.resolve_callback}
  | Script_Info of {prfstep: proofstep, source: term list}
type scripts = script list
type pre_scripts = Proof.context -> scripts * Proof.context

fun no_script ctxt = ([], ctxt)

fun CASE str ctxt =
    ([Script_Task {assums = [HOLogic.mk_Trueprop (Syntax.read_term ctxt str)],
                   concls = [], subs = [], cb = Update.null_callback}], ctxt)

fun OBTAIN str ctxt =
    ([Script_Task {assums = [], subs = [],
                   concls = [HOLogic.mk_Trueprop (Syntax.read_term ctxt str)],
                   cb = Update.null_callback}], ctxt)

fun (s1 THEN s2) =
    (fn ctxt => let
       val (s1', ctxt') = s1 ctxt
       val (s2', ctxt'') = s2 ctxt'
     in
       (s1' @ s2', ctxt'')
     end)

fun (s1 WITH s2) =
    (fn ctxt =>
        case s1 ctxt of
            ([Script_Task {assums, concls, subs = _, cb}], ctxt') =>
            let
              val (s2', ctxt'') = s2 ctxt'
            in
              ([Script_Task {assums = assums, concls = concls, subs = s2',
                             cb = cb}], ctxt'')
            end
          | _ => raise AUTO2 "WITH: first argument should be single script.")

fun CHOOSE str ctxt =
    let
      val ts = Syntax.read_term ctxt str |> HOLogic.strip_tuple
      val err = "CHOOSE: input should be in the form (var1, ..., varn, cond)."
      val (freevars, cond) = split_last ts
      val dest_vars = map Term.dest_Free freevars
                      handle TERM _ => raise AUTO2 err
      fun mk_exists' (nm, T) cond = HOLogic.mk_exists (nm, T, cond)
      val ex_cond = fold mk_exists' (rev dest_vars) cond |> HOLogic.mk_Trueprop
      val nms = map fst dest_vars
      val _ = assert (not (exists (Variable.is_fixed ctxt) nms))
                     ("CHOOSE: variable name(s) already used.")
      val ctxt' = ctxt |> Variable.add_fixes_direct nms
                       |> fold Variable.declare_term freevars

      (* Given ex_cond_th verifying ex_cond, instantiate the existence
         statement with explicit variable freevar. Code is similar to
         exists_elim proofstep.
       *)
      fun exists_callback (id, ex_cond_th) =
          let
            val cond' = HOLogic.mk_Trueprop cond
            val new_th = Thm.trivial (cert ctxt' cond')
            fun ready (t, ts) =
                forall (fn t' => t' aconv t orelse
                                 not (occurs_frees freevars t')) ts
            fun handler (t, th) =
                th |> Thm.implies_intr (cert ctxt' t)
                   |> fold (ex_elim ctxt) (rev freevars)
                   |> Thm.elim_implies ex_cond_th
            val ritems = (map FreeVar freevars) @
                         [Fact new_th, Handler (cond', (ready, handler))]
          in
            [Update.AddItems {id = id, raw_items = ritems}]
          end
    in
      ([Script_Task {assums = [], subs = [], concls = [ex_cond],
                     cb = exists_callback}], ctxt')
    end

fun CHOOSES strs =
    case strs of
        [str] => CHOOSE str
      | str :: rest => (CHOOSE str) THEN (CHOOSES rest)
      | _ => raise AUTO2 "CHOOSES: empty argument"

end  (* structure Script. *)

open Script
