(* More logic proofsteps. *)

signature LOGIC_MORE =
sig
  val not_ex_forall_cv: Proof.context -> conv
  val disj_rewrite_not_all_prfstep: proofstep
  val add_logic_more_prfsteps: theory -> theory
end;

structure Logic_More : LOGIC_MORE =
struct

open Logic_ProofSteps

(* Move "not" inside exists and foralls. *)
fun not_ex_forall_cv ctxt ct =
    case Thm.term_of ct of
        @{const Not} $ (Const ("HOL.Ex", _) $ Abs _) =>
        (* ~ EX x. P x to ALL x. ~ P x. *)
        ((rewr_obj_eq @{thm HOL.not_ex})
             then_conv (Conv.binder_conv (not_ex_forall_cv o snd) ctxt)) ct
      | @{const Not} $ (Const ("HOL.All", _) $ Abs _) =>
        (* ~ ALL x. P x to EX x. ~ P x. *)
        ((rewr_obj_eq @{thm HOL.not_all})
             then_conv (Conv.binder_conv (not_ex_forall_cv o snd) ctxt)) ct
      | @{const Not} $ (Const ("HOL.conj", _) $ A $ _) =>
        (* ~ (x < y & C) to x < y --> ~C. *)
        if is_order A then
          ((rewr_obj_eq @{thm not_conj_to_imp})
               then_conv (Conv.arg_conv (not_ex_forall_cv ctxt))) ct
        else Conv.all_conv ct
      | @{const Not} $ (Const ("HOL.implies", _) $ A $ _) =>
        (* ~ (x < y --> C) to x < y & ~C. *)
        if is_order A then
          ((rewr_obj_eq @{thm not_imp})
               then_conv (Conv.arg_conv (not_ex_forall_cv ctxt))) ct
        else Conv.all_conv ct
      | @{const Not} $ (Const ("HOL.Not", _) $ _) =>
        (* ~ ~ A to A. *)
        ((rewr_obj_eq nn_cancel_th) then_conv (not_ex_forall_cv ctxt)) ct
      | @{const Not} $ (Const (@{const_name less}, _) $ _ $ _) =>
        (Conv.try_conv (rewr_obj_eq @{thm not_less})) ct
      | @{const Not} $ (Const (@{const_name less_eq}, _) $ _ $ _) =>
        (Conv.try_conv (rewr_obj_eq @{thm not_le})) ct
      | _ => Conv.all_conv ct

(* Rewrite part of DISJ item that is ~ALL. *)
fun disj_rewrite_not_all rtype {ctxt, ...} {id, tname, prop, ...} =
    if not (RewriteTable.is_single_rtype rtype) then [] else
    if not (exists has_vars tname) then [] else
    let
      val (disj_head, subs) = dest_tname_of_disj tname
      fun rewrite_not_all ct =
          case Thm.term_of ct of
              @{const Not} $ (Const ("HOL.All", _) $ Abs _) =>
              not_ex_forall_cv ctxt ct
            | _ => Conv.all_conv ct
      val prop' =
          apply_to_thm' (ac_disj_conv (length subs) rewrite_not_all) prop
    in
      if Thm.prop_of prop aconv Thm.prop_of prop' then []
      else [disj_to_update disj_head (id, length subs, prop')]
    end

val disj_rewrite_not_all_prfstep =
    {name = "disj_rewrite_not_all",
     args = [TypedMatch (TY_DISJ, @{term_pat "?C::bool"})],
     priority = PRIORITY_ADD,
     func = OneStep disj_rewrite_not_all}

(* Function body for proofsteps if_P, if_not_P, and if_not_P'. *)
fun apply_if_eq_thm if_eq_th ((id, _), ths) items _ =
    let
      val {prop, ...} = hd items
      val eq = (nth ths 1) RS if_eq_th
      val th = prop |> to_meta_eq |> apply_to_rhs (rewr_obj_eq eq)
                    |> to_obj_eq
    in
      [Update.thm_update (id, th),
       ShadowItem {id = id, item = hd items}]
    end

val add_logic_more_prfsteps =
    fold add_prfstep (
      [disj_rewrite_not_all_prfstep]

    ) #> fold add_prfstep_custom [
      ("if_P",
       [WithItem (TY_EQ_IF, @{term_pat "?t = (if ?cond then ?x else ?y)"}),
        WithFact @{term_pat "?cond::bool"}],
       PRIORITY_SHADOW,
       apply_if_eq_thm @{thm HOL.if_P}),

      ("if_not_P",
       [WithItem (TY_EQ_IF, @{term_pat "?t = (if ?cond then ?x else ?y)"}),
        WithFact @{term_pat "~?cond::bool"}],
       PRIORITY_SHADOW,
       apply_if_eq_thm @{thm HOL.if_not_P}),

      ("if_not_P'",
       [WithItem (TY_EQ_IF, @{term_pat "?t = (if ~?cond then ?x else ?y)"}),
        WithFact @{term_pat "?cond::bool"}],
       PRIORITY_SHADOW,
       apply_if_eq_thm @{thm if_not_P'})

    ] #> fold add_fixed_sc (
      map (rpair 1) ["if_P", "if_not_P", "if_not_P'"]
    )

end  (* structure Logic_More. *)

val _ = Theory.setup Logic_More.add_logic_more_prfsteps
