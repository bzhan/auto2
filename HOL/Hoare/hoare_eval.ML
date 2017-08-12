(* Evaluation on states of the form st { x -> n }. *)

fun is_const_ID t =
    case t of
        Const ("Hoare_States.id.Id", _) $ n => UtilArith.is_numc n
      | _ => false

fun dest_const_ID t =
    case t of
        Const ("Hoare_States.id.Id", _) $ n => UtilArith.dest_numc n
      | _ => raise Fail "dest_const_ID: not constant ID."

(* Converts m = n to Id m = Id n. *)
val id_eq_cv = rewr_obj_eq (obj_sym @{thm id.simps(1)})

fun get_const_ID_eq ctxt t t' =
    if t aconv t' then
      SOME (Thm.reflexive (Thm.cterm_of ctxt t) |> to_obj_eq)
    else if not (is_const_ID t andalso is_const_ID t') then NONE
    else let
      val (n, n') = (dest_const_ID t, dest_const_ID t')
    in
      if n = n' then raise Fail "get_const_ID_eq"
      else SOME ((Nat_Arith.nat_neq_th n n')
                     |> apply_to_thm' (Conv.arg_conv id_eq_cv))
    end

(* For eval (st {x -> n}) x', if both x and x' are constants,
   automatically reduce by comparing them.
 *)
fun eval_update_const_conv ctxt ct =
    case Thm.term_of ct of
        Const ("Hoare_States.eval", _) $ st $ x' =>
        (case st of
             Const ("Hoare_States.empty_state", _) =>
             rewr_obj_eq @{thm eval_empty} ct
           | Const ("Hoare_States.update", _) $ _ $ x $ _ =>
             (case get_const_ID_eq ctxt x x' of
                  NONE => Conv.all_conv ct
                | SOME th =>
                  let
                    val if_th =
                        if is_eq_term (prop_of' th) then th RS @{thm if_P}
                        else th RS @{thm if_not_P}
                  in
                    ((rewr_obj_eq @{thm eval_update})
                         then_conv (rewr_obj_eq if_th)
                         then_conv (eval_update_const_conv ctxt)) ct
                  end)
           | _ => Conv.all_conv ct)
      | _ => Conv.all_conv ct

(* For eval (st {x -> n}) x', if at least one of them is not a
   constant, reduce to an if expression on x = x'.
 *)
fun eval_update_non_const_conv ctxt ct =
    case Thm.term_of ct of
        Const ("Hoare_States.eval", _) $ st $ x' =>
        (case st of
             Const ("Hoare_States.update", _) $ _ $ x $ _ =>
             (case get_const_ID_eq ctxt x x' of
                  NONE => rewr_obj_eq @{thm eval_update} ct
                | SOME _ => Conv.all_conv ct)
           | _ => Conv.all_conv ct)
      | _ => Conv.all_conv ct

val _ = Theory.setup (
      fold add_prfstep_pre_conv [
        ("eval_ES",
         [WithTerm @{term_pat "eval ES ?n"}],
         eval_update_const_conv),

        ("eval_update_const",
         [WithTerm @{term_pat "eval (update ?st ?x ?n) ?x'"}],
         eval_update_const_conv),

        ("eval_update_non_const",
         [WithTerm @{term_pat "eval (update ?st ?x ?n) ?x'"}],
         eval_update_non_const_conv)]
    )
