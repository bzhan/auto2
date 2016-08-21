(* Proof steps related to sequences. *)

signature SEQ_PROOFSTEPS =
sig
  val convert_eval_Suc_n: proofstep
  val ex_seq_def: proofstep
  val ind_seq_def: proofstep
  val ind_seq_mutual_def: proofstep
  val monotone_pred_ex_prfstep: proofstep
end;

structure Seq_ProofSteps : SEQ_PROOFSTEPS =
struct

val convert_eval_Suc_n =
    prfstep_custom
        "convert_eval_Suc_n"
        [WithFact @{term_pat "!(n::nat). ?f n = ?g n"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (id, (ths MRS @{thm convert_eval_Suc_n}))]
            handle THM _ => [])

val ex_seq_def =
    prfstep_custom
        "ex_seq_def"
        [WithGoal @{term_pat "EX S. !n. ?P S n"}]
        PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (id, (ths MRS (backward_th @{thm ex_seq})))]
            handle THM _ => [])

val ind_seq_def =
    prfstep_custom
        "ind_seq_def"
        [WithGoal @{term_pat "EX S. eval S 0 = ?I &
                              (!n. eval S (1 + n) = ?E S n)"}]
        PRIORITY_RESOLVE
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (
                id, (ths @ [@{thm ex_ind_seq}]) MRS @{thm contra_triv})]
            handle THM _ => [])

val ind_seq_mutual_def =
    prfstep_custom
        "ind_seq_mutual_def"
        [WithGoal
         @{term_pat "EX S T. eval S 0 = ?I & eval T 0 = ?J &
                             (!n. eval S (1 + n) = ?E1 S T n) &
                             (!n. eval T (1 + n) = ?E2 S T n)"}]
        PRIORITY_RESOLVE
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (
                id, (ths @ [@{thm ex_mutual_ind_seq}]) MRS @{thm contra_triv})]
            handle THM _ => [])

fun get_monotone_pred_for_th ctxt p gen_th =
    let
      val pat = gen_th |> prop_of' |> dest_arg
      val inst = pattern_match ctxt (pat, p)
    in
      SOME (subst_thm ctxt inst gen_th)
    end
    handle Pattern.MATCH => NONE

fun get_monotone_pred ctxt p =
    get_first (get_monotone_pred_for_th ctxt p)
              [@{thm monotone_pred_ge}, @{thm monotone_pred_forall},
               @{thm monotone_pred_forall2}]

val monotone_pred_ex_prfstep =
    prfstep_custom
        "monotone_pred_ex"
        [WithGoal @{term_pat "EX x. ?P x & ?Q x"}]
        PRIORITY_SHADOW
        (fn ((id, _), ths) => fn items => fn {ctxt, ...} =>
            let
              val ex_prop = ths |> the_single |> prop_of' |> get_neg
              val (P, Q) =
                  case ex_prop of
                      Const (@{const_name HOL.Ex}, _) $
                            Abs (nm, T, Const (@{const_name conj}, _) $ P $ Q)
                      => (Abs (nm, T, P), Abs (nm, T, Q))
                    | _ => raise AUTO2 "get_monotone_pred: wrong form of prop"
            in
              if Term_Ord.termless (Q, P) then []
              else let
                val p_th = get_monotone_pred ctxt P
                val q_th = get_monotone_pred ctxt Q
              in
                if is_none p_th orelse is_none q_th then []
                else let
                  val th = @{thm monotone_pred_ex}
                                |> apply_on [the p_th, the q_th]
                                |> backward_th |> apply_on ths
                in
                  [Update.ShadowItem {id = id, item = the_single items},
                   Update.thm_update (id, th)]
                end
              end
            end)

end  (* structure Seq_ProofSteps. *)

val _ = Theory.setup (add_prfstep Seq_ProofSteps.convert_eval_Suc_n)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ex_seq_def)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ind_seq_def)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ind_seq_mutual_def)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.monotone_pred_ex_prfstep)
