(* Proof steps related to sequences. *)

signature SEQ_PROOFSTEPS =
sig
  val convert_eval_Suc_n: proofstep
  val ex_seq_def: proofstep
  val ind_seq_def: proofstep
  val ind_seq_mutual_def: proofstep
end;

structure Seq_ProofSteps : SEQ_PROOFSTEPS =
struct

val convert_eval_Suc_n =
    prfstep_custom
        "convert_eval_Suc_n"
        [WithFact @{term_pat "!(n::nat). ?f n = ?g n"}]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (id, (ths MRS @{thm convert_eval_Suc_n}))]
            handle THM _ => [])

val ex_seq_def =
    prfstep_custom
        "ex_seq_def"
        [WithGoal @{term_pat "EX S. !n. ?P S n"}]
        [Update.ADD_ITEMS]
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (id, (ths MRS (backward_th @{thm ex_seq})))]
            handle THM _ => [])

val ind_seq_def =
    prfstep_custom
        "ind_seq_def"
        [WithGoal @{term_pat "EX S. eval S 0 = ?I &
                              (!n. eval S (1 + n) = ?E S n)"}]
        [Update.RESOLVE_BOX]
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
        [Update.RESOLVE_BOX]
        (fn ((id, _), ths) => fn _ => fn _ =>
            [Update.thm_update (
                id, (ths @ [@{thm ex_mutual_ind_seq}]) MRS @{thm contra_triv})]
            handle THM _ => [])

end  (* structure Seq_ProofSteps. *)

val _ = Theory.setup (add_prfstep Seq_ProofSteps.convert_eval_Suc_n)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ex_seq_def)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ind_seq_def)
val _ = Theory.setup (add_prfstep Seq_ProofSteps.ind_seq_mutual_def)
