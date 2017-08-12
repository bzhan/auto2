(* Outer syntax for auto2 *)

signature AUTO2_OUTER =
sig
  val auto2_solve: Proof.context -> cterm -> thm
  val init_state: Proof.state -> Proof.state

  val have_resolve: Proof.context -> term list -> thm -> term -> thm
  val strip_goal: term -> term list * term
  val refine_subgoal_th: thm -> thm -> thm
  val have_after_qed: Proof.context -> thm -> thm -> thm
  val strip_have_goal: term -> term list * (term list * term)
  val have_cmd: string * 'a option * string option -> Proof.state -> Proof.state

  val end_cmd: Proof.state -> Proof.state
  val qed_cmd: Proof.state -> Proof.context

  val strip_ex: term -> term list * term
  val obtain_resolve: Proof.context -> term list -> thm -> term -> thm
  val obtain_after_qed: Proof.context -> thm -> thm -> thm
  val obtain_cmd:
      string list * string list * string option -> Proof.state -> Proof.state

  val case_resolve: Proof.context -> term list -> thm -> thm
  val case_after_qed: Proof.context -> thm -> thm -> thm
  val case_cmd: string * string option -> Proof.state -> Proof.state

  val contra_resolve: Proof.context -> term list -> term list -> term -> thm
  val contra_after_qed: Proof.context -> thm -> thm
  val contra_cmd: Proof.state -> Proof.state

  val let_resolve: Proof.context -> term list -> term -> term list -> term -> thm
  val let_after_qed_one: Proof.context -> term -> thm -> thm
  val let_after_qed: Proof.context -> term list -> thm -> thm
  val let_cmd: string list -> Proof.state -> Proof.state
end;

structure Auto2_Outer : AUTO2_OUTER =
struct

open Base
open UtilLogic

(* Use auto2 to solve the given statement *)
fun auto2_solve ctxt stmt =
    let
      val goal = stmt |> Thm.trivial |> Goal.protect 1
    in
      (Auto2.auto2_tac ctxt goal)
          |> Seq.hd |> Goal.conclude
    end

(* Initiate auto2 state, using goal from the Isar state. *)
fun init_state state =
    let
      val {goal, context = ctxt, ...} = Proof.goal state
      val _ = assert (Auto2_State.get_num_frame ctxt = 0)
                     "init_state: state not empty."
      val init_frame = {prop = goal, induct_stmt = NONE, prem_only = [],
                        after_qed = NONE}
    in
      state |> Proof.map_contexts (Auto2_State.push_head init_frame)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@proof"} "begin auto2 proof"
    (Scan.succeed (Toplevel.proof init_state))

(* Given theorem A_1 ==> ... ==> A_n ==> B, a term C, and a list of
   variables x, obtain the theorem (!!x. A_1 ==> ... ==> A_n ==> B ==>
   C) ==> (!!x. A_1 ==> ... ==> A_n ==> C).
 *)
fun have_resolve ctxt vars th concl =
    let
      val prop = Thm.prop_of th
      val (As, B) = Logic.strip_horn prop
      val cAs = map (cert ctxt) As
      val c_vars = map (cert ctxt) vars
      val stmt = (Logic.list_implies (As @ [B], concl))
                     |> fold Logic.all (rev vars) |> cert ctxt

      val thAs = map Thm.assume cAs
      val th_bc =
          stmt |> Thm.assume  (* !!x. A_1 ==> ... ==> A_n ==> B ==> C *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* B ==> C *)

      val th_b = th |> fold Thm.elim_implies thAs  (* B *)

      val th_c = Thm.implies_elim th_bc th_b  (* C *)
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

fun strip_goal t =
    case t of
        Const (@{const_name Pure.all}, _) $ Abs (abs as (_, T, _)) =>
        let
          val (x, body) = Term.dest_abs abs
          val var = Free (x, T)
          val (vars, body') = strip_goal body
        in
          (var :: vars, body')
        end
      | _ => ([], t)

fun refine_subgoal_th th prop =
    let
      val assum = hd (Drule.cprems_of th)
    in
      th |> send_first_to_hyps
         |> Thm.implies_elim prop
         |> Thm.implies_intr assum
    end

(* Given prop in the form (!!x. A_1 ==> ... ==> A_n ==> C) ==> D, and
   th in the form A_1 ==> ... ==> A_n ==> B, return the theorem
   (!!x. A_1 ==> ... ==> A_n ==> B ==> C) ==> D.
 *)
fun have_after_qed ctxt th prop =
    let
      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal

      val concl = Logic.strip_imp_concl body
      val have_res = have_resolve ctxt vars th concl
    in
      refine_subgoal_th have_res prop
    end

fun strip_have_goal t =
    if is_all t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, (assum, concl)) = strip_have_goal body
          in
            (var :: vars, (assum, concl))
          end
        | _ => error "strip_have_goal"
    else if is_ball t then
      case t of
          _ $ S $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val mem = mk_mem (var, S)
            val (vars, (assum, concl)) = strip_have_goal body
          in
            (var :: vars, (mem :: assum, concl))
          end
        | _ => error "strip_have_goal"
    else if is_imp t then
      let
        val (vars, (assum, concl)) = strip_have_goal (dest_arg t)
      in
        (vars, (dest_arg1 t :: assum, concl))
      end
    else
      ([], ([], t))

fun have_cmd (s, r, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state

      val (vars, (assums, concl)) = s |> Syntax.read_term ctxt
                                      |> strip_have_goal

      val {prop, ...} = Auto2_State.get_head ctxt
      val (_, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val (As, _) = Logic.strip_horn body

      val stmt = Logic.list_implies (As @ map mk_Trueprop assums,
                                     mk_Trueprop concl)

      fun after_qed th prop =
          let
            val th' = th |> funpow (length As) send_first_to_hyps
                         |> fold Thm.forall_intr (rev (map (cert ctxt) vars))
                         |> apply_to_thm (to_obj_conv ctxt)
                         |> fold Thm.implies_intr (rev (map (cert ctxt) As))
          in
            have_after_qed ctxt th' prop
          end

      val stmt' = fold mk_obj_all (rev vars) (list_obj_imp (assums, concl))

      val is_rule = is_some r
      val new_vars =
          filter_out (
            fn v => Variable.is_fixed ctxt (fst (Term.dest_Free v))) vars
    in
      if is_none t orelse the t = "@then" then
        let
          (* Run auto2 to obtain A_1 ==> ... ==> A_n ==> B. *)
          val ctxt' = ctxt |> fold declare_free_term new_vars
          val th = auto2_solve ctxt' (cert ctxt' stmt)
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th (after_qed th))
                |> (if is_rule then I else
                    Proof.map_contexts (Auto2_State.add_prem_only stmt'))
        end
      else
        let
          (* Create new block with stmt *)
          val goal = Thm.trivial (cert ctxt stmt) |> Goal.protect 1
          val new_block = {prop = goal, induct_stmt = NONE, prem_only = [],
                           after_qed = SOME ([], after_qed)}
        in
          state |> (if is_rule then I else
                    Proof.map_contexts (Auto2_State.add_prem_only stmt'))
                |> Proof.map_contexts (fold declare_free_term new_vars)
                |> Proof.map_contexts (Auto2_State.push_head new_block)
        end
    end

val rule =
    Scan.option (Parse.$$$ "(" --| @{keyword "@rule"} |-- Parse.$$$ ")")

val _ =
  Outer_Syntax.command @{command_keyword "@have"} "intermediate goal"
    (((rule -- Parse.term) --
      Scan.option (@{keyword "@with"} || @{keyword "@then"})) >>
        (fn ((s, r), t) =>
           Toplevel.proof (fn state => have_cmd (r, s, t) state)))

fun end_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val {prop, after_qed, ...} = Auto2_State.get_head ctxt

      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal

      val th = (auto2_solve ctxt (cert ctxt body))
                   |> fold Thm.forall_intr (rev (map (cert ctxt) vars))

      val new_prop = Goal.conclude (Thm.implies_elim prop th)
      val (new_vars, f) = (the after_qed)
    in
      state |> Proof.map_contexts Auto2_State.pop_head
            |> Proof.map_contexts (Auto2_State.map_head_th (f new_prop))
            |> Proof.map_contexts (fold declare_free_term new_vars)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@end"} "end of with block"
    (Scan.succeed (
       Toplevel.proof (fn state => end_cmd state)))

fun qed_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val _ = assert (Auto2_State.get_num_frame ctxt = 1)
                     "Qed should be applied outside any 'with' blocks"
      val {prop, ...} = Auto2_State.get_head ctxt

      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal

      val th = (auto2_solve ctxt (cert ctxt body))
                   |> fold Thm.forall_intr (rev (map (cert ctxt) vars))
      val new_prop = Thm.implies_elim prop th

      val method = K (Method.CONTEXT_TACTIC (PRIMITIVE (K new_prop)))
    in
      state |> Proof.map_contexts (Auto2_State.set_head_th new_prop)
            |> Proof.refine_singleton (Method.Basic (K method))
            |> Proof.global_done_proof
    end

val _ =
  Outer_Syntax.command @{command_keyword "@qed"} "end of proof"
    (Scan.succeed (
       Toplevel.end_proof (K qed_cmd)))

fun strip_ex t =
    if is_ex t then
      case t of
          _ $ Abs (abs as (_, T, _)) =>
          let
            val (x, body) = Term.dest_abs abs
            val var = Free (x, T)
            val (vars, body') = strip_ex body
          in
            (var :: vars, body')
          end
        | _ => error "strip_ex"
    else
      ([], t)

(* Given theorem A_1 ==> ... ==> A_n ==> EX y. P(y), a term C, and a
   list of variables x, obtain the theorem (!!x y. A_1 ==> ... ==> A_n
   ==> P(y) ==> C) ==> (!!x. A_1 ==> ... ==> A_n ==> C)
 *)
fun obtain_resolve ctxt vars th concl =
    let
      val prop = Thm.prop_of th

      (* B is EX x. P(x) *)
      val (As, B) = Logic.strip_horn prop
      val cAs = map (cert ctxt) As
      val c_vars = map (cert ctxt) vars

      val (new_vars, body) = strip_ex (dest_Trueprop B)

      val stmt = (Logic.list_implies (As @ [mk_Trueprop body], concl))
                     |> fold Logic.all (rev new_vars)
                     |> fold Logic.all (rev vars)
                     |> cert ctxt

      val thAs = map Thm.assume cAs
      val th_b = th |> fold Thm.elim_implies thAs

      (* P(x) ==> C *)
      val th_bc = stmt |> Thm.assume
                       |> fold Thm.forall_elim c_vars
                       |> fold Thm.forall_elim (map (cert ctxt) new_vars)
                       |> fold Thm.elim_implies thAs
      val th_c = (fold (ex_elim ctxt) (rev new_vars) th_bc)
                     |> Thm.elim_implies th_b
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Give prop in the form (A_1 ==> ... ==> A_n ==> C) ==> D, and th in
   the form A_1 ==> ... ==> A_n ==> EX x. P(x), return the theorem
   (!!x. A_1 ==> ... ==> A_n ==> P(x) ==> C) ==> D
 *)
fun obtain_after_qed ctxt th prop =
    let
      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal

      val concl = Logic.strip_imp_concl body
      val obtain_res = obtain_resolve ctxt vars th concl
    in
      refine_subgoal_th obtain_res prop
    end

fun obtain_cmd (s, t, u) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val (vars, conds) = (Syntax.read_terms ctxt (s @ t))
                              |> chop (length s)
      (* Elements of vars can be in the form x : A, process into var x
         and cond x : A.
       *)
      val conds = filter is_mem vars @ conds
      val vars = map (fn t => if is_mem t then dest_arg1 t else t) vars

      val C = conds |> list_conj |> fold mk_exists (rev vars) |> mk_Trueprop

      val {prop, ...} = Auto2_State.get_head ctxt
      val (_, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val (As, _) = Logic.strip_horn body

      val stmt = Logic.list_implies (As, C)
      val new_vars =
          filter_out (
            fn v => Variable.is_fixed ctxt (fst (Term.dest_Free v))) vars
    in
      if is_none u orelse the u = "@then" then
        let
          (* Run auto2 to obtain A_1 ==> ... ==> A_n ==> B. *)
          val th = auto2_solve ctxt (cert ctxt stmt)
        in
          state |> Proof.map_contexts (fold declare_free_term new_vars)
                |> Proof.map_contexts (Auto2_State.map_head_th (obtain_after_qed ctxt th))
        end
      else
        let
          (* Create new block with stmt *)
          val goal = Thm.trivial (cert ctxt stmt) |> Goal.protect 1
          val new_block = {prop = goal, induct_stmt = NONE, prem_only = [],
                           after_qed = SOME (new_vars, obtain_after_qed ctxt)}
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_block)
        end
    end

val obtain_param =
  ((Scan.repeat Parse.term --
    Scan.option (@{keyword "where"} |-- (Scan.repeat Parse.term)))
     -- Scan.option (@{keyword "@with"} || @{keyword "@then"}))

val _ =
  Outer_Syntax.command @{command_keyword "@obtain"} "obtain variables"
    (obtain_param >>
       (fn ((s, t), u) =>
           Toplevel.proof (fn state => obtain_cmd (s, these t, u) state)))

(* Given theorem A_1 ==> ... ==> A_n ==> B ==> C, and a list of
   variables x, obtain the theorem (!!x. A_1 ==> ... ==> A_n ==> ~B
   ==> C) ==> (!!x. A_1 ==> ... ==> A_n ==> C).
 *)
fun case_resolve ctxt vars th =
    let
      val prop = Thm.prop_of th

      val ((As, B), C) = prop |> Logic.strip_horn |> apfst split_last
      val cAs = map (cert ctxt) As
      val c_vars = map (cert ctxt) vars
      val nB = mk_Trueprop (Not $ (dest_Trueprop B))
      val stmt = (Logic.list_implies (As @ [nB], C))
                     |> fold Logic.all (rev vars) |> cert ctxt

      val thAs = map Thm.assume cAs
      val th_nbc =
          stmt |> Thm.assume  (* !!x. A_1 ==> ... ==> A_n ==> ~B ==> C *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* ~B ==> C *)

      val th_bc = th |> fold Thm.elim_implies thAs

      val inst = fo_init |> update_env (("P",0), dest_Trueprop B)
                         |> update_env (("Q",0), dest_Trueprop C)
      val th_c = case_split_th |> subst_thm ctxt inst
                               |> fold Thm.elim_implies [th_bc, th_nbc]
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Given prop in the form (!!x. A_1 ==> ... ==> A_n ==> C) ==> D, and
   th in the form A_1 ==> ... ==> A_n ==> B ==> C, return the theorem
   (!!x. A_1 ==> ... ==> A_n ==> ~B ==> C) ==> D.
 *)
fun case_after_qed ctxt th prop =
    let
      val (vars, _) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val case_res = case_resolve ctxt vars th
    in
      refine_subgoal_th case_res prop
    end

fun case_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val B = s |> Syntax.read_term ctxt |> mk_Trueprop

      val {prop, ...} = Auto2_State.get_head ctxt
      val (_, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val (As, C) = Logic.strip_horn body

      val stmt = Logic.list_implies (As @ [B], C) |> cert ctxt
    in
      if is_none t orelse the t = "@then" then
        let
          (* Run auto2 to obtain A_1 ==> ... ==> A_n ==> B ==> C *)
          val th = auto2_solve ctxt stmt
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th (case_after_qed ctxt th))
        end
      else
        let
          (* Create new block with stmt *)
          val goal = Thm.trivial stmt |> Goal.protect 1
          val new_block = {prop = goal, induct_stmt = NONE, prem_only = [],
                           after_qed = SOME ([], case_after_qed ctxt)}
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_block)
        end
    end

val _ =
  Outer_Syntax.command @{command_keyword "@case"} "intermediate case"
    ((Parse.term -- Scan.option (@{keyword "@with"} || @{keyword "@then"})) >>
        (fn (s, t) =>
            Toplevel.proof (fn state => case_cmd (s, t) state)))

(* Given a list of variables x, assumptions A_i, and term C, return
   the theorem (!!x. A_1 ==> ... ==> A_n ==> ~C ==> False) ==>
   (!!x. A_1 ==> ... ==> A_n ==> C).
 *)
fun contra_resolve ctxt vars As C =
    let
      val stmt = (Logic.list_implies (As @ [get_neg' C], pFalse))
                     |> fold Logic.all (rev vars) |> cert ctxt
      val cAs = map (cert ctxt) As
      val c_vars = map (cert ctxt) vars

      val thAs = map Thm.assume cAs
      val th_c =
          stmt |> Thm.assume  (* !!x. A_1 ==> ... ==> A_n ==> ~C ==> False *)
               |> fold Thm.forall_elim c_vars
               |> fold Thm.elim_implies thAs  (* ~C ==> False *)
               |> rewrite_thm_from_contra_form  (* C *)
    in
      th_c |> fold Thm.implies_intr (rev cAs)
           |> fold Thm.forall_intr (rev c_vars)
           |> Thm.implies_intr stmt
    end

(* Given prop in the form (!!x. A_1 ==> ... ==> A_n ==> C) ==> D,
   return the theorem (!!x. A_1 ==> ... ==> A_n ==> ~C ==> False) ==>
   D.
 *)
fun contra_after_qed ctxt prop =
    let
      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val (As, C) = Logic.strip_horn body
      val contra_res = contra_resolve ctxt vars As C
    in
      refine_subgoal_th contra_res prop
    end

(* Change the subgoal from !!x. A_1 ==> ... ==> A_n ==> C to !!x. A_1
   ==> ... ==> A_n ==> ~C ==> False.
 *)
fun contra_cmd state =
    let
      val {context = ctxt, ...} = Proof.goal state
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th (contra_after_qed ctxt))
    end

val _ =
  Outer_Syntax.command @{command_keyword "@contradiction"}
    "apply proof by contradiction"
    (Scan.succeed (
        Toplevel.proof (fn state => contra_cmd state)))

(* Given a list of variables x, an equation y = t, assumptions A_i,
   and a term C, return the theorem (!!x y. A_1 ==> ... ==> A_n ==> y
   = t ==> C) ==> (!!x. A_1 ==> ... ==> A_n ==> C).
 *)
fun let_resolve ctxt vars eq As C =
    let
      val thy = Proof_Context.theory_of ctxt

      (* Call obtain_resolve with th as A_i ==> EX y. y = t. *)
      val (lhs, rhs) = dest_eq eq
      val pat_a = case ex_vardef_th |> prop_of' |> dest_arg of
                      Abs (_, _, b) => dest_arg b
                    | _ => raise Fail "ex_vardef_th"
      val (x, _) = Term.dest_Free lhs
      val inst = Pattern.first_order_match thy (pat_a, rhs) fo_init
      val ex_th = subst_thm ctxt inst ex_vardef_th
      val t' = case Thm.prop_of ex_th of
                   A $ (B $ Abs (_, T, body)) => A $ (B $ Abs (x, T, body))
                 | _ => error "let_resolve"
      val ex_th = ex_th |> Thm.renamed_prop t'
                        |> fold Thm.implies_intr (rev (map (cert ctxt) As))
    in
      obtain_resolve ctxt vars ex_th C
    end

(* Given prop in the form (!!x. A_1 ==> ... ==> A_n ==> C) ==> D, and
   an equation y = t, return the theorem (!!x. A_1 ==> ... ==> A_n ==>
   y = t ==> C) ==> D.
 *)
fun let_after_qed_one ctxt eq prop =
    let
      val (vars, body) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> strip_goal
      val (As, C) = Logic.strip_horn body
      val let_res = let_resolve ctxt vars eq As C
    in
      refine_subgoal_th let_res prop
    end

fun let_after_qed ctxt eqs prop =
    prop |> fold (let_after_qed_one ctxt) eqs

(* Add y = t as an assumption *)
fun let_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val eqs = Syntax.read_terms ctxt s
      val vars = map (fst o dest_eq) eqs
      val new_vars =
          filter_out (
            fn v => Variable.is_fixed ctxt (fst (Term.dest_Free v))) vars
    in
      state |> Proof.map_context (fold declare_free_term new_vars)
            |> Proof.map_contexts (Auto2_State.map_head_th (let_after_qed ctxt eqs))
    end

val _ =
  Outer_Syntax.command @{command_keyword "@let"} "define a variable"
    (((Scan.repeat Parse.term) --| Scan.option @{keyword "@then"}) >>
        (fn s =>
            Toplevel.proof (fn state => let_cmd s state)))

end  (* structure Auto2_Outer *)
