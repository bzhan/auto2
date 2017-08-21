(* Induction on variables *)

fun read_var_spec ctxt (n, s) =
    let
      val prem = Syntax.read_term ctxt s
      val var = if is_none n then
                  (Term.add_frees prem []) |> the_single |> Free
                  handle List.Empty => raise Fail "read_var_spec"
                else Syntax.read_term ctxt (the n)
    in
      (var, prem)
    end

fun get_induct_stmt ctxt (var, prem, stmt, arbitrary) =
    if is_some stmt then
      UtilLogic.list_obj_horn (arbitrary, ([], Syntax.read_term ctxt (the stmt)))
    else
      let
        val (_, (As, C)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                                |> Thm.term_of |> Util.strip_meta_horn
        val all_vars = var :: arbitrary
        val obj_As = As |> filter (Util.occurs_frees all_vars)
                        |> map dest_Trueprop
                        |> remove (op aconv) prem
        val obj_C = dest_Trueprop C
      in
        UtilLogic.list_obj_horn (arbitrary, (obj_As, obj_C))
      end

fun var_induct_cmd ((n, s), t, u, v) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val (var, prem) = read_var_spec ctxt (n, s)
      val arbitraries = map (Syntax.read_term ctxt) u
      val stmt = get_induct_stmt ctxt (var, prem, t, arbitraries)
      val _ = trace_t ctxt "Induct statement" stmt

      val (arbitraries, _) = UtilLogic.strip_obj_horn stmt

      (* Obtain the induction theorem *)
      val ind_th = the (ScriptInduct_Data.lookup_induct_data "var_induct" thy prem)
                   handle Option.Option => error "var induct: cannot find theorem."

      val concl = concl_of' ind_th
      val (P, vars) = Term.strip_comb concl
      val _ = assert (Term.is_Var P) "var induct: P is not schematic variable."
      val P_inst = fold Term.lambda (rev vars) stmt
      val inst = Util.update_env (("P", 0), P_inst) fo_init
      val ind_th' = Util.subst_thm_thy thy inst ind_th

      (* Obtain list of assumptions *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As
      val use_As = As |> filter_out (Util.occurs_frees (var :: arbitraries))

      fun retrieve_pat t =
          let
            val t = dest_Trueprop t
            val (vars, (_, C)) = UtilLogic.strip_obj_horn t
            val pat_vars = map (fn t => let val (x, T) = dest_Free t in
                                          Var ((x,0), T)
                                        end) vars
            val arg = C |> dest_arg |> Term.subst_atomic (vars ~~ pat_vars)
          in
            mk_eq (var, arg)
          end

      val prem = hd (Thm.prems_of ind_th)
      val ind_prems = tl (Thm.prems_of ind_th)
      val pats = prem :: map retrieve_pat ind_prems

      val prem_goal = (Logic.list_implies (As, prem))
                          |> Thm.cterm_of ctxt |> Thm.reflexive

      val ind_goals =
          ind_th' |> Thm.prems_of |> tl
                  |> map (fn t => Logic.list_implies (use_As, t))
                  |> map (Thm.cterm_of ctxt)
                  |> map (UtilLogic.to_meta_conv ctxt)

      val all_goals = prem_goal :: ind_goals

      fun solve_eq eq =
          let
            val th = Auto2_Outer.auto2_solve ctxt (Thm.rhs_of eq)
          in
            Thm.equal_elim (meta_sym eq) th
          end

      val _ = assert (length pats = length all_goals)
                     "var_induct: unexpected number of patterns"
    in
      if is_none v then
        let
          val ths = (map solve_eq all_goals) |> map Util.send_all_to_hyps
          val ind_concl = ind_th' |> fold Thm.elim_implies ths
                                  |> fold Thm.implies_intr (rev cAs)
          val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
        end
      else
        let
        (* Create new block with the subgoals *)
        fun after_qed ths prop =
            let
              val ths' = (all_goals ~~ ths)
                            |> map (fn (eq, th) => Thm.equal_elim (meta_sym eq) th)
                            |> map Util.send_all_to_hyps
              val ind_concl = ind_th' |> fold Thm.elim_implies ths'
                                      |> fold Thm.implies_intr (rev cAs)
            in
              Auto2_Outer.have_after_qed ctxt ind_concl prop
            end

          val new_frame =
              Auto2_State.multiple_frame (pats ~~ map Thm.rhs_of all_goals, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val var_spec =
    Scan.option (Parse.term --| @{keyword "in"}) -- Parse.term

val for_stmt =
    Scan.option (@{keyword "for"} |-- Parse.term)

val arbitrary =
    Scan.option (@{keyword "arbitrary"} |-- Scan.repeat Parse.term)

val _ =
  Outer_Syntax.command @{command_keyword "@var_induct"} "apply induction"
    (var_spec -- for_stmt -- arbitrary -- Scan.option @{keyword "@with"} >>
        (fn ((((n, s), t), u), v) =>
            Toplevel.proof (fn state => var_induct_cmd ((n, s), t, these u, v) state)))

val add_var_induct_data = ScriptInduct_Data.add_induct_data "var_induct"
val add_var_induct_data_with_prem =
    ScriptInduct_Data.add_induct_data_with_prem "var_induct"
