(* Induction related proof steps. *)

(* Context is all facts where freevar (an init variable)
   appears. Return a pair (facts, stmt), where facts are the initial
   facts to include, and stmt is the neg_form of facts.
 *)
fun get_var_context id freevar (st as {ctxt, ...}) =
    let
      val init_vars = Status.get_all_init_vars st id
      val init_facts = (Status.get_all_init_facts st id)
                           |> filter (occurs_free freevar o fst)
    in
      if member (op aconv) init_vars freevar andalso
         1 <= length init_facts andalso length init_facts <= 2 andalso
         length (init_facts |> filter snd) <= 1  (* number of concls <= 1 *)
      then
        SOME (init_facts, Status.get_neg_form ctxt init_facts)
      else NONE
    end

(* Given an initial free variable freevar and a box ID, find a set of
   initial facts and other initial variables that form a general
   context around freevar. Include other initial variables that do not
   appear by itself in an initial fact (no explicit conditions on that
   variable), then include all initial facts that contain any of these
   variables (including freevar).

   Return a triple (vars, facts, stmt), where vars are the additional
   variables, facts are the initial facts. stmt is the neg_form of
   facts.
 *)
fun get_gen_var_context id freevar (st as {ctxt, ...}) =
    let
      val init_vars = Status.get_all_init_vars st id
      val init_facts = Status.get_all_init_facts st id

      (* Get initial variables that appear alone in an initial fact. *)
      fun only_var (t, _) =
          let val frees = Term.add_frees t []
          in if length frees = 1 then map Free frees else [] end
      val only_vars = maps only_var init_facts

      (* List of variables to include. *)
      val gen_vars = subtract (op aconv) only_vars init_vars

      (* List of initial facts to include. *)
      fun has_gen_var (t, _) =
          let val frees = map Free (Term.add_frees t [])
          in inter (op aconv) gen_vars frees <> [] end
      val init_facts' = init_facts |> filter has_gen_var

      fun make_all freevar t =
          let val (x, T) = dest_Free freevar in HOLogic.mk_all (x, T, t) end
      val abs_vars = remove (op aconv) freevar gen_vars
    in
      if member (op aconv) gen_vars freevar andalso
         1 <= length init_facts' andalso length init_facts' <= 3 andalso
         length (init_facts' |> filter snd) <= 1  (* number of concls <= 1 *)
      then
        SOME (abs_vars, init_facts',
              (Status.get_neg_form ctxt init_facts')
                  |> HOLogic.dest_Trueprop |> fold make_all abs_vars
                  |> HOLogic.mk_Trueprop)
      else NONE
    end

fun implies_intr_vars freevars exclude th =
    let
      val thy = Thm.theory_of_thm th
      val chyps = (Thm.hyps_of th)
                      |> filter (fn t => not (member (op aconv) exclude t)
                                         andalso occurs_frees freevars t)
                      |> map (cert_thy thy)
    in
      fold Thm.implies_intr chyps th
    end

fun nat_induct_handler ctxt var (abs_vars, inits, stmt) neq0_th (t, th) =
    let
      val p = lambda var (Term.abstract_over (var, HOLogic.dest_Trueprop stmt))
      val init_facts = map fst inits
      val cinit_facts = map (cert ctxt) init_facts
      val inst = (Vartab.empty,
                  Vartab.empty |> Vartab.update_new (("P", 0), (type_of p, p)))

      (* First compute the case zero part of induction. *)
      val neq0 = neq0_th |> Thm.prop_of |> HOLogic.dest_Trueprop
                         |> get_neg |> HOLogic.mk_Trueprop |> cert ctxt
      val neq0_th' =
          neq0_th |> rewrite_thm_to_contra_form
                  |> send_to_hyps neq0
                  |> fold Thm.implies_intr cinit_facts
                  |> rewrite_thm_from_contra_form
                  |> fold Thm.forall_intr (map (cert ctxt) abs_vars)
                  |> apply_to_thm (to_obj_conv ctxt)
                  |> Thm.implies_intr neq0
                  |> Thm.forall_intr (cert ctxt var)
      val nat0_inst = subst_thm ctxt inst @{thm nat_zero}
      val p0_th = Thm.implies_elim nat0_inst neq0_th'
      val _ = assert ((HOLogic.dest_Trueprop (Thm.prop_of p0_th))
                          aconv (betapply (p, @{term "0::nat"}))) "incorrect p0"

      (* Second step: Suc part of induction. *)
      val ct = cert ctxt t
      val th' = th |> fold Thm.implies_intr cinit_facts
                   |> rewrite_thm_from_contra_form
                   |> fold Thm.forall_intr (map (cert ctxt) abs_vars)
                   |> apply_to_thm (to_obj_conv ctxt)
                   |> Thm.implies_intr ct
                   |> Thm.forall_intr (cert ctxt var)
      val natS_inst = subst_thm ctxt inst @{thm nat_shift}
      val pS_th = th' |> Thm.implies_elim natS_inst
                      |> Thm.forall_intr (cert ctxt @{term_pat "?n::nat"})

      (* Finally, instantiate nat.induct. *)
      val natI_inst = subst_thm ctxt inst @{thm nat.induct}
    in
      natI_inst |> fold Thm.elim_implies [p0_th, pS_th]
                |> Thm.forall_intr (cert ctxt @{term_pat "?nat::nat"})
                |> Thm.forall_elim (cert ctxt var)
                |> apply_to_thm (to_meta_all_conv ctxt)
                |> fold Thm.forall_elim (map (cert ctxt) (rev abs_vars))
                |> apply_to_thm to_meta_imp_conv
                |> rewrite_thm_to_contra_form
                |> send_all_to_hyps
    end

val induction =
    prfstep_custom
        "induction"
        [WithFact @{term_pat "(?n::nat) ~= 0"}]
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val tbl = Status.get_rewrite_table st
              val trm_n = RewriteTable.simp_val id tbl (lookup_inst inst "n")
              val var_ctxt = get_var_context id trm_n st
              val pred_pat = @{term_pat "(n::nat) - 1"}
              val trm_pred_n =
                  subst_atomic [(Free ("n", HOLogic.natT), trm_n)] pred_pat
            in
              case var_ctxt of
                  NONE => []
                | SOME (inits, stmt) =>
                  (* Simple induction. *)
                  let
                    val stmt' = Term.subst_atomic [(trm_n, trm_pred_n)] stmt
                    val init_facts = map fst inits

                    (* Attempt to clear all retro hyps from neq0_th. *)
                    val neq0_th = the_single ths
                    val handlers = Status.get_all_handlers st id
                    val neq0_th' = Status.invoke_handlers handlers neq0_th

                    fun ready (t, ts) =
                        forall (fn t' => t' aconv t orelse
                                         member (op aconv) init_facts t' orelse
                                         not (occurs_free trm_n t')) ts

                    fun handler (t, th) =
                        nat_induct_handler ctxt trm_n ([], inits, stmt)
                                           neq0_th' (t, th)
                  in
                    [Update.AddItems {
                        id = id, raw_items =
                                 handler_ritems ctxt stmt' (ready, handler)}]
                  end
            end)
val _ = Theory.setup (add_prfstep induction)

(* Similar to nat_induct_handler. *)
fun nat_strong_induct_handler ctxt var (inits, stmt) (t, th) =
    let
      val p = lambda var (Term.abstract_over (var, HOLogic.dest_Trueprop stmt))
      val ct = cert ctxt t
      val init_facts = map fst inits
      val cinit_facts = map (cert ctxt) init_facts
      val inst = (Vartab.empty,
                  Vartab.empty |> Vartab.update_new (("P", 0), (type_of p, p)))
      val th' = th |> fold Thm.implies_intr cinit_facts
                   |> rewrite_thm_from_contra_form
                   |> apply_to_thm (to_obj_conv ctxt)
                   |> Thm.implies_intr ct
                   |> Thm.forall_intr (cert ctxt var)
      val natless_inst = subst_thm ctxt inst @{thm nat_less_induct}
    in
      th' |> Thm.implies_elim natless_inst
          |> Thm.forall_intr (cert ctxt @{term_pat "?n::nat"})
          |> Thm.forall_elim (cert ctxt var)
          |> apply_to_thm to_meta_imp_conv
          |> rewrite_thm_to_contra_form
          |> send_all_to_hyps
    end

val strong_induction =
    prfstep_custom
        "strong_induction"
        [WithFact @{term_pat "(?m::nat) < ?n"}]
        (fn ((id, inst), _) => fn (st as {ctxt, ...}) =>
            let
              val tbl = Status.get_rewrite_table st
              val trm_m = RewriteTable.simp_val id tbl (lookup_inst inst "m")
              val trm_n = RewriteTable.simp_val id tbl (lookup_inst inst "n")
              val var_ctxt = get_var_context id trm_n st
              val dep_vars = Status.get_all_dep_vars st id
            in
              if member (op aconv) dep_vars trm_m then
                case var_ctxt of
                    NONE => []
                  | SOME (inits, stmt) =>
                    (* Strong induction. *)
                    let
                      val stmt' = Term.abstract_over
                                      (trm_n, HOLogic.dest_Trueprop stmt)
                      val pat_res = @{term_pat "(! (m::nat) < (n::nat). P)"}
                      val subst = [(Free ("P", @{typ bool}), stmt')]
                      val stmt'' = pat_res |> subst_atomic subst
                                           |> HOLogic.mk_Trueprop
                      val init_facts = map fst inits

                      fun ready (t, ts) =
                          forall (fn t' =>
                                     t' aconv t orelse
                                     member (op aconv) init_facts t' orelse
                                     not (occurs_free trm_n t')) ts

                      fun handler (t, th) = nat_strong_induct_handler
                                                ctxt trm_n (inits, stmt) (t, th)
                    in
                      [Update.AddItems {
                          id = id, raw_items =
                                   handler_ritems ctxt stmt'' (ready, handler)}]
                    end
              else []
            end)
val _ = Theory.setup (add_prfstep strong_induction)

val gen_induction =
    prfstep_custom
        "gen_induction"
        [WithFact @{term_pat "(?n::nat) ~= 0"}]
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val tbl = Status.get_rewrite_table st
              val trm_n = RewriteTable.simp_val id tbl (lookup_inst inst "n")
              val var_ctxt = get_gen_var_context id trm_n st
              val pred_pat = @{term_pat "(n::nat) - 1"}
              val trm_pred_n =
                  subst_atomic [(Free ("n", HOLogic.natT), trm_n)] pred_pat
            in
              case var_ctxt of
                  NONE => []
                | SOME (abs_vars, inits, stmt) =>
                  (* Induction generalizing other variables. *)
                  let
                    val stmt' = Term.subst_atomic [(trm_n, trm_pred_n)] stmt
                    val init_facts = map fst inits
                    val gen_vars = trm_n :: abs_vars

                    (* Attempt to clear all retro hyps from neq0_th. *)
                    val neq0_th = the_single ths
                    val handlers = Status.get_all_handlers st id
                    val neq0_th' = Status.invoke_handlers handlers neq0_th

                    fun ready (t, ts) =
                        forall (fn t' => t aconv t' orelse
                                         member (op aconv) init_facts t' orelse
                                         not (occurs_frees gen_vars t')) ts

                    fun handler (t, th) =
                        nat_induct_handler ctxt trm_n (abs_vars, inits, stmt)
                                           neq0_th' (t, th)
                  in
                    [Update.AddItems {
                        id = id, raw_items =
                                 handler_ritems ctxt stmt' (ready, handler)}]
                  end
            end)
val _ = Theory.setup (add_prfstep gen_induction)

(* Case analysis. *)
val _ = Theory.setup (
      add_gen_prfstep
          ("case_intro",
           [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
            CreateCase ([@{term_pat "?cond::bool"}], [])]))

val _ = Theory.setup (
      add_gen_prfstep
          ("if_true",
           [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
            WithFact @{term_pat "?cond::bool"},
            GetFact (@{term_pat "(if ?cond then (?yes::?'a) else ?no) = ?yes"},
                     @{thm if_true})]))

val _ = Theory.setup (
      add_gen_prfstep
          ("if_false",
           [WithTerm @{term_pat "if ?cond then (?yes::?'a) else ?no"},
            WithFact @{term_pat "~?cond"},
            GetFact (@{term_pat "(if ?cond then (?yes::?'a) else ?no) = ?no"},
                     @{thm if_false})]))

val _ = Theory.setup (
      add_gen_prfstep
          ("if_false'",
           [WithTerm @{term_pat "if (~?cond) then (?yes::?'a) else ?no"},
            WithFact @{term_pat "?cond::bool"},
            GetFact (@{term_pat
                           "(if (~ ?cond) then (?yes::?'a) else ?no) = ?no"},
                     @{thm if_false'})]))
