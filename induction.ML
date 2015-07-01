(* Induction related proof steps. *)

structure InductData =
Theory_Data (
  type T = ((term * (term list -> proofstep)) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (eq_fst (op =))
)

signature INDUCT_PROOFSTEPS =
sig
  val add_induct_data:
      string -> term * (term list -> proofstep) -> theory -> theory
  val add_typed_induct_data:
      string -> typ * (term list -> proofstep) -> theory -> theory
  val get_typed_prfstep:
      theory -> string -> typ -> (term list -> proofstep) option
  val get_term_prfstep:
      theory -> string -> term -> (term list -> proofstep) option
  val get_var_context: box_id -> term list -> Status.status ->
                       (term * init_type) list option
  val check_ind_th: thm -> prfstep_descriptor list * (term * term)
  val induct_handler: thm -> Proof.context -> term ->
                      term list * (term * init_type) list * term -> thm ->
                      (term * thm) -> thm
  val prfstep_induction: string -> prfstep_descriptor list -> term * term ->
                         thm -> term list -> proofstep
  val add_prfstep_induction: thm -> theory -> theory
  val check_strong_ind_th: thm -> term
  val strong_induct_handler: thm -> Proof.context -> term ->
                             term list * (term * init_type) list * term ->
                             (term * thm) -> thm
  val prfstep_strong_induction:
      string -> prfstep_descriptor list -> thm -> term list -> proofstep
  val add_prfstep_strong_induction: thm -> theory -> theory
  val prfstep_prop_induction:
      string -> prfstep_descriptor list -> thm -> term list -> proofstep
  val add_prfstep_prop_induction: thm -> theory -> theory
  val prfstep_var_induction:
      string -> prfstep_descriptor list -> thm -> term list -> proofstep
  val add_prfstep_var_induction: thm -> theory -> theory

  datatype induct_info = Arbitrary of string
                       | OnFact of string
  val Arbitraries: string list -> induct_info list
  val collect_arbitraries: induct_info list -> string list
  val collect_facts: induct_info list -> string list
  val INDUCT: string * induct_info list -> pre_scripts
  val STRONG_INDUCT: string * induct_info list -> pre_scripts
  val PROP_INDUCT: string * induct_info list -> pre_scripts
  val VAR_INDUCT: string * induct_info list -> pre_scripts
end;

structure Induct_ProofSteps : INDUCT_PROOFSTEPS =
struct

fun add_induct_data str (t, prfstep) = InductData.map (
      Symtab.map_default (str, []) (cons (t, prfstep)))

fun add_typed_induct_data str (ty, prfstep) =
    add_induct_data str (Term.dummy_pattern ty, prfstep)

fun get_typed_prfstep thy nm ty =
    let
      val tab = InductData.get thy
      fun typ_can_match t' =
          let val _ = typ_match thy (type_of t', ty) in true end
          handle Type.TYPE_MATCH => false
    in
      case Symtab.lookup tab nm of
          NONE => NONE
        | SOME lst =>
          case find_first (fn (t', _) => typ_can_match t') lst of
              NONE => NONE
            | SOME (_, prfstep) => SOME prfstep
    end

fun get_term_prfstep thy nm t =
    let
      val tab = InductData.get thy
      fun term_can_match t' =
          let val _ = Pattern.first_order_match thy (t', t) in true end
          handle Pattern.MATCH => false
    in
      case Symtab.lookup tab nm of
          NONE => NONE
        | SOME lst =>
          case find_first (fn (t', _) => term_can_match t') lst of
              NONE => NONE
            | SOME (_, prfstep) => SOME prfstep
    end

(* Context is all initial facts where at least one of freevars (subset
   of initial variables) appear. Return the list of initial facts and
   variables.
 *)
fun get_var_context id freevars st =
    let
      val init_vars = Status.get_all_init_vars st id
      val init_facts = (Status.get_all_init_facts st id)
                           |> filter (occurs_frees freevars o fst)
    in
      if subset (op aconv) (freevars, init_vars) andalso
         length (init_facts |> filter is_init_concl) <= 1
      then SOME (init_facts @ map (rpair InitVar) freevars)
      else NONE
    end

(* Check ind_th for simple induction is in the right form, and extract
   induction variable and hypothesis from ind_th.

   Returns (descs, (pat_var, pat_subst)), where descs is the trigger
   for induction ?n ~= base, pat_var is the induction variable ?n, and
   pat_subst is the inductive hypothesis P' ?n.
 *)
fun check_ind_th ind_th =
    let
      fun err str = "prfstep_induction: " ^ str
      val ((cond_base, cond_ind), concl) =
          strip_horn' ind_th |> apfst the_pair
          handle AUTO2 _ => raise AUTO2 (err "ind_th must have two hypotheses.")

      (* concl must be of form ?P ?n. *)
      val err_concl = err "concl of ind_th must be ?P ?n."
      val (P, pat_var) = Term.dest_comb concl
                         handle TERM _ => raise AUTO2 err_concl
      val _ = assert (is_Var P andalso is_Var pat_var andalso
                      (dest_Var P |> fst |> fst) = "P") err_concl

      (* cond_base must be of form ?P b, where b is base case for ?n. *)
      val err_base_hyp = err "Base assumption of ind_th must be ?P base."
      val (P', base) = Term.dest_comb cond_base
                       handle TERM _ => raise AUTO2 err_base_hyp
      val _ = assert (P' aconv P) err_base_hyp

      (* cond_ind must be of form !n. P' n --> ?P n, where P' is
         preceding case.
       *)
      val err_ind_hyp =
          err "Ind assumption of ind_th must be !n. P' n --> ?P n."
      val cond_ind' =
          case cond_ind of
              Const("HOL.All", _) $ Abs (_, _, ind') =>
              subst_bound (pat_var, ind')
            | _ => raise AUTO2 err_ind_hyp
      val (pat_subst, P_n) = HOLogic.dest_imp cond_ind'
      val _ = assert (P_n aconv concl) err_ind_hyp

      (* Trigger induction when we know some variable is not equal to base. *)
      val var = Var (("FREE", 0), type_of pat_var)
      val descs = [WithFact (HOLogic.Not $ (HOLogic.mk_eq (var, base)))]
    in
      (descs, (pat_var, pat_subst))
    end

fun induct_handler ind_th ctxt var (abs_vars, inits, _) neq0_th (t, th) =
    let
      val init_facts = inits |> filter_out is_init_var |> map fst |> rev
      val cinit_facts = map (cert ctxt) init_facts
      val nprems = length init_facts - 1

      (* First compute the case zero part of induction. *)
      val neq0 = neq0_th |> Thm.prop_of |> HOLogic.dest_Trueprop
                         |> get_neg |> HOLogic.mk_Trueprop |> cert ctxt
      val use_vardef_cv = Conv.arg_conv (rewr_obj_eq use_vardef_th)
      val neq0_th' =
          neq0_th |> rewrite_thm_to_contra_form
                  |> send_to_hyps neq0
                  |> fold Thm.implies_intr cinit_facts
                  |> rewrite_thm_from_contra_form
                  |> fold Thm.forall_intr (map (cert ctxt) (rev abs_vars))
                  |> apply_to_thm (to_obj_conv ctxt)
                  |> Thm.implies_intr neq0
                  |> Thm.forall_intr (cert ctxt var)
                  |> apply_to_thm (to_obj_conv ctxt)
      val p0_th = apply_to_thm use_vardef_cv neq0_th'

      (* Second step: Suc part of induction. *)
      val ct = cert ctxt t
      val th' = th |> fold Thm.implies_intr cinit_facts
                   |> rewrite_thm_from_contra_form
                   |> fold Thm.forall_intr (map (cert ctxt) (rev abs_vars))
                   |> apply_to_thm (to_obj_conv ctxt)
                   |> Thm.implies_intr ct
                   |> Thm.forall_intr (cert ctxt var)
                   |> apply_to_thm (to_obj_conv ctxt)
      val pl_th = [p0_th, th'] MRS ind_th
      val lvar = map Var (Term.add_vars (Thm.prop_of pl_th) [])
    in
      pl_th |> Thm.forall_intr (cert ctxt (the_single lvar))
            |> Thm.forall_elim (cert ctxt var)
            |> apply_to_thm (to_meta_all_conv ctxt)
            |> fold Thm.forall_elim (map (cert ctxt) abs_vars)
            |> apply_to_thm (to_meta_imp_conv_n nprems)
            |> rewrite_thm_to_contra_form
            |> send_all_to_hyps
    end

fun prfstep_induction name descs (pat_var, pat_subst) ind_th extra_vars =
    prfstep_custom
        name descs
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val _ = assert (Term.is_Var pat_var)
                             "prfstep_induction: pat_var must be Var"
              val trm_n = lookup_inst inst "FREE"
              val gen_vars = trm_n :: extra_vars
              val var_ctxt = get_var_context id gen_vars st
            in
              case var_ctxt of
                  NONE => []
                | SOME inits =>
                  (* Induction generalizing other variables. *)
                  let
                    val inits' = inits |> filter_out (
                          fn (t, ity) => t aconv trm_n andalso ity = InitVar)
                    val stmt = Status.get_neg_form ctxt inits'
                    val p = lambda_abstract trm_n (HOLogic.dest_Trueprop stmt)
                    val typ_P = (type_of pat_var) --> HOLogic.boolT
                    val inst =
                        (pattern_match ctxt (pat_var, trm_n))
                            |> apsnd (Vartab.update_new (("P", 0), (typ_P, p)))
                    val stmt' = (Envir.subst_term inst pat_subst)
                                    |> Envir.beta_norm |> HOLogic.mk_Trueprop
                    val init_facts = inits |> filter_out is_init_var |> map fst

                    (* Attempt to clear all retro hyps from neq0_th. *)
                    val neq0_th = the_single ths
                    val handlers = Status.get_all_handlers st id
                    val warn_clear = "Warning: unable to clear for induction:"
                    val neq0_th' =
                        SOME ((Status.invoke_handlers handlers neq0_th)
                                  RS @{thm HOL.not_sym})
                        handle AUTO2 _ => let
                          val _ = trace_fullthm_ctxt ctxt warn_clear neq0_th
                        in NONE end

                    fun ready (t, ts) =
                        forall (fn t' => t aconv t' orelse
                                         member (op aconv) init_facts t' orelse
                                         not (occurs_frees gen_vars t')) ts

                    fun handler (t, th) =
                        induct_handler
                            ind_th ctxt trm_n (extra_vars, inits, stmt)
                            (the neq0_th') (t, th)
                  in
                    if is_some neq0_th' then
                      [Update.AddItems {
                          id = id, raw_items =
                                   handler_ritems ctxt stmt' (ready, handler)}]
                    else []
                  end
            end)

fun add_prfstep_induction ind_th thy =
    let
      val (descs, pats as (pat_var, pat_subst)) = check_ind_th ind_th
      val ctxt = Proof_Context.init_global thy
      val name = name_of_thm ind_th
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^ (pretty_terms ctxt [pat_var, pat_subst] |> str))

      (* First part, automatic induction on unique free variables,
         generalizing no other variables.
       *)
      val descs' = descs @ [Filter (unique_free_filter "FREE")]
      val prfstep_auto = prfstep_induction name descs' pats ind_th []

      (* Second part, add user invoked proofstep. More general. *)
      val ty_var = type_of pat_var
      val name' = name ^ "@gen"
      val pre_prfstep = prfstep_induction name' descs pats ind_th
    in
      thy |> add_prfstep prfstep_auto
          |> add_typed_induct_data "induct" (ty_var, pre_prfstep)
    end

(* Check a strong induction theorem ind_th is of the right form, and
   extract the induction variable (with its type).
*)
fun check_strong_ind_th ind_th =
    let
      fun err str = "prfstep_strong_induction: " ^ str
      val (_, concl) =
          (Logic.strip_horn (Thm.prop_of ind_th))
              |> apsnd HOLogic.dest_Trueprop
              |> apfst the_single
          handle List.Empty =>
                 raise AUTO2 (err "ind_th must have one hypothesis.")

      (* concl must be of form ?P ?n. *)
      val err_concl = err "concl of ind_th must be ?P ?n."
      val (P, pat_var) = Term.dest_comb concl
                         handle TERM _ => raise AUTO2 err_concl
      val _ = assert (is_Var P andalso is_Var pat_var andalso
                      (dest_Var P |> fst |> fst) = "P") err_concl

      (* assum must be of form !!n. (!m. m < n --> ?P m) ==> ?P n.
         Check omitted.
       *)
    in
      pat_var
    end

(* Induction handler for strong induction. *)
fun strong_induct_handler ind_th ctxt var (abs_vars, inits, stmt) (t, th) =
    let
      val p = lambda_abstract var (HOLogic.dest_Trueprop stmt)
      val ct = cert ctxt t
      val init_facts = inits |> filter_out is_init_var |> map fst |> rev
      val cinit_facts = map (cert ctxt) init_facts
      val nprems = length init_facts - 1

      val pat_var = (Logic.strip_horn (Thm.prop_of ind_th))
                        |> snd |> HOLogic.dest_Trueprop |> Term.dest_comb |> snd
      val inst = (pattern_match_ty ctxt (type_of pat_var, type_of var),
                  Vartab.empty) |> update_env (("P", 0), p)
      val th' = th |> fold Thm.implies_intr cinit_facts
                   |> rewrite_thm_from_contra_form
                   |> fold Thm.forall_intr (map (cert ctxt) (rev abs_vars))
                   |> apply_to_thm (to_obj_conv ctxt)
                   |> Thm.implies_intr ct
                   |> Thm.forall_intr (cert ctxt var)
      val ind_th' = subst_thm ctxt inst ind_th
      val pl_th = Thm.implies_elim ind_th' th'
      val lvar = map Var (Term.add_vars (Thm.prop_of pl_th) [])
    in
      pl_th |> Thm.forall_intr (cert ctxt (the_single lvar))
            |> Thm.forall_elim (cert ctxt var)
            |> apply_to_thm (to_meta_all_conv ctxt)
            |> fold Thm.forall_elim (map (cert ctxt) abs_vars)
            |> apply_to_thm (to_meta_imp_conv_n nprems)
            |> rewrite_thm_to_contra_form
            |> send_all_to_hyps
    end

fun prfstep_strong_induction name descs ind_th extra_vars =
    prfstep_custom
        name descs
        (fn ((id, inst), _) => fn (st as {ctxt, ...}) =>
            let
              val trm_n = lookup_inst inst "FREE"
              val gen_vars = trm_n :: extra_vars
              val var_ctxt = get_var_context id gen_vars st
              val ty_var = type_of trm_n
            in
              case var_ctxt of
                  NONE => []
                | SOME inits =>
                  (* Strong induction. *)
                  let
                    val inits' = inits |> filter_out (
                          fn (t, ity) => t aconv trm_n andalso ity = InitVar)
                    val stmt = Status.get_neg_form ctxt inits'
                    val stmt' = Term.abstract_over
                                    (trm_n, HOLogic.dest_Trueprop stmt)
                    val less_const =
                        Const (@{const_name less},
                               ty_var --> ty_var --> HOLogic.boolT)
                    (* m < n --> stmt'. *)
                    val body = HOLogic.mk_imp (
                          less_const $ Free ("m", ty_var) $ trm_n, stmt')
                    (* !m. m < n --> stmt'. *)
                    val stmt'' = HOLogic.mk_Trueprop (
                          HOLogic.mk_all ("m", ty_var, body))
                    val init_facts = inits |> filter_out is_init_var |> map fst

                    fun ready (t, ts) =
                        forall (fn t' => t' aconv t orelse
                                         member (op aconv) init_facts t' orelse
                                         not (occurs_frees gen_vars t')) ts

                    fun handler (t, th) =
                        strong_induct_handler ind_th ctxt trm_n
                                              (extra_vars, inits, stmt) (t, th)
                  in
                    [Update.AddItems {
                        id = id, raw_items =
                                 handler_ritems ctxt stmt'' (ready, handler)}]
                  end
            end)

fun add_prfstep_strong_induction ind_th thy =
    let
      val name = name_of_thm ind_th
      val pat_var = check_strong_ind_th ind_th
      val ty_var = type_of pat_var
      val descs = [WithTerm (Var (("FREE", 0), (type_of pat_var)))]
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs))
      val pre_prfstep = prfstep_strong_induction name descs ind_th
    in
      thy |> add_typed_induct_data "strong_induct" (ty_var, pre_prfstep)
    end

(* Apply induction rule for an inductively defined proposition. The
   form of the rule is: f ?a_1 ... ?a_n ==> ... ==> ?P ?a_1
   ... ?a_n. The proofstep matches a fact of form f a_1 ... a_n. The
   simplest case is when all a_i's are free variables, and produces
   subgoals for each inductive case to prove ?P a_1 ... a_n. If some
   a_i is not a free variable, an equation v = a_i need to be
   introduced and removed at the end.
 *)
fun prfstep_prop_induction name descs ind_th extra_vars =
    prfstep_custom
        name descs
        (fn ((id, _), ths) => fn (st as {ctxt, ...}) =>
            let
              (* Matched statement is of form f a_1 ... a_n. *)
              val init_th = the_single ths
              val init_prop = Thm.prop_of init_th
              val (f, th_vars) =
                  Term.strip_comb (HOLogic.dest_Trueprop init_prop)
              val free_th_vars = filter Term.is_Free th_vars
              val all_free_vars = merge (op aconv) (free_th_vars, extra_vars)
              val var_ctxt = get_var_context id all_free_vars st

              val (init_assum, _) = Logic.dest_implies (Thm.prop_of ind_th)
              val (_, pat_vars) =
                  Term.strip_comb (HOLogic.dest_Trueprop init_assum)

              fun get_eq_prop (th_var, pat_var) =
                  if Term.is_Free th_var then NONE else
                  let
                    val ((nm, _), T) = Term.dest_Var pat_var
                    val (nm', _) =
                        the_single (Variable.variant_frees ctxt [] [(nm, T)])
                  in
                    SOME (HOLogic.mk_eq (th_var, Free (nm', T)))
                  end
              val eq_props = map get_eq_prop (th_vars ~~ pat_vars)
              val eq_props_lst = maps the_list eq_props

              fun get_new_th_var (th_var, eq_prop) =
                  case eq_prop of
                      NONE => th_var
                    | SOME eq => eq |> HOLogic.dest_eq |> snd
              val th_vars' = map get_new_th_var (th_vars ~~ eq_props)
              val init_prop' =
                  HOLogic.mk_Trueprop (Term.list_comb (f, th_vars'))
              val init_th' = assume_thm ctxt init_prop'

              val init_facts = Status.get_all_init_facts st id

              fun callback (id, th) =
                  let
                    val num_eqs = length eq_props_lst
                    val eq_cprops =
                        map (cert ctxt o HOLogic.mk_Trueprop) eq_props_lst
                    val new_th_vars = subtract (op aconv) th_vars th_vars'
                    val use_vardef_cv =
                        Conv.arg_conv (rewr_obj_eq use_vardef_th)
                    fun use_vardef (eq_cprop, new_th_var) th =
                        th |> Thm.implies_intr eq_cprop
                           |> Thm.forall_intr (cert ctxt new_th_var)
                           |> apply_to_thm (to_obj_conv ctxt)
                           |> apply_to_thm use_vardef_cv
                    val th' =
                        th |> apply_to_thm (to_meta_imp_conv_n num_eqs)
                           |> fold send_to_hyps eq_cprops
                           |> Thm.implies_intr (cert ctxt init_prop')
                           |> fold use_vardef (eq_cprops ~~ new_th_vars)
                           |> apply_to_thm to_meta_imp_conv
                    val th'_concl = Logic.strip_imp_concl (Thm.prop_of th')
                    val th'' = if th'_concl aconv @{prop False} then
                                 rewrite_thm_from_contra_form th'
                               else th'
                  in
                    [Update.thm_update (id, th'')]
                  end
            in
              case var_ctxt of
                  NONE => []
                | SOME inits =>
                  if not (exists (fn (t, _) => t aconv init_prop) init_facts)
                  then [] else
                  let
                    val init_facts =
                        inits |> filter_out (fn (t, _) => t aconv init_prop)
                              |> filter_out is_init_var
                              |> append (map (rpair InitVar) extra_vars)
                    val stmt =
                        (Status.get_neg_form ctxt init_facts)
                            |> HOLogic.dest_Trueprop
                            |> fold (curry HOLogic.mk_imp) (rev eq_props_lst)
                    val p = fold lambda_abstract (rev th_vars') stmt
                    val inst = fo_init |> update_env (("P", 0), p)
                    val ind_th' = (subst_thm ctxt inst ind_th)
                                      |> apply_to_thm (to_obj_conv_on_horn ctxt)
                  in
                    Update.apply_horn_clause (id, [init_th'] MRS ind_th')
                                             callback
                  end
            end)

fun add_prfstep_prop_induction ind_th thy =
    let
      (* Initial assumption is of form f ?a_1 ... ?a_n. *)
      val (init_assum, _) = Logic.dest_implies (Thm.prop_of ind_th)
      val (f, pat_vars) = Term.strip_comb (HOLogic.dest_Trueprop init_assum)
      val _ = assert (forall Term.is_Var pat_vars)
                     "prop_induction: arguments in ind_th must be variables."
      val idx_vars = (1 upto (length pat_vars)) ~~ pat_vars
      val pat_args = map (fn (i, pat_var) =>
                             Var (("FREE", i), (type_of pat_var))) idx_vars
      val pat = Term.list_comb (f, pat_args)
      val name = name_of_thm ind_th

      (* First part, automatic induction on initial facts at box [0],
         generalizing no other variables.
       *)
      val descs = [WithFact pat] @ [Filter (id_filter (equal [0]))]
      val prfstep_auto = prfstep_prop_induction name descs ind_th []

      (* Second part, add user invoked proofsteps. More general. *)
      val name' = name ^ "@gen"
      val descs' = [WithFact (HOLogic.dest_Trueprop init_assum)]
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs'))
      val pre_prfstep = prfstep_prop_induction name' descs' ind_th
    in
      thy |> add_prfstep prfstep_auto
          |> add_induct_data "prop_induct" (f, pre_prfstep)
    end

(* Apply induction rule for an inductively defined type. The form of
   the rule is: ... ==> ?P ?a, where the type of ?a is inductively
   defined. The proofstep matches terms 'a' that are free variables of
   the given type, and produces subgoals for each inductive case to
   prove ?P a.
 *)
fun prfstep_var_induction name descs ind_th extra_vars =
    prfstep_custom
        name descs
        (fn ((id, inst), _) => fn (st as {ctxt, ...}) =>
            let
              val trm_a = lookup_inst inst "FREE"
              val var_ctxt = get_var_context id (trm_a :: extra_vars) st
              val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
              val (_, pat_var) =
                  Term.dest_comb (HOLogic.dest_Trueprop ind_concl)
              val _ = assert (Term.is_Var pat_var)
                             "var_induction: concl of ind_th must be ?P ?var"
              val ((nm, idx), _) = Term.dest_Var pat_var
            in
              case var_ctxt of
                  NONE => []
                | SOME inits =>
                  let
                    val inits' = inits |> filter_out (
                          fn (t, ity) => t aconv trm_a andalso ity = InitVar)
                    val stmt = Status.get_neg_form ctxt inits'
                    val p = lambda_abstract trm_a (HOLogic.dest_Trueprop stmt)
                    val inst = fo_init |> update_env (("P", 0), p)
                                       |> update_env ((nm, idx), trm_a)
                    val ind_th' = (subst_thm ctxt inst ind_th)
                                      |> apply_to_thm (to_obj_conv_on_horn ctxt)
                  in
                    Update.apply_horn_clause
                        (id, ind_th') (Update.null_callback)
                  end
            end)

fun add_prfstep_var_induction ind_th thy =
    let
      val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
      val (_, pat_var) = Term.dest_comb (HOLogic.dest_Trueprop ind_concl)
      val _ = assert (Term.is_Var pat_var)
                     "var_induction: concl of ind_th must be ?P ?var"
      val descs = [WithTerm (Var (("FREE", 0), (type_of pat_var)))]
      val name = name_of_thm ind_th
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs))

      (* First part, automatic induction on unique free variables,
         generalizing no other variables.
       *)
      val descs' = descs @ [Filter (unique_free_filter "FREE")]
      val prfstep_auto = prfstep_var_induction name descs' ind_th []

      (* Second part, add user invoked proofstep. More general. *)
      val ty_var = type_of pat_var
      val name' = name ^ "@gen"
      val pre_prfstep = prfstep_var_induction name' descs ind_th
    in
      thy |> add_prfstep prfstep_auto
          |> add_typed_induct_data "var_induct" (ty_var, pre_prfstep)
    end

datatype induct_info = Arbitrary of string
                     | OnFact of string

val Arbitraries = map Arbitrary
fun is_arbitrary info = case info of Arbitrary _ => true | _ => false
fun is_fact info = case info of OnFact _ => true | _ => false
fun dest_arbitrary info =
    case info of Arbitrary str => str
               | _ => raise AUTO2 "dest_arbitrary: wrong type"
fun dest_fact info =
    case info of OnFact str => str
               | _ => raise AUTO2 "dest_fact: wrong type"
fun collect_arbitraries infos =
    infos |> filter is_arbitrary |> map dest_arbitrary
fun collect_facts infos = infos |> filter is_fact |> map dest_fact

fun INDUCT (var_name, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt var_name
      val ty = type_of var
      val pre_prfstep = the (get_typed_prfstep thy "induct" ty)
                        handle Option.Option =>
                               raise AUTO2 "INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val facts = (collect_facts ind_infos) |> map (Syntax.read_term ctxt)
                                            |> map HOLogic.mk_Trueprop
      val _ = assert (length facts = 1) "INDUCT: should have exactly one fact."
      val prfstep = pre_prfstep arbitraries
    in
      ([Script_Info {prfstep = prfstep, source = facts}], ctxt)
    end

fun STRONG_INDUCT (var_name, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt var_name
      val ty = type_of var
      val pre_prfstep = the (get_typed_prfstep thy "strong_induct" ty)
                        handle Option.Option =>
                               raise AUTO2 "STRONG_INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val prfstep = pre_prfstep arbitraries
      val source = [(TermConst ty) $ var]
    in
      ([Script_Info {prfstep = prfstep, source = source}], ctxt)
    end

fun PROP_INDUCT (str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = Syntax.read_term ctxt str
      val (f, _) = Term.strip_comb t
      val pre_prfstep = the (get_term_prfstep thy "prop_induct" f)
                        handle Option.Option =>
                               raise AUTO2 "PROP_INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val prfstep = pre_prfstep arbitraries
      val source = [HOLogic.mk_Trueprop t]
    in
      ([Script_Info {prfstep = prfstep, source = source}], ctxt)
    end

fun VAR_INDUCT (var_name, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt var_name
      val ty = type_of var
      val pre_prfstep = the (get_typed_prfstep thy "var_induct" ty)
                        handle Option.Option =>
                               raise AUTO2 "VAR_INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val prfstep = pre_prfstep arbitraries
      val source = [(TermConst ty) $ var]
    in
      ([Script_Info {prfstep = prfstep, source = source}], ctxt)
    end

end  (* structure Induct_ProofSteps. *)

open Induct_ProofSteps
