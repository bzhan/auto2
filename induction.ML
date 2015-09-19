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
  val get_var_context: box_id -> term list -> status ->
                       (term list * term list * term list) option
  val get_ind_var: term * term list -> term * term option * term list
  val get_ind_vars:
      term list * term list -> (term * term option) list * term list
  val use_var_eq: Proof.context -> term option -> thm -> thm
  val get_eq_handler: Proof.context -> term option -> raw_item list
  val clear_retro_hyps: box_id -> status -> thm -> thm option
  val process_neq0_th: term list * term list -> Proof.context -> thm -> thm
  val remove_pred_assum: thm -> term list -> term list * term list ->
                         Proof.context -> term * thm -> thm
  val get_induct_handler: term list * term list * term list -> Proof.context ->
                          thm -> term -> raw_item list
  val check_strong_ind_prop: term -> term list * term
  val apply_induction: box_id -> term list * term list * term list ->
                       (term * term option) list -> Proof.context -> thm ->
                       thm list -> Update.raw_update list
  val prfstep_strong_induction:
      theory -> string -> prfstep_descriptor list -> thm -> term list ->
      proofstep
  val add_prfstep_strong_induction: thm -> theory -> theory
  val check_ind_th: thm -> term * (term * term)
  val prfstep_induction:
      theory -> string -> prfstep_descriptor list -> thm -> string ->
      term list -> proofstep
  val add_prfstep_induction: thm -> theory -> theory
  val check_double_ind_th: thm -> (term * term) * (term list * term)
  val prfstep_double_induction:
      theory -> string -> prfstep_descriptor list -> thm -> string * string ->
      term list -> proofstep
  val add_prfstep_double_induction: thm -> theory -> theory
  val prfstep_prop_induction:
      theory -> string -> prfstep_descriptor list -> thm -> term list ->
      proofstep
  val add_prfstep_prop_induction: thm -> theory -> theory
  val prfstep_var_induction:
      theory -> string -> prfstep_descriptor list -> thm -> term list ->
      proofstep
  val add_prfstep_var_induction: thm -> theory -> theory

  datatype induct_info = Arbitrary of string
                       | OnFact of string
  val Arbitraries: string list -> induct_info list
  val collect_arbitraries: induct_info list -> string list
  val collect_facts: induct_info list -> string list
  val INDUCT: string * induct_info list -> pre_scripts
  val DOUBLE_INDUCT: (string * string) * induct_info list -> pre_scripts
  val STRONG_INDUCT: string * induct_info list -> pre_scripts
  val PROP_INDUCT: string * induct_info list -> pre_scripts
  val VAR_INDUCT: string * induct_info list -> pre_scripts
end;

structure Induct_ProofSteps : INDUCT_PROOFSTEPS =
struct

fun add_induct_data str (t, prfstep) =
    InductData.map (Symtab.map_default (str, []) (cons (t, prfstep)))

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
          let val _ = pattern_fo_match_thy thy (t', t) in true end
          handle Pattern.MATCH => false
    in
      case Symtab.lookup tab nm of
          NONE => NONE
        | SOME lst =>
          case find_first (fn (t', _) => term_can_match t') lst of
              NONE => NONE
            | SOME (_, prfstep) => SOME prfstep
    end

(* Context is all initial facts where at least one of vars (subset of
   initial variables) appear. Return the list of initial facts and
   variables.
 *)
fun get_var_context id vars st =
    let
      val init_vars = Status.get_all_init_vars st id
      val (init_assums, init_concls) =
          (Status.get_all_init_assums st id, Status.get_all_init_concls st id)
              |> apply2 (filter (occurs_frees vars))
    in
      if subset (op aconv) (vars, init_vars) andalso length init_concls <= 1
      then SOME (vars, init_assums, init_concls) else NONE
    end

(* Obtain free variable for induction. If trm_n is a free variable
   then use that. Otherwise, pull the head variable from vars_spec,
   and create equality between that variable and trm_n.
 *)
fun get_ind_var (trm_n, vars_spec) =
    if is_Free trm_n then (trm_n, NONE, vars_spec)
    else (hd vars_spec,
          SOME (HOLogic.mk_Trueprop (HOLogic.mk_eq (hd vars_spec, trm_n))),
          tl vars_spec)

(* List version of get_ind_var. *)
fun get_ind_vars (trms, vars_spec) =
    let
      fun append_ind_var t (prevs, vars_spec) =
          let val (ind_var, eq, vars_spec') = get_ind_var (t, vars_spec) in
            (prevs @ [(ind_var, eq)], vars_spec')
          end
    in
      fold append_ind_var trms ([], vars_spec)
    end

(* Given var_eq as returned by get_ind_var (either NONE or SOME
   (ind_var = trm_n), return a function thm -> thm that converts trm_n
   ~= 0 to ind_var ~= 0. The three arg(1)_conv goes inside Trueprop,
   Not, and Eq in reverse order.
 *)
fun use_var_eq ctxt var_eq =
    case var_eq of
        NONE => I
      | SOME eq => eq |> assume_thm ctxt |> obj_sym |> rewr_obj_eq
                      |> Conv.arg1_conv |> Conv.arg_conv |> Conv.arg_conv
                      |> apply_to_thm

(* Given var_eq as returned by get_ind_var, return the raw items
   specifying the new variable, equation, and handler.
 *)
fun get_eq_handler ctxt var_eq =
    case var_eq of
        NONE => []
      | SOME eq =>
        let
          val (ind_var, _) = eq |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
          fun eq_ready (t, ts) =
              forall (fn t' => t' aconv t orelse
                               not (occurs_free ind_var t')) ts
          fun eq_handler (t, th) =
              th |> Thm.implies_intr (cert ctxt t)
                 |> Thm.forall_intr (cert ctxt ind_var)
                 |> apply_to_thm (to_obj_conv ctxt)
                 |> apply_to_thm (Conv.arg_conv (rewr_obj_eq @{thm use_vardef}))
        in
          [var_to_fact ind_var] @
          Update.handler_ritems ctxt eq (eq_ready, eq_handler)
        end

(* Attempt to clear all retro hyps from th. This is used on the
   theorems verifying base cases of induction.
 *)
fun clear_retro_hyps id (st as {ctxt, ...}) th =
    let
      val handlers = Status.get_all_handlers st id
      val warn_clear = "Warning: unable to clear for induction:"
    in
      SOME (Status.invoke_handlers handlers th)
      handle AUTO2 _ => let
        val _ = trace_fullthm_ctxt ctxt warn_clear th
      in NONE end
    end

(* Given a theorem n ~= 0 (where 0 stands for the base case of
   induction, which is [] for lists, etc), depending on init_facts,
   construct theorem P 0, where P is the predicate
   !abs_vars. [init_facts] ==> False, written in negation form.
 *)
fun process_neq0_th (abs_vars, init_facts) ctxt neq0_th =
    let
      val cinit_facts = map (cert ctxt) init_facts
      val cabs_vars = map (cert ctxt) abs_vars
      val cvar_n = neq0_th |> prop_of' |> Term.dest_comb |> snd
                           |> Term.strip_comb |> snd |> hd |> cert ctxt
      val neq0 = neq0_th |> Thm.prop_of |> get_neg' |> cert ctxt
      val use_vardef_cv = Conv.arg_conv (rewr_obj_eq @{thm use_vardef})
    in
      neq0_th |> rewrite_thm_to_contra_form  (* n = 0 ==> False *)
              |> send_to_hyps neq0  (* [n = 0] ==> False *)
              |> fold Thm.implies_intr (rev cinit_facts)
              |> rewrite_thm_from_contra_form  (* [n = 0] ==> ~ init_facts *)
              |> fold Thm.forall_intr (rev cabs_vars)
              |> apply_to_thm (to_obj_conv ctxt)  (* [n = 0] ==> P n *)
              |> Thm.implies_intr neq0  (* n = 0 ==> P n *)
              |> Thm.forall_intr cvar_n  (* !!n. n = 0 ==> P n *)
              |> apply_to_thm (to_obj_conv ctxt)  (* !n. n = 0 --> P n *)
              |> apply_to_thm use_vardef_cv  (* P 0 *)
    end

(* Given ind_th of form !vars. P' vars --> P vars ==> P vars, and a
   theorem P vars depending on P' vars, remove t = P' vars from
   hypothesis using ind_th. Here P is !abs_vars. [init_facts] ==>
   False, written in negation form.
 *)
fun remove_pred_assum ind_th vars (abs_vars, init_facts) ctxt (t, th) =
    let
      val nprems = length init_facts - 1
      val cinit_facts = map (cert ctxt) init_facts
      val cabs_vars = map (cert ctxt) abs_vars
      val cvars = map (cert ctxt) vars
      val ct = cert ctxt t
    in
      (* begins with [P' vars, init_facts] ==> False *)
      th |> fold Thm.implies_intr (rev cinit_facts)
         |> rewrite_thm_from_contra_form  (* [P' vars] ==> ~ init_facts *)
         |> fold Thm.forall_intr (rev cabs_vars)
         |> apply_to_thm (to_obj_conv ctxt)  (* [P' vars] ==> P vars *)
         |> Thm.implies_intr ct  (* P' vars ==> P vars *)
         |> fold Thm.forall_intr (rev cvars)
         |> apply_to_thm (to_obj_conv ctxt)  (* !vars. P' vars --> P vars *)
         |> Thm.implies_elim ind_th  (* P vars *)
         |> apply_to_thm (to_meta_all_conv ctxt)
         |> fold Thm.forall_elim cabs_vars  (* ~ init_facts *)
         |> apply_to_thm (to_meta_imp_conv_n nprems)
         |> rewrite_thm_to_contra_form  (* init_facts ==> False *)
         |> send_all_to_hyps  (* [init_facts] ==> False *)
    end

(* Given informtion for an induction, return the induct handler. *)
fun get_induct_handler (ind_vars, abs_vars, init_facts) ctxt ind_th stmt =
    let
      val gen_vars = ind_vars @ abs_vars
      fun ready (t, ts) =
          forall (fn t' => t aconv t' orelse
                           member (op aconv) init_facts t' orelse
                           not (occurs_frees gen_vars t')) ts
      val handler =
          remove_pred_assum ind_th ind_vars (abs_vars, init_facts) ctxt
    in
      Update.handler_ritems ctxt stmt (ready, handler)
    end

(* Check a strong induction theorem ind_th is of the right form, and
   extract the induction variables and substitution.
 *)
fun check_strong_ind_prop ind_prop =
    let
      fun err str = "check_strong_ind_prop: " ^ str
      val (cond_ind, concl) =
          ind_prop |> Logic.dest_implies |> apply2 (HOLogic.dest_Trueprop)

      (* concl must be of form ?P [?vars]. *)
      val err_concl = err "concl of ind_th must be ?P [?vars]."
      val (P, pat_vars) = Term.strip_comb concl
                          handle TERM _ => raise AUTO2 err_concl
      val _ = assert (is_Var P andalso forall is_Var pat_vars andalso
                      (dest_Var P |> fst |> fst) = "P") err_concl

      (* cond_ind must be of form !n. P' n --> ?P n. Return the
         substitution pattern P'.
       *)
      val err_ind_hyp = err "cond_ind of ind_th must be !n. P' --> ?P vars."
      fun dest_one_all var body =
          case body of
              Const ("HOL.All", _) $ Abs (_, _, t) => subst_bound (var, t)
            | _ => raise AUTO2 err_ind_hyp
      val (pat_subst, P_vars) =
          cond_ind |> fold dest_one_all pat_vars |> HOLogic.dest_imp
      val _ = assert (P_vars aconv concl) err_ind_hyp
    in
      (pat_vars, pat_subst)
    end

fun apply_induction id var_ctxt var_infos ctxt ind_th prev_ths =
    let
      val thy = Proof_Context.theory_of ctxt
      val ind_vars = map fst var_infos

      (* Obtain pat_vars and pat_subst from the conclusion and
         induction hypothesis of ind_th.
       *)
      val (assums, concl) = Logic.strip_horn (Thm.prop_of ind_th)
      val _ = assert (length assums = length prev_ths + 1)
                     "apply_induction: wrong number of prev_ths"
      val ind_prop = Logic.mk_implies ((snd o split_last) assums, concl)
      val (pat_vars, pat_subst) = check_strong_ind_prop ind_prop

      val (vars, assums, concls) = var_ctxt
      val vars' = subtract (op aconv) ind_vars vars
      val assums' = maps (the_list o snd) var_infos @ assums
      val stmt = Status.get_neg_form ctxt (vars', assums', concls)
      val init_facts = assums' @ map get_neg' concls
      val p = stmt |> HOLogic.dest_Trueprop
                   |> fold lambda_abstract (rev ind_vars)
      val typ_P = fold (fn pat_var => fn ty => type_of pat_var --> ty)
                       (rev pat_vars) boolT
      val inst = fo_init |> fold (Pattern.match thy) (pat_vars ~~ ind_vars)
                         |> apsnd (Vartab.update_new (("P", 0), (typ_P, p)))
      val stmt' = (Envir.subst_term inst pat_subst)
                      |> Envir.beta_norm |> HOLogic.mk_Trueprop
      val ind_th' = ind_th |> subst_thm ctxt inst
                           |> fold Thm.elim_implies prev_ths
      val ind_ritems = get_induct_handler (ind_vars, vars', init_facts) ctxt
                                          ind_th' stmt'
      val eq_ritems = maps (get_eq_handler ctxt) (map snd var_infos)
    in
      [Update.AddItems {id = id, raw_items = ind_ritems @ eq_ritems}]
    end

fun prfstep_strong_induction thy name descs ind_th extra_vars =
    prfstep_custom
        thy name descs [Update.ADD_ITEMS]
        (fn ((id, inst), _) => fn (st as {ctxt, ...}) =>
            let
              val trm_n = lookup_inst inst "FREE"
              val _ = assert (is_Free trm_n)
                             "prfstep_strong_induction: var is not Free."
              val var_ctxt = get_var_context id (trm_n :: extra_vars) st
              val var_infos = [(trm_n, NONE)]
            in
              if is_none var_ctxt then []
              else apply_induction id (the var_ctxt) var_infos ctxt ind_th []
            end)

fun add_prfstep_strong_induction ind_th thy =
    let
      val name = name_of_thm ind_th
      val ctxt = Proof_Context.init_global thy
      val ind_th' = apply_to_thm (to_obj_conv_on_horn ctxt) ind_th
      val (pat_var, pat_subst) =
          check_strong_ind_prop (Thm.prop_of ind_th') |> apfst the_single
          handle List.Empty =>
                 raise AUTO2 "add_prfstep_strong_induction: more than one var."
      val ty_var = type_of pat_var
      val descs = [WithTerm (Var (("FREE", 0), (type_of pat_var)))]
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^ (pretty_terms ctxt [pat_var, pat_subst] |> str))
      val pre_prfstep = prfstep_strong_induction thy name descs ind_th'
    in
      thy |> add_typed_induct_data "strong_induct" (ty_var, pre_prfstep)
    end

(* Check ind_th for simple induction is in the right form, and extract
   induction variable and hypothesis from ind_th.

   Returns (base, (pat_var, pat_subst)), where base is the base case
   of induction, pat_var is the induction variable ?n, and pat_subst
   is the inductive hypothesis P' ?n.
 *)
fun check_ind_th ind_th =
    let
      val thy = Thm.theory_of_thm ind_th
      fun err str = "check_ind_th: " ^ str
      val (cond_base, ind_th') =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst (HOLogic.dest_Trueprop)

      (* cond_base must be of form ?P b, where b is base case for ?n. *)
      val err_base_hyp = err "Base assumption of ind_th must be ?P base."
      val inst = pattern_fo_match_thy thy (@{term_pat "?P ?b"}, cond_base)
                 handle Pattern.MATCH => raise AUTO2 err_base_hyp
      val base = lookup_inst inst "b"
    in
      (base, check_strong_ind_prop ind_th' |> apfst the_single)
    end

(* n_str is the name of the schematic variable in the pattern. If
   trm_n is a variable (which should be an initial variable),
   vars_spec specifies the list of arbitrary variables (as
   terms). Otherwise extra_vars is the new variable for trm_n followed
   by the list of arbitrary variables.
 *)
fun prfstep_induction thy name descs ind_th n_str vars_spec =
    prfstep_custom
        thy name descs [Update.ADD_ITEMS]
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val trm_n = lookup_inst inst n_str
              val (var_infos, extra_vars) = get_ind_vars ([trm_n], vars_spec)
              val (_, var_eq) = the_single var_infos
              val search_vars = filter is_Free [trm_n] @ extra_vars
              val var_ctxt = get_var_context id search_vars st
            in
              if is_none var_ctxt then [] else
              let
                val (_, assums, concls) = the var_ctxt
                val assums' = the_list var_eq @ assums
                val neq0_th = clear_retro_hyps id st (the_single ths)
              in
                if is_none neq0_th then [] else
                let
                  val init_facts = assums' @ map get_neg' concls
                  val p0_th =
                      neq0_th |> the |> use_var_eq ctxt var_eq
                              |> process_neq0_th (extra_vars, init_facts) ctxt
                in
                  apply_induction id (the var_ctxt) var_infos ctxt ind_th
                                  [p0_th]
                end
              end
            end)

fun add_prfstep_induction ind_th thy =
    let
      val (base, (pat_var, pat_subst)) = check_ind_th ind_th
      val ctxt = Proof_Context.init_global thy
      val name = name_of_thm ind_th

      (* First part, automatic induction on unique free variables,
         generalizing no other variables.
       *)
      val var = Var (("FREE", 0), type_of pat_var)
      val descs = [WithFact (HOLogic.Not $ (HOLogic.mk_eq (var, base))),
                   Filter (unique_free_filter "FREE")]
      val prfstep_auto = prfstep_induction thy name descs ind_th "FREE" []

      (* Second part, add user invoked proofstep. More general. *)
      val ty_var = type_of pat_var
      val name' = name ^ "@gen"
      val var' = Var (("n", 0), ty_var)
      val descs' = [WithFact (HOLogic.Not $ (HOLogic.mk_eq (var', base)))]
      val pre_prfstep = prfstep_induction thy name' descs' ind_th "n"
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs') ^ "\n" ^
            "Substitution: " ^ (pretty_terms ctxt [pat_var, pat_subst] |> str))
    in
      thy |> add_prfstep prfstep_auto
          |> add_typed_induct_data "induct" (ty_var, pre_prfstep)
    end

(* Check ind_th for a double induction is in the right form. *)
fun check_double_ind_th ind_th =
    let
      val thy = Thm.theory_of_thm ind_th
      fun err str = "check_double_ind_th: " ^ str
      val (cond_base1, (cond_base2, ind_th')) =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst (HOLogic.dest_Trueprop)
                 |> apsnd (Logic.dest_implies #> apfst (HOLogic.dest_Trueprop))

      (* cond_base1 must be of form !n. ?P mb n, where mb is the base
         case for ?m.
       *)
      val err_base_hyp1 =
          err "First base assumption of ind_th must be !n. ?P mb n."
      val inst1 = pattern_fo_match_thy
                      thy (@{term_pat "!n. ?P ?mb n"}, cond_base1)
                  handle Pattern.MATCH => raise AUTO2 err_base_hyp1
      val mb = lookup_inst inst1 "mb"

      (* cond_base2 must be of form !m. ?P m nb, where nb is the base
         case for ?n.
       *)
      val err_base_hyp2 =
          err "Second base assumption of ind_th must be !m. ?P m nb."
      val inst2 = pattern_fo_match_thy
                      thy (@{term_pat "!m. ?P m ?nb"}, cond_base2)
                  handle Pattern.MATCH => raise AUTO2 err_base_hyp2
      val nb = lookup_inst inst2 "nb"
    in
      ((mb, nb), check_strong_ind_prop ind_th')
    end

fun prfstep_double_induction thy name descs ind_th (m_str, n_str) vars_spec =
    prfstep_custom
        thy name descs [Update.ADD_ITEMS]
        (fn ((id, inst), ths) => fn (st as {ctxt, ...}) =>
            let
              val trms = map (lookup_inst inst) [m_str, n_str]
              val (var_infos, extra_vars) = get_ind_vars (trms, vars_spec)
              val ((ind_var1, eq1), (ind_var2, eq2)) = the_pair var_infos
              val search_vars = filter is_Free trms @ extra_vars
              val var_ctxt = get_var_context id search_vars st
            in
              if is_none var_ctxt then [] else
              let
                val (_, assums, concls) = the var_ctxt
                val assums' = the_list eq1 @ the_list eq2 @ assums
                val (neq0_th1, neq0_th2) =
                    apply2 (clear_retro_hyps id st) (the_pair ths)
              in
                if is_none neq0_th1 orelse is_none neq0_th2 then [] else
                let
                  val init_facts = assums' @ map get_neg' concls
                  (* Zero part of the induction. *)
                  val p0_th =
                      neq0_th1 |> the |> use_var_eq ctxt eq1
                               |> process_neq0_th (extra_vars, init_facts) ctxt
                               |> Thm.forall_intr (cert ctxt ind_var2)
                               |> apply_to_thm (to_obj_conv ctxt)
                  val p1_th =
                      neq0_th2 |> the |> use_var_eq ctxt eq2
                               |> process_neq0_th (extra_vars, init_facts) ctxt
                               |> Thm.forall_intr (cert ctxt ind_var1)
                               |> apply_to_thm (to_obj_conv ctxt)
                in
                  apply_induction id (the var_ctxt) var_infos ctxt ind_th
                                  [p0_th, p1_th]
                end
              end
            end)

fun add_prfstep_double_induction ind_th thy =
    let
      val ((mb, nb), (pat_vars, pat_subst)) = check_double_ind_th ind_th
      val ctxt = Proof_Context.init_global thy
      val name = name_of_thm ind_th
      val err = "add_prfstep_double_induction: should have two vars."
      val (pat_var1, pat_var2) =
          the_pair pat_vars handle AUTO2 _ => raise AUTO2 err

      (* Add user invoked proofstep. *)
      val (ty_var1, ty_var2) = apply2 type_of (pat_var1, pat_var2)
      val var1 = Var (("m", 0), ty_var1)
      val var2 = Var (("n", 0), ty_var2)
      val descs = [WithFact (HOLogic.Not $ (HOLogic.mk_eq (var1, mb))),
                   WithFact (HOLogic.Not $ (HOLogic.mk_eq (var2, nb)))]
      val pre_prfstep =
          prfstep_double_induction thy name descs ind_th ("m", "n")
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^
            (pretty_terms ctxt [pat_var1, pat_var2, pat_subst] |> str))
      val ty = HOLogic.mk_prodT (ty_var1, ty_var2)
    in
      thy |> add_typed_induct_data "double_induct" (ty, pre_prfstep)
    end

(* Apply induction rule for an inductively defined proposition. The
   form of the rule is: f ?a_1 ... ?a_n ==> ... ==> ?P ?a_1
   ... ?a_n. The proofstep matches a fact of form f a_1 ... a_n. The
   simplest case is when all a_i's are free variables, and produces
   subgoals for each inductive case to prove ?P a_1 ... a_n. If some
   a_i is not a free variable, an equation v = a_i need to be
   introduced and removed at the end.
 *)
fun prfstep_prop_induction thy name descs ind_th extra_vars =
    prfstep_custom
        thy name descs [Update.ADD_BOXES]
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
                    SOME (HOLogic.mk_eq (Free (nm', fastype_of th_var), th_var))
                  end
              val eq_props = map get_eq_prop (th_vars ~~ pat_vars)
              val eq_props_lst = maps the_list eq_props

              fun get_new_th_var (th_var, eq_prop) =
                  case eq_prop of
                      NONE => th_var
                    | SOME eq => eq |> HOLogic.dest_eq |> fst
              val th_vars' = map get_new_th_var (th_vars ~~ eq_props)
              val init_prop' =
                  HOLogic.mk_Trueprop (Term.list_comb (f, th_vars'))
              val init_th' = assume_thm ctxt init_prop'

              fun callback (id, th) =
                  let
                    val num_eqs = length eq_props_lst
                    val eq_cprops =
                        map (cert ctxt o HOLogic.mk_Trueprop) eq_props_lst
                    val new_th_vars = subtract (op aconv) th_vars th_vars'
                    val use_vardef_cv =
                        Conv.arg_conv (rewr_obj_eq @{thm use_vardef})
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
                    [Update.thm_update thy (id, th'')]
                  end

              val ninit_prop = get_neg' init_prop
            in
              case var_ctxt of
                  NONE => []
                | SOME (_, assums, concls) =>
                  if not (member (op aconv) assums init_prop) andalso
                     not (member (op aconv) concls ninit_prop) then [] else
                  let
                    val assums' = remove (op aconv) init_prop assums
                    val concls' = remove (op aconv) ninit_prop concls
                    val stmt =
                        (extra_vars, assums', concls')
                            |> Status.get_neg_form ctxt |> HOLogic.dest_Trueprop
                            |> fold (curry HOLogic.mk_imp) (rev eq_props_lst)
                    val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
                    val (P, _) = ind_concl |> HOLogic.dest_Trueprop
                                           |> Term.strip_comb
                    val p = fold lambda_abstract (rev th_vars') stmt
                    val inst = pattern_match ctxt (P, p)
                    val ind_th' = (subst_thm ctxt inst ind_th)
                                      |> apply_to_thm (to_obj_conv_on_horn ctxt)
                  in
                    Update.apply_horn_clause
                        thy (id, [init_th'] MRS ind_th') callback
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
      val prfstep_auto = prfstep_prop_induction thy name descs ind_th []

      (* Second part, add user invoked proofsteps. More general. *)
      val name' = name ^ "@gen"
      val descs' = [WithFact (HOLogic.dest_Trueprop init_assum)]
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs'))
      val pre_prfstep = prfstep_prop_induction thy name' descs' ind_th
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
fun prfstep_var_induction thy name descs ind_th extra_vars =
    prfstep_custom
        thy name descs [Update.ADD_BOXES]
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
                | SOME (vars, assums, concls) =>
                  let
                    val vars' = remove (op aconv) trm_a vars
                    val stmt = Status.get_neg_form ctxt (vars', assums, concls)
                    val p = lambda_abstract trm_a (HOLogic.dest_Trueprop stmt)
                    val inst = fo_init |> update_env (("P", 0), p)
                                       |> update_env ((nm, idx), trm_a)
                    val ind_th' = (subst_thm ctxt inst ind_th)
                                      |> apply_to_thm (to_obj_conv_on_horn ctxt)
                  in
                    Update.apply_horn_clause
                        thy (id, ind_th') (Update.null_callback)
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
      val prfstep_auto = prfstep_var_induction thy name descs' ind_th []

      (* Second part, add user invoked proofstep. More general. *)
      val ty_var = type_of pat_var
      val name' = name ^ "@gen"
      val pre_prfstep = prfstep_var_induction thy name' descs ind_th
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

fun INDUCT (var_spec_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var_spec = Syntax.read_term ctxt var_spec_str
      val (ty, new_var, ctxt') =
          case var_spec of
              Const ("HOL.eq", _) $ lhs $ _ =>
              (type_of lhs, [lhs],
               ctxt |> Variable.add_fixes_direct [lhs |> Term.dest_Free |> fst]
                    |> Variable.declare_term lhs)
            | _ =>  (type_of var_spec, [], ctxt)

      val pre_prfstep = the (get_typed_prfstep thy "induct" ty)
                        handle Option.Option =>
                               raise AUTO2 "INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val facts = (collect_facts ind_infos)
                      |> map (Syntax.read_term ctxt)
                      |> map (fn t => (TY_PROP, [t]))
      val _ = assert (length facts = 1) "INDUCT: should have exactly one fact."
      val prfstep = pre_prfstep (new_var @ arbitraries)
    in
      ([Script_Info {prfstep = prfstep, source = facts}], ctxt')
    end

fun DOUBLE_INDUCT ((var_spec_str1, var_spec_str2), ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      (* Returns type, variable, and new context. *)
      fun process_spec_str var_spec_str ctxt =
          let val var_spec = Syntax.read_term ctxt var_spec_str in
            case Syntax.read_term ctxt var_spec_str of
                Const ("HOL.eq", _) $ lhs $ _ =>
                (type_of lhs, [lhs],
                 ctxt |> Variable.add_fixes_direct [lhs |> Term.dest_Free
                                                        |> fst]
                      |> Variable.declare_term lhs)
              | _ => (type_of var_spec, [], ctxt)
          end

      val (ty1, new_var1, ctxt') = process_spec_str var_spec_str1 ctxt
      val (ty2, new_var2, ctxt'') = process_spec_str var_spec_str2 ctxt'
      val ty = HOLogic.mk_prodT (ty1, ty2)
      val new_vars = new_var1 @ new_var2

      val pre_prfstep = the (get_typed_prfstep thy "double_induct" ty)
                        handle Option.Option =>
                               raise AUTO2 "DOUBLE_INDUCT: proofstep not found."
      val arbitraries = (collect_arbitraries ind_infos)
                            |> map (Syntax.read_term ctxt)
      val facts = (collect_facts ind_infos)
                      |> map (Syntax.read_term ctxt)
                      |> map (fn t => (TY_PROP, [t]))
      val _ = assert (length facts = 2) "INDUCT: should have exactly one fact."
      val prfstep = pre_prfstep (new_vars @ arbitraries)
    in
      ([Script_Info {prfstep = prfstep, source = facts}], ctxt'')
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
      val source = [(TY_TERM, [var])]
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
      val source = [(TY_PROP, [t])]
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
      val source = [(TY_TERM, [var])]
    in
      ([Script_Info {prfstep = prfstep, source = source}], ctxt)
    end

end  (* structure Induct_ProofSteps. *)

open Induct_ProofSteps
