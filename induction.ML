(* Induction related proof steps. *)

structure InductData =
Theory_Data (
  type T = ((term * thm) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (eq_fst (op =))
)

signature INDUCT_PROOFSTEPS =
sig
  val add_induct_data: string -> term * thm -> theory -> theory
  val add_typed_induct_data: string -> typ * thm -> theory -> theory
  val get_typed_ind_th: theory -> string -> typ -> thm option
  val get_term_ind_th: theory -> string -> term -> thm option
  val get_var_context: box_id -> term list -> status ->
                       (term list * term list) option
  val use_var_eq: Proof.context -> term option -> thm -> thm
  val get_eq_handler: Proof.context -> term option -> raw_item list
  val get_new_vars: term option -> term list
  val process_neq0_th: box_id -> term list * term list -> status -> thm -> thm
  val remove_pred_assum: thm -> term list -> term list * term list ->
                         Proof.context -> term * thm -> thm
  val get_induct_handler: term list * term list * term list -> Proof.context ->
                          thm -> term -> raw_item list
  val check_strong_ind_prop: term -> term list * term
  val apply_induction: term list * term list -> (term * term option) list ->
                       Proof.context -> thm -> thm list -> raw_item list
  val add_prfstep_strong_induction: thm -> theory -> theory
  val add_prfstep_upper_strong_induction: thm -> theory -> theory
  val check_ind_th: thm -> term * (term * term)
  val prfstep_induction: string -> prfstep_descriptor list -> thm -> proofstep
  val add_prfstep_induction: thm -> theory -> theory
  val check_double_ind_th: thm -> (term * term) * (term list * term)
  val add_prfstep_double_induction: thm -> theory -> theory
  val prfstep_prop_induction:
      string -> prfstep_descriptor list -> thm -> proofstep
  val add_prfstep_prop_induction: thm -> theory -> theory
  val prfstep_var_induction:
      string -> prfstep_descriptor list -> thm -> proofstep
  val add_prfstep_var_induction: thm -> theory -> theory

  datatype induct_info = Arbitrary of string | ApplyOn of string
  val Arbitraries: string list -> induct_info list
  val collect_arbitraries: Proof.context -> induct_info list -> term list
  val ApplyOns: string list -> induct_info list
  val collect_apply_ons: Proof.context -> induct_info list -> term list
  val process_var_spec_str: Proof.context -> string -> term * term * term option
  val INDUCT: string * induct_info list -> pre_scripts
  val DOUBLE_INDUCT: (string * string) * induct_info list -> pre_scripts
  val STRONG_INDUCT: string * induct_info list -> pre_scripts
  val UPPER_STRONG_INDUCT: string * string * induct_info list -> pre_scripts
  val PROP_INDUCT: string * induct_info list -> pre_scripts
  val VAR_INDUCT: string * induct_info list -> pre_scripts
end;

structure Induct_ProofSteps : INDUCT_PROOFSTEPS =
struct

fun add_induct_data str (t, ind_th) =
    InductData.map (Symtab.map_default (str, []) (cons (t, ind_th)))

fun add_typed_induct_data str (ty, ind_th) =
    add_induct_data str (Term.dummy_pattern ty, ind_th)

fun get_typed_ind_th thy nm ty =
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
            | SOME (_, ind_th) => SOME ind_th
    end

fun get_term_ind_th thy nm t =
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
            | SOME (_, ind_th) => SOME ind_th
    end

(* Context is all initial facts where at least one of vars (subset of
   initial variables) appear. Return the list of initial facts and
   variables.
 *)
fun get_var_context id vars st =
    let
      val init_vars = Status.get_init_vars st id
      val init_assums = (Status.get_init_assums st id)
                            |> filter (occurs_frees vars)
    in
      if subset (op aconv) (vars, init_vars) then
        SOME (vars, init_assums)
      else NONE
    end

(* Given var_eq as either NONE or SOME (ind_var = trm_n), return a
   function thm -> thm that converts trm_n ~= 0 to ind_var ~= 0. The
   two arg(1)_conv goes inside Not, and Eq in reverse order.
 *)
fun use_var_eq ctxt var_eq =
    case var_eq of
        NONE => I
      | SOME eq => eq |> assume_thm ctxt |> obj_sym |> rewr_obj_eq
                      |> Conv.arg1_conv |> Conv.arg_conv |> apply_to_thm'

(* Given var_eq as either NONE or SOME (ind_var = trm_n), return the
   raw items specifying the new variable, equation, and handler.
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
                 |> apply_to_thm' (rewr_obj_eq @{thm use_vardef})
        in
          [var_to_fact ind_var] @
          Update.handler_ritems ctxt eq (eq_ready, eq_handler)
        end

(* Obtain new variables (if any) indicated by var_eq. *)
fun get_new_vars var_eq =
    case var_eq of
        NONE => []
      | SOME eq => [eq |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst]

(* Given a theorem n ~= 0 (where 0 stands for the base case of
   induction, which is [] for lists, etc), depending on init_facts,
   construct theorem P 0, where P is the predicate
   !abs_vars. [init_facts] ==> False, written in negation form.
 *)
fun process_neq0_th id (abs_vars, init_facts) (st as {ctxt, ...}) neq0_th =
    let
      val handlers = map (pair false) (Status.get_handlers st id)
      val cinit_facts = map (cert ctxt) init_facts
      val cabs_vars = map (cert ctxt) abs_vars
      val cvar_n = neq0_th |> prop_of' |> dest_arg
                           |> dest_args |> hd |> cert ctxt
      val neq0 = neq0_th |> Thm.prop_of |> get_neg' |> cert ctxt
      val use_vardef_cv = Conv.arg_conv (rewr_obj_eq @{thm use_vardef})
    in
      neq0_th |> Status.invoke_handlers handlers
              |> rewrite_thm_to_contra_form  (* n = 0 ==> False *)
              |> send_to_hyps neq0  (* [n = 0] ==> False *)
              |> fold Thm.implies_intr (rev cinit_facts)
              |> rewrite_thm_from_contra_form  (* [n = 0] ==> ~ init_facts *)
              |> fold Thm.forall_intr (rev cabs_vars)
              |> apply_to_thm (to_obj_conv ctxt)  (* [n = 0] ==> P n *)
              |> Thm.implies_intr neq0  (* n = 0 ==> P n *)
              |> Thm.forall_intr cvar_n  (* !!n. n = 0 ==> P n *)
              |> apply_to_thm (to_obj_conv ctxt)  (* !n. n = 0 --> P n *)
              |> apply_to_thm use_vardef_cv  (* P 0 *)
      handle AUTO2 _ => raise AUTO2 "apply_induction: unable to process neq0_th"
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
      (* Begins with [P' vars, init_facts] ==> False *)
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

(* Here ind_th is the induction theorem A_1 ==> ... ==> A_n ==> C. The
   given prev_ths are matched against A_1, ... A_{n-1}. The conclusion
   C is of the form ?P ?n_1 ... ?n_k. The matching process can be
   subtle, as the instantiation of ?P has to be constructed manually.
 *)
fun apply_induction var_ctxt var_infos ctxt ind_th prev_ths =
    let
      val thy = Proof_Context.theory_of ctxt
      val ind_vars = map fst var_infos

      (* Obtain pat_vars and pat_subst from the conclusion and
         induction hypothesis of ind_th.
       *)
      val (ind_assums, ind_concl) = Logic.strip_horn (Thm.prop_of ind_th)
      val _ = assert (length ind_assums = length prev_ths + 1)
                     "apply_induction: wrong number of prev_ths"
      val ind_prop = Logic.mk_implies (List.last ind_assums, ind_concl)
      val (pat_vars, pat_subst) = check_strong_ind_prop ind_prop

      (* First, we obtain the instantiation of ?P (term p). *)
      val (vars, assums) = var_ctxt
      val vars' = subtract (op aconv) ind_vars vars
      val assums' = maps (the_list o snd) var_infos @ assums
      val stmt = Update.get_neg_form
                     ctxt (Update.build_init_infos (vars', assums'))
      val p = stmt |> HOLogic.dest_Trueprop
                   |> fold lambda_abstract (rev ind_vars)
      val typ_P = fold (fn pat_var => fn ty => type_of pat_var --> ty)
                       (rev pat_vars) boolT
      val inst = fo_init |> fold (Pattern.match thy) (pat_vars ~~ ind_vars)
                         |> apsnd (Vartab.update_new (("P", 0), (typ_P, p)))

      (* Having matched ?P and the arguments ?n_i, we obtain
         instantiations of any remaining schematic variables A_1,
         ... A_{n_1} by matching with statements of prev_ths.
       *)
      val prev_pats = ind_assums |> split_last |> fst
                                 |> map (subst_term_norm inst)
      val prev_ts = prev_ths |> map Thm.prop_of |> map (subst_term_norm inst)
      val inst' = inst |> fold (Pattern.match thy) (prev_pats ~~ prev_ts)

      (* Finally, substitute using the full instantiation. *)
      val stmt' = HOLogic.mk_Trueprop (subst_term_norm inst' pat_subst)
      val ind_th' = ind_th |> subst_thm ctxt inst'
                           |> fold Thm.elim_implies prev_ths
      val ind_ritems =
          get_induct_handler (ind_vars, vars', assums') ctxt ind_th' stmt'
      val eq_ritems = maps (get_eq_handler ctxt) (map snd var_infos)
    in
      ind_ritems @ eq_ritems
    end

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
      val _ = writeln (name ^ "\nSubstitution: " ^
                       (pretty_terms ctxt [pat_var, pat_subst] |> str))
    in
      thy |> add_typed_induct_data "strong_induct" (ty_var, ind_th')
    end

fun add_prfstep_upper_strong_induction ind_th thy =
    let
      val name = name_of_thm ind_th
      val ctxt = Proof_Context.init_global thy
      val ind_th' = apply_to_thm (to_obj_conv_on_horn ctxt) ind_th
      val (pat_var, pat_subst) =
          check_strong_ind_prop (ind_th' |> Thm.prop_of |> Logic.dest_implies
                                         |> snd) |> apfst the_single
          handle List.Empty =>
                 raise AUTO2 "upper_strong_induction: more than one var."
      val ty_var = type_of pat_var
      val _ = writeln (name ^ "\nSubstitution: " ^
                       (pretty_terms ctxt [pat_var, pat_subst] |> str))
    in
      thy |> add_typed_induct_data "upper_strong_induct" (ty_var, ind_th')
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

(* descs is of the form ?FREE = base. *)
fun prfstep_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, inst), ths) => fn _ => fn (st as {ctxt, ...}) =>
            let
              val trm_n = lookup_inst inst "FREE"
              val _ = assert (is_Free trm_n)
                             "prfstep_induction: trm_n should be a variable."
              val var_ctxt = get_var_context id [trm_n] st
            in
              if is_none var_ctxt then [] else
              let
                val (_, assums) = the var_ctxt
                val neq0_th = the_single ths

                val p0_th = neq0_th |> process_neq0_th id ([], assums) st
                val var_infos = [(trm_n, NONE)]
                val ritems =
                    apply_induction (the var_ctxt) var_infos ctxt ind_th [p0_th]
              in
                [Update.AddItems {id = id, raw_items = ritems}]
              end
            end)

fun add_prfstep_induction ind_th thy =
    let
      val (base, (pat_var, pat_subst)) = check_ind_th ind_th
      val ctxt = Proof_Context.init_global thy
      val name = name_of_thm ind_th

      (* Automatic induction on unique free variables, generalizing no
         other variables.
       *)
      val var = Var (("FREE", 0), type_of pat_var)
      val descs = [WithFact (HOLogic.Not $ (HOLogic.mk_eq (var, base))),
                   Filter (unique_free_filter "FREE")]
      val prfstep = prfstep_induction name descs ind_th

      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^ (pretty_terms ctxt [pat_var, pat_subst] |> str))

      val ty_var = type_of pat_var
    in
      thy |> add_prfstep prfstep
          |> add_typed_induct_data "induct" (ty_var, ind_th)
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
      val _ = writeln (
            name ^ "\n" ^ (string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^
            (pretty_terms ctxt [pat_var1, pat_var2, pat_subst] |> str))
      val ty = HOLogic.mk_prodT (ty_var1, ty_var2)
    in
      thy |> add_typed_induct_data "double_induct" (ty, ind_th)
    end

(* Apply induction rule for an inductively defined proposition. The
   form of the rule is: f ?a_1 ... ?a_n ==> ... ==> ?P ?a_1
   ... ?a_n. The function matches a fact of form f a_1 ... a_n. The
   simplest case is when all a_i's are free variables, and produces
   subgoals for each inductive case to prove ?P a_1 ... a_n. If some
   a_i is not a free variable, an equation v = a_i need to be
   introduced and removed at the end.
 *)
fun apply_prop_induction (id, init_th) ind_th extra_vars (st as {ctxt, ...}) =
    let
      (* init_th is of the form f a_1 ... a_n. *)
      val init_prop = Thm.prop_of init_th
      val (f, th_vars) = Term.strip_comb (HOLogic.dest_Trueprop init_prop)
      val free_th_vars = filter Term.is_Free th_vars
      val all_free_vars = merge (op aconv) (free_th_vars, extra_vars)
      val var_ctxt = get_var_context id all_free_vars st

      val (init_assum, _) = Logic.dest_implies (Thm.prop_of ind_th)
      val pat_vars = dest_args (HOLogic.dest_Trueprop init_assum)

      fun get_eq_prop (th_var, pat_var) =
          if Term.is_Free th_var then NONE else
          let
            val ((nm, _), T) = Term.dest_Var pat_var
            val (nm', _) = the_single (Variable.variant_frees ctxt [] [(nm, T)])
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
      val init_prop' = HOLogic.mk_Trueprop (Term.list_comb (f, th_vars'))
      val init_th' = assume_thm ctxt init_prop'

      fun callback (id, th) =
          let
            val num_eqs = length eq_props_lst
            val eq_cprops = map (cert ctxt o HOLogic.mk_Trueprop) eq_props_lst
            val new_th_vars = subtract (op aconv) th_vars th_vars'
            val use_vardef_cv = Conv.arg_conv (rewr_obj_eq @{thm use_vardef})
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
            val th'' = if Thm.concl_of th' aconv @{prop False} then
                         rewrite_thm_from_contra_form th'
                       else th'
          in
            [Update.thm_update (id, send_all_to_hyps th'')]
          end
    in
      case var_ctxt of
          NONE => []
        | SOME (_, assums) =>
          if not (member (op aconv) assums init_prop) then []
          else let
            val assums' = remove (op aconv) init_prop assums
            val stmt = (Update.build_init_infos (extra_vars, assums'))
                           |> Update.get_neg_form ctxt |> HOLogic.dest_Trueprop
                           |> fold (curry HOLogic.mk_imp) (rev eq_props_lst)
            val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
            val P = ind_concl |> HOLogic.dest_Trueprop |> Term.head_of
            val p = fold lambda_abstract (rev th_vars') stmt
            val inst = pattern_match ctxt (P, p)
            val ind_th' = (subst_thm ctxt inst ind_th)
                              |> apply_to_thm (to_obj_conv_on_horn ctxt)
          in
            Update.apply_horn_clause (id, [init_th'] MRS ind_th') callback
          end
    end

(* Proofstep invoking apply_prop_induction. *)
fun prfstep_prop_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn st =>
            apply_prop_induction (id, the_single ths) ind_th [] st)

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

      (* Automatic induction on initial facts at box [0], generalizing
         no other variables.
       *)
      val descs = [WithFact pat] @ [Filter (id_filter (equal [0]))]
      val prfstep = prfstep_prop_induction name descs ind_th
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs))
    in
      thy |> add_prfstep prfstep
          |> add_induct_data "prop_induct" (f, ind_th)
    end

(* Apply induction rule for an inductively defined type. The form of
   the rule is: ... ==> ?P ?a, where the type of ?a is inductively
   defined. The function matches terms 'a' that are free variables of
   the given type, and produces subgoals for each inductive case to
   prove ?P a.
 *)
fun apply_var_induction (id, var) ind_th extra_vars (st as {ctxt, ...}) =
    let
      val var_ctxt = get_var_context id (var :: extra_vars) st
      val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
      val pat_var = dest_arg (HOLogic.dest_Trueprop ind_concl)
      val _ = assert (Term.is_Var pat_var)
                     "var_induction: concl of ind_th must be ?P ?var"
      val ((nm, idx), _) = Term.dest_Var pat_var
    in
      case var_ctxt of
          NONE => []
        | SOME (vars, assums) =>
          let
            val vars' = remove (op aconv) var vars
            val stmt = Update.get_neg_form ctxt (
                  Update.build_init_infos (vars', assums))
            val p = lambda_abstract var (HOLogic.dest_Trueprop stmt)
            val inst = fo_init |> update_env (("P", 0), p)
                               |> update_env ((nm, idx), var)
            val ind_th' = (subst_thm ctxt inst ind_th)
                              |> apply_to_thm (to_obj_conv_on_horn ctxt)
          in
            Update.apply_horn_clause (id, ind_th') (Update.null_callback)
          end
    end

(* Proofstep invoking apply_var_induction. *)
fun prfstep_var_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, inst), _) => fn _ => fn st =>
            apply_var_induction (id, lookup_inst inst "FREE") ind_th [] st)

fun add_prfstep_var_induction ind_th thy =
    let
      val ind_concl = Logic.strip_imp_concl (Thm.prop_of ind_th)
      val pat_var = dest_arg (HOLogic.dest_Trueprop ind_concl)
      val _ = assert (Term.is_Var pat_var)
                     "var_induction: concl of ind_th must be ?P ?var"

      (* Automatic induction on unique free variables, generalizing no
         other variables.
       *)
      val descs = [WithTerm (Var (("FREE", 0), (type_of pat_var))),
                   Filter (unique_free_filter "FREE")]
      val name = name_of_thm ind_th
      val prfstep = prfstep_var_induction name descs ind_th
      val _ = writeln (name ^ "\n" ^ (string_of_descs thy descs))
    in
      thy |> add_prfstep prfstep
          |> add_typed_induct_data "var_induct" (type_of pat_var, ind_th)
    end

datatype induct_info = Arbitrary of string | ApplyOn of string

val Arbitraries = map Arbitrary
fun collect_arbitraries ctxt infos =
    infos |> maps (fn info => case info of Arbitrary str => [str] | _ => [])
          |> map (read_term ctxt)
val ApplyOns = map ApplyOn
fun collect_apply_ons ctxt infos =
    infos |> maps (fn info => case info of ApplyOn str => [str] | _ => [])
          |> map (read_term ctxt)

fun process_var_spec_str ctxt var_spec_str =
    let
      val var_spec = read_term ctxt var_spec_str
    in
      case var_spec of
          Const ("HOL.eq", _) $ lhs $ rhs =>
          (lhs, rhs, SOME (HOLogic.mk_Trueprop var_spec))
        | Free _ => (var_spec, var_spec, NONE)
        | _ => raise AUTO2 "INDUCT: var_spec is either eqn or variable."
    end

fun get_neq0_th (t, base) =
    let
      val base' = case base of
                      Const (nm, _) => Const (nm, type_of t)
                    | _ => raise AUTO2 "INDUCT: base is not a constant."
    in
      HOLogic.mk_eq (t, base')
    end

fun INDUCT (var_spec_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val (var, rhs, var_eq) = process_var_spec_str ctxt var_spec_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "INDUCT: ind_th not found."
      val (base, _) = check_ind_th ind_th
      val neq0 = HOLogic.mk_Trueprop (get_neq0_th (rhs, base))
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = filter is_Free [rhs] @ arbitraries

      fun callback ((id, neq0_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "INDUCT: cannot get var context."
            val (_, assums) = the var_ctxt
            val assums' = the_list var_eq @ assums

            val var_infos = [(var, var_eq)]
            val p0_th =
                neq0_th |> use_var_eq ctxt var_eq
                        |> process_neq0_th id (arbitraries, assums') st
            val ritems =
                apply_induction (the var_ctxt) var_infos ctxt ind_th [p0_th]
          in
            [Update.thm_update (id, neq0_th),
             Update.AddItems {id = id, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [Update.InitAssum neq0], subs = [], cb = callback,
                    end_vars = get_new_vars var_eq}]
    end

fun DOUBLE_INDUCT ((var_spec_str1, var_spec_str2), ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      val (var1, rhs1, eq1) = process_var_spec_str ctxt var_spec_str1
      val (var2, rhs2, eq2) = process_var_spec_str ctxt var_spec_str2
      val ty = HOLogic.mk_prodT (type_of var1, type_of var2)

      val ind_th = the (get_typed_ind_th thy "double_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "DOUBLE_INDUCT: ind_th not found."
      val ((mb, nb), _) = check_double_ind_th ind_th
      val neq0 = HOLogic.mk_Trueprop (
            HOLogic.mk_disj (get_neq0_th (rhs1, mb), get_neq0_th (rhs2, nb)))
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = filter is_Free [rhs1, rhs2] @ arbitraries

      fun callback ((id, neq0_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "DOUBLE_INDUCT: cannot get var context."
            val (_, assums) = the var_ctxt
            val assums' = the_list eq1 @ the_list eq2 @ assums
            val (neq0_th1, neq0_th2) = the_pair (split_not_disj_th neq0_th)

            val p0_th =
                neq0_th1 |> use_var_eq ctxt eq1
                         |> process_neq0_th id (arbitraries, assums') st
                         |> Thm.forall_intr (cert ctxt var2)
                         |> apply_to_thm (to_obj_conv ctxt)
            val p1_th =
                neq0_th2 |> use_var_eq ctxt eq2
                         |> process_neq0_th id (arbitraries, assums') st
                         |> Thm.forall_intr (cert ctxt var1)
                         |> apply_to_thm (to_obj_conv ctxt)
            val var_infos = [(var1, eq1), (var2, eq2)]
            val ritems = apply_induction (the var_ctxt) var_infos ctxt ind_th
                                         [p0_th, p1_th]
          in
            [Update.thm_update (id, neq0_th),
             Update.AddItems {id = id, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [Update.InitAssum neq0], subs = [], cb = callback,
                    end_vars = maps get_new_vars [eq1, eq2]}]
    end

fun STRONG_INDUCT (var_spec_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val (var, rhs, var_eq) = process_var_spec_str ctxt var_spec_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "strong_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "STRONG_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos
      val apply_ons = map (cert ctxt) (collect_apply_ons ctxt ind_infos)
      val search_vars = filter is_Free [rhs] @ arbitraries

      fun callback ((id, _), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "STRONG_INDUCT: cannot get var context."
            val var_infos = [(var, var_eq)]
            val ritems = apply_induction (the var_ctxt) var_infos ctxt ind_th []
            val (ind_prop, rest) =
                filter_split (fn ritem =>
                                 case ritem of Fact ("PROP", _, _) => true
                                             | _ => false) ritems
            val _ = assert (length ind_prop = 1)
                           "STRONG_INDUCT: should have one ind_prop."
            val all_th = ind_prop |> the_single |> get_thm_raw
                                  |> apply_to_thm (to_meta_all_conv ctxt)
            val ths = map (fn ct => Thm.forall_elim ct all_th) apply_ons
            val ritems' = if length apply_ons = 0 then ritems
                          else map Update.thm_to_ritem ths @ rest
          in
            [Update.AddItems {id = id, raw_items = ritems'}]
          end
    in
      [Script_Task {inits = [Update.InitAssum @{prop "~True"}], subs = [],
                    cb = callback, end_vars = get_new_vars var_eq}]
    end

fun UPPER_STRONG_INDUCT (var_spec_str, less_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val (var, rhs, var_eq) = process_var_spec_str ctxt var_spec_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "upper_strong_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "UPPER_STRONG_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos
      val apply_ons = map (cert ctxt) (collect_apply_ons ctxt ind_infos)
      val search_vars = filter is_Free [rhs] @ arbitraries

      (* The n < M requirement (first assumption of ind_th). *)
      val less_req = read_term ctxt less_str
      val init_assum = less_req |> get_neg |> HOLogic.mk_Trueprop

      (* If the right side is not a free variable, create a new
         variable equal to it. This will be considered an initial
         assumption in the var_ctxt.
       *)
      val rhs_req = dest_arg less_req
      val var_eq2 =
          if is_Free rhs_req then NONE
          else let
            val var = singleton (Variable.variant_frees ctxt []) ("M", ty)
          in
            SOME (HOLogic.mk_Trueprop (HOLogic.mk_eq (Free var, rhs_req)))
          end

      fun callback ((id, th), st as {ctxt, ...}) =
          let
            val handlers = map (pair false) (Status.get_handlers st id)
            fun rewr_th th =
                if is_none var_eq2 then th
                else th |> apply_to_thm (
                    rewr_obj_eq_top
                        ctxt (obj_sym (assume_thm ctxt (the var_eq2))))
            val th' = th |> Status.invoke_handlers handlers |> rewr_th
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "STRONG_INDUCT: cannot get var context."
            val var_ctxt' = var_ctxt |> the |> apsnd (append (the_list var_eq2))
            val var_infos = [(var, var_eq)]
            val ritems =
                apply_induction var_ctxt' var_infos ctxt ind_th [th'] @
                get_eq_handler ctxt var_eq2
            val (ind_prop, rest) =
                filter_split (fn ritem =>
                                 case ritem of Fact ("PROP", _, _) => true
                                             | _ => false) ritems
            val _ = assert (length ind_prop = 1)
                           "UPPER_STRONG_INDUCT: should have one ind_prop."
            val all_th = ind_prop |> the_single |> get_thm_raw
                                  |> apply_to_thm (to_meta_all_conv ctxt)
            val ths = map (fn ct => Thm.forall_elim ct all_th) apply_ons
            val ritems' = if length apply_ons = 0 then ritems
                          else map Update.thm_to_ritem ths @ rest
          in
            [Update.AddItems {id = id, raw_items = ritems'}]
          end
    in
      [Script_Task {
          inits = [Update.InitAssum init_assum], subs = [],
          cb = callback, end_vars = maps get_new_vars [var_eq, var_eq2]}]
    end

fun PROP_INDUCT (str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val t = read_term ctxt str
      val f = Term.head_of t
      val ind_th = the (get_term_ind_th thy "prop_induct" f)
                   handle Option.Option =>
                          raise AUTO2 "PROP_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos

      fun callback ((id, th), st) =
          let
            val ind_updt = apply_prop_induction (id, th) ind_th arbitraries st
          in
            if length ind_updt = 0 then
              raise AUTO2 "PROP_INDUCT: failed"
            else
              [Update.thm_update (id, th)] @ ind_updt
          end
    in
      [Script_Task {inits = [Update.InitAssum (
                                HOLogic.mk_Trueprop (get_neg t))], subs = [],
                    cb = callback, end_vars = []}]
    end

fun VAR_INDUCT (var_name, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = read_term ctxt var_name
      val ty = type_of var
      val ind_th = the (get_typed_ind_th thy "var_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "VAR_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos

      fun callback ((id, _), st) =
          let
            val ind_updt = apply_var_induction (id, var) ind_th arbitraries st
          in
            if length ind_updt = 0 then
              raise AUTO2 "VAR_INDUCT: failed"
            else ind_updt
          end
    in
      [Script_Task {inits = [Update.InitAssum @{prop "~True"}], subs = [],
                    cb = callback, end_vars = []}]
    end

end  (* structure Induct_ProofSteps. *)

open Induct_ProofSteps
