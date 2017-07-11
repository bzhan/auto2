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
  val process_neq0_th: box_id -> term list * term list -> status -> thm -> thm
  val remove_pred_assum: thm -> term list -> term list * term list ->
                         Proof.context -> term * thm -> thm
  val get_induct_handler: term list * term list * term list -> Proof.context ->
                          thm -> term -> raw_item list
  val check_strong_ind_prop: term -> term list * term
  val apply_induction: term list * term list -> term list ->
                       Proof.context -> thm -> thm list -> raw_item list
  val add_prfstep_strong_induction: thm -> theory -> theory
  val add_prfstep_upper_strong_induction: thm -> theory -> theory
  val check_ind_th: thm -> term * (term * term)
  val prfstep_induction: string -> prfstep_descriptor list -> thm -> proofstep
  val add_prfstep_induction: thm -> theory -> theory

  datatype induct_info = Arbitrary of string | ApplyOn of string
  val Arbitraries: string list -> induct_info list
  val collect_arbitraries: Proof.context -> induct_info list -> term list
  val ApplyOns: string list -> induct_info list
  val collect_apply_ons: Proof.context -> induct_info list -> term list
  val get_neq0_th: term * term -> term
  val INDUCT: string * induct_info list -> pre_scripts
  val STRONG_INDUCT: string * induct_info list -> pre_scripts
  val UPPER_STRONG_INDUCT: string * string * induct_info list -> pre_scripts
  val add_case_induct_rule: thm -> theory -> theory
  val CASE_INDUCT: string -> pre_scripts
  val add_prop_induct_rule: thm -> theory -> theory
  val PROP_INDUCT: string * string -> pre_scripts
  val add_var_induct_rule: thm -> theory -> theory
  val VAR_INDUCT: string * string -> pre_scripts
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
      val use_vardef_cv = Conv.arg_conv (rewr_obj_eq use_vardef_th)
    in
      neq0_th |> Status.invoke_handlers handlers
              |> rewrite_thm_to_contra_form  (* n = 0 ==> False *)
              |> send_first_to_hyps  (* [n = 0] ==> False *)
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
          ind_prop |> Logic.dest_implies |> apply2 dest_Trueprop

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
              Const (c, _) $ Abs (_, _, t) =>
              if c = All_name then subst_bound (var, t)
              else raise AUTO2 err_ind_hyp
            | _ => raise AUTO2 err_ind_hyp
      val (pat_subst, P_vars) =
          cond_ind |> fold dest_one_all pat_vars |> dest_imp
      val _ = assert (P_vars aconv concl) err_ind_hyp
    in
      (pat_vars, pat_subst)
    end

(* Here ind_th is the induction theorem A_1 ==> ... ==> A_n ==> C. The
   given prev_ths are matched against A_1, ... A_{n-1}. The conclusion
   C is of the form ?P ?n_1 ... ?n_k. The matching process can be
   subtle, as the instantiation of ?P has to be constructed manually.
 *)
fun apply_induction var_ctxt ind_vars ctxt ind_th prev_ths =
    let
      val thy = Proof_Context.theory_of ctxt

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
      val stmt = Update.get_neg_form_obj
                     ctxt (Update.build_init_infos (vars', assums))
      val p = stmt |> dest_Trueprop
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
      val stmt' = mk_Trueprop (subst_term_norm inst' pat_subst)
      val ind_th' = ind_th |> subst_thm ctxt inst'
                           |> fold Thm.elim_implies prev_ths
    in
      get_induct_handler (ind_vars, vars', assums) ctxt ind_th' stmt'
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
      fun err str = "check_ind_th: " ^ str
      val (cond_base, ind_th') =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst dest_Trueprop

      (* cond_base must be of form ?P b, where b is base case for ?n. *)
      val err_base_hyp = err "Base assumption of ind_th must be ?P base."
      val base =
          case cond_base of
              P $ b =>
              if Term.is_Var P then b else raise AUTO2 err_base_hyp
            | _ => raise AUTO2 err_base_hyp
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
                val ritems =
                    apply_induction (the var_ctxt) [trm_n] ctxt ind_th [p0_th]
              in
                [AddItems {id = id, sc = NONE, raw_items = ritems}]
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
      val descs = [WithFact (Not $ (mk_eq (var, base))),
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

datatype induct_info = Arbitrary of string | ApplyOn of string

val Arbitraries = map Arbitrary
fun collect_arbitraries ctxt infos =
    infos |> maps (fn info => case info of Arbitrary str => [str] | _ => [])
          |> map (read_term ctxt)
val ApplyOns = map ApplyOn
fun collect_apply_ons ctxt infos =
    infos |> maps (fn info => case info of ApplyOn str => [str] | _ => [])
          |> map (read_term ctxt)

fun get_neq0_th (t, base) =
    let
      val base' = case base of
                      Const (nm, _) => Const (nm, type_of t)
                    | _ => raise AUTO2 "INDUCT: base is not a constant."
    in
      mk_eq (t, base')
    end

fun INDUCT (var_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = read_term ctxt var_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "INDUCT: ind_th not found."
      val (base, _) = check_ind_th ind_th
      val neq0 = mk_Trueprop (get_neq0_th (var, base))
      val arbitraries = collect_arbitraries ctxt ind_infos
      val search_vars = var :: arbitraries

      fun callback ((id, neq0_th), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "INDUCT: cannot get var context."
            val (_, assums) = the var_ctxt

            val p0_th = neq0_th |> process_neq0_th id (arbitraries, assums) st
            val ritems =
                apply_induction (the var_ctxt) [var] ctxt ind_th [p0_th]
          in
            [Update.thm_update (id, neq0_th),
             AddItems {id = id, sc = NONE, raw_items = ritems}]
          end
    in
      [Script_Task {inits = [InitAssum neq0], subs = [], cb = callback,
                    end_vars = []}]
    end

fun STRONG_INDUCT (var_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = read_term ctxt var_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "strong_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "STRONG_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos
      val apply_ons = map (cert ctxt) (collect_apply_ons ctxt ind_infos)
      val search_vars = var :: arbitraries

      fun callback ((id, _), st as {ctxt, ...}) =
          let
            val var_ctxt = get_var_context id search_vars st
            val _ = assert (is_some var_ctxt)
                           "STRONG_INDUCT: cannot get var context."
            val ritems = apply_induction (the var_ctxt) [var] ctxt ind_th []
            val (ind_prop, rest) =
                filter_split (BoxItem.match_ty_str_raw TY_PROP) ritems
            val _ = assert (length ind_prop = 1)
                           "STRONG_INDUCT: should have one ind_prop."
            val all_th = ind_prop |> the_single |> BoxItem.get_thm_raw
                                  |> apply_to_thm (to_meta_all_conv ctxt)
            val ths = map (fn ct => Thm.forall_elim ct all_th) apply_ons
            val ritems' = if length apply_ons = 0 then ritems
                          else map Update.thm_to_ritem ths @ rest
          in
            [AddItems {id = id, sc = NONE, raw_items = ritems'}]
          end

      val not_True = bTrue |> get_neg |> mk_Trueprop
    in
      [Script_Task {inits = [InitAssum not_True], subs = [],
                    cb = callback, end_vars = []}]
    end

fun UPPER_STRONG_INDUCT (var_str, less_str, ind_infos) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val var = read_term ctxt var_str
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "upper_strong_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "UPPER_STRONG_INDUCT: ind_th not found."
      val arbitraries = collect_arbitraries ctxt ind_infos
      val apply_ons = map (cert ctxt) (collect_apply_ons ctxt ind_infos)
      val search_vars = var :: arbitraries

      (* The n < M requirement (first assumption of ind_th). *)
      val less_req = read_term ctxt less_str
      val init_assum = less_req |> get_neg |> mk_Trueprop

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
            SOME (mk_Trueprop (mk_eq (Free var, rhs_req)))
          end

      (* Given var_eq as either NONE or SOME (ind_var = trm_n), return
         the raw items specifying the new variable, equation, and
         handler.
       *)
      fun get_eq_handler ctxt var_eq =
          case var_eq of
              NONE => []
            | SOME eq =>
              let
                val (ind_var, _) = eq |> dest_Trueprop |> dest_eq
                fun eq_ready (t, ts) =
                    forall (fn t' => t' aconv t orelse
                                     not (occurs_free ind_var t')) ts
                fun eq_handler (t, th) =
                    th |> Thm.implies_intr (cert ctxt t)
                       |> Thm.forall_intr (cert ctxt ind_var)
                       |> apply_to_thm (to_obj_conv ctxt)
                       |> apply_to_thm' (rewr_obj_eq use_vardef_th)
              in
                [BoxItem.var_to_fact ind_var] @
                Update.handler_ritems ctxt eq (eq_ready, eq_handler)
              end


      (* Obtain new variables (if any) indicated by var_eq. *)
      fun get_new_vars var_eq =
          case var_eq of
              NONE => []
            | SOME eq => [eq |> dest_Trueprop |> dest_eq |> fst]

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
            val ritems = apply_induction var_ctxt' [var] ctxt ind_th [th'] @
                         get_eq_handler ctxt var_eq2
            val (ind_prop, rest) =
                filter_split (
                  fn ritem =>
                     case ritem of Fact ("PROP", [t], _) => not (is_eq_term t)
                                 | _ => false) ritems
            val _ = assert (length ind_prop = 1)
                           "UPPER_STRONG_INDUCT: should have one ind_prop."
            val all_th = ind_prop |> the_single |> BoxItem.get_thm_raw
                                  |> apply_to_thm (to_meta_all_conv ctxt)
            val ths = map (fn ct => Thm.forall_elim ct all_th) apply_ons
            val ritems' = if length apply_ons = 0 then ritems
                          else map Update.thm_to_ritem ths @ rest
          in
            [AddItems {id = id, sc = NONE, raw_items = ritems'}]
          end
    in
      [Script_Task {inits = [InitAssum init_assum], subs = [], cb = callback,
                    end_vars = get_new_vars var_eq2}]
    end

fun add_case_induct_rule ind_th thy =
    let
      (* Initial assumption is of form f ?a_1 ... ?a_n. *)
      val init_assum = hd (Thm.prems_of ind_th)
      val (f, pat_vars) = Term.strip_comb (dest_Trueprop init_assum)
      val _ = assert (forall Term.is_Var pat_vars) "add_case_induct_rule"
    in
      thy |> add_induct_data "case_induct" (f, ind_th)
    end

fun CASE_INDUCT t_str ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      val t = read_term ctxt t_str
      val (f, _) = Term.strip_comb t
      val ind_th = the (get_term_ind_th thy "case_induct" f)
                   handle Option.Option =>
                          raise AUTO2 "CASE_INDUCT: unknown function head."
      val var_P = ind_th |> concl_of' |> Term.dest_Var |> fst
      val inst = update_env (var_P, bFalse) fo_init
      val ind_th' = (subst_thm ctxt inst ind_th)
                        |> apply_to_thm (to_obj_conv_on_horn ctxt)
      fun callback ((id, th), {ctxt, ...}) =
          Logic_ProofSteps.apply_horn_clause ctxt (id, th RS ind_th')
    in
      [Script_Task {inits = [InitAssum (mk_Trueprop (get_neg t))],
                    subs = [], cb = callback, end_vars = []}]
    end

fun add_prop_induct_rule ind_th thy =
    let
      (* Initial assumption is of form f ?a_1 ... ?a_n. *)
      val (init_assum, _) = Logic.dest_implies (Thm.prop_of ind_th)
      val (f, pat_vars) = Term.strip_comb (dest_Trueprop init_assum)
      val _ = assert (forall Term.is_Var pat_vars) "add_prop_induct_rule"
    in
      thy |> add_induct_data "prop_induct" (f, ind_th)
    end

fun PROP_INDUCT (t_str, stmt_str) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      val (t, stmt) = (read_term ctxt t_str, read_term ctxt stmt_str)
      val (f, args) = Term.strip_comb t
      val ind_th = the (get_term_ind_th thy "prop_induct" f)
                   handle Option.Option =>
                          raise AUTO2 "PROP_INDUCT: unknown function head."
      val P = fold lambda_abstract (rev args) stmt
      val var_P = ind_th |> concl_of' |> Term.head_of |> Term.dest_Var |> fst
      val inst = update_env (var_P, P) fo_init

      fun callback ((id, th), {ctxt, ...}) =
          let
            val ind_th' = (th RS ind_th)
                              |> subst_thm ctxt inst
                              |> apply_to_thm (to_obj_conv_on_horn ctxt)
          in
            Logic_ProofSteps.apply_horn_clause ctxt (id, ind_th')
          end
    in
      [Script_Task {inits = [InitAssum (mk_Trueprop (get_neg t))],
                    subs = [], cb = callback, end_vars = []}]
    end

fun add_var_induct_rule ind_th thy =
    let
      val (P, n) = ind_th |> concl_of' |> Term.dest_comb
      val _ = assert (Term.is_Var P andalso Term.is_Var n)
                     "add_var_induct_rule: concl of ind_th must be ?P ?var"
    in
      thy |> add_typed_induct_data "var_induct" (type_of n, ind_th)
    end

fun VAR_INDUCT (n_str, stmt_str) ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      val (n, stmt) = (read_term ctxt n_str, read_term ctxt stmt_str)
      val ty = type_of n
      val ind_th = the (get_typed_ind_th thy "var_induct" ty)
                   handle Option.Option =>
                          raise AUTO2 "VAR_INDUCT: unknown variable type."
      val P = Abs ("x", ty, Term.abstract_over (n, stmt))
      val (var_P, var_n) = ind_th |> concl_of' |> Term.dest_comb
                                  |> apply2 (fst o Term.dest_Var)
      val inst = pattern_fo_match ctxt (ind_th |> concl_of' |> dest_arg, n)
      val inst' = update_env (var_P, P) inst
      val ind_th' = (subst_thm ctxt inst' ind_th)
                        |> apply_to_thm (to_obj_conv_on_horn ctxt)
      fun callback ((id, _), {ctxt, ...}) =
          Logic_ProofSteps.apply_horn_clause ctxt (id, ind_th')

      val not_True = bTrue |> get_neg |> mk_Trueprop
    in
      [Script_Task {inits = [InitAssum not_True], subs = [],
                    cb = callback, end_vars = []}]
    end

end  (* structure Induct_ProofSteps. *)

open Induct_ProofSteps
