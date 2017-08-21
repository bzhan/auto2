(* Outer syntax for induction *)

signature INDUCT_PROOFSTEPS =
sig
  val add_induct_data: string -> term * thm -> theory -> theory
  val add_typed_induct_data: string -> typ * thm -> theory -> theory
  val get_typed_ind_th: theory -> string -> typ -> thm option
  val get_term_ind_th: theory -> string -> term -> thm option

  val check_strong_ind_prop: term -> term list * term
  val add_strong_induct_rule: thm -> theory -> theory
  val add_case_induct_rule: thm -> theory -> theory
  val add_prop_induct_rule: thm -> theory -> theory
  val add_var_induct_rule: thm -> theory -> theory

  val strong_induct_cmd: string * string list -> Proof.state -> Proof.state
  val apply_induct_hyp_cmd: string -> Proof.state -> Proof.state
  val case_induct_cmd: string -> Proof.state -> Proof.state
  val prop_induct_cmd: string * string -> Proof.state -> Proof.state
  val induct_cmd: string * string option * string list * string option -> Proof.state -> Proof.state
end;

structure Induct_ProofSteps : INDUCT_PROOFSTEPS =
struct

structure Data = Theory_Data (
  type T = ((term * thm) list) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list (eq_fst (op =))
)

fun add_induct_data str (t, ind_th) =
    Data.map (Symtab.map_default (str, []) (cons (t, ind_th)))

fun add_typed_induct_data str (ty, ind_th) =
    add_induct_data str (Term.dummy_pattern ty, ind_th)

fun get_typed_ind_th thy ind_type ty =
    let
      val tab = Data.get thy
      fun typ_can_match t' =
          let val _ = Sign.typ_match thy (type_of t', ty) Vartab.empty in true end
          handle Type.TYPE_MATCH => false
    in
      case Symtab.lookup tab ind_type of
          NONE => NONE
        | SOME lst =>
          case find_first (fn (t', _) => typ_can_match t') lst of
              NONE => NONE
            | SOME (_, ind_th) => SOME ind_th
    end

fun get_term_ind_th thy ind_type t =
    let
      val tab = Data.get thy
      fun term_can_match t' =
          let val _ = Pattern.first_order_match thy (t', t) fo_init in true end
          handle Pattern.MATCH => false
    in
      case Symtab.lookup tab ind_type of
          NONE => NONE
        | SOME lst =>
          case find_first (fn (t', _) => term_can_match t') lst of
              NONE => NONE
            | SOME (_, ind_th) => SOME ind_th
    end

(* Check a strong induction theorem ind_th is of the right form, and
   extract the induction variables and substitution.
 *)
fun check_strong_ind_prop ind_prop =
    let
      fun err str = "Strong induction: " ^ str
      val (cond_ind, concl) =
          ind_prop |> Logic.dest_implies |> apply2 dest_Trueprop

      (* concl must be of form ?P [?vars]. *)
      val err_concl = err "concl of ind_th must be ?P [?vars]."
      val (P, pat_vars) = Term.strip_comb concl
                          handle TERM _ => error err_concl
      val _ = assert (is_Var P andalso forall is_Var pat_vars andalso
                      (dest_Var P |> fst |> fst) = "P") err_concl

      (* cond_ind must be of form !n. P' n --> ?P n. Return the
         substitution pattern P'.
       *)
      val err_ind_hyp = err "cond_ind of ind_th must be !n. P' --> ?P vars."
      fun dest_one_all var body =
          case body of
              Const (c, _) $ Abs (_, _, t) =>
              if c = UtilBase.All_name then subst_bound (var, t)
              else error err_ind_hyp
            | _ => error err_ind_hyp
      val (pat_subst, P_vars) =
          cond_ind |> fold dest_one_all pat_vars |> dest_imp
      val _ = assert (P_vars aconv concl) err_ind_hyp
    in
      (pat_vars, pat_subst)
    end

fun add_strong_induct_rule ind_th thy =
    let
      val name = name_of_thm ind_th
      val ctxt = Proof_Context.init_global thy
      val ind_th' = apply_to_thm (to_obj_conv_on_horn ctxt) ind_th
      val (pat_var, pat_subst) =
          check_strong_ind_prop (Thm.prop_of ind_th') |> apfst the_single
          handle List.Empty => error "Strong induction: more than one var."
      val ty_var = type_of pat_var
      val _ = writeln (name ^ "\nSubstitution: " ^
                       (string_of_terms_global thy [pat_var, pat_subst]))
    in
      thy |> add_typed_induct_data "strong_induct" (ty_var, ind_th')
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

fun add_prop_induct_rule ind_th thy =
    let
      (* Initial assumption is of form f ?a_1 ... ?a_n. *)
      val (init_assum, _) = Logic.dest_implies (Thm.prop_of ind_th)
      val (f, pat_vars) = Term.strip_comb (dest_Trueprop init_assum)
      val _ = assert (forall Term.is_Var pat_vars) "add_prop_induct_rule"
    in
      thy |> add_induct_data "prop_induct" (f, ind_th)
    end

fun add_var_induct_rule ind_th thy =
    let
      val (P, n) = ind_th |> concl_of' |> Term.dest_comb
      val _ = assert (Term.is_Var P andalso Term.is_Var n)
                     "add_var_induct_rule: concl of ind_th must be ?P ?var"
    in
      thy |> add_typed_induct_data "var_induct" (type_of n, ind_th)
    end

fun strong_induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val var = s |> Syntax.read_term ctxt

      val arbitraries = map (Syntax.read_term ctxt) t

      val prop = Auto2_State.get_selected ctxt
      val (vars, (assums, concl)) = prop |> Auto2_State.subgoal_of |> Thm.term_of
                                         |> Util.strip_meta_horn

      val P = (list_obj_horn (arbitraries, (map dest_Trueprop assums, dest_Trueprop concl)))
                  |> lambda_abstract var

      val ty = type_of var
      val ind_th = the (get_typed_ind_th thy "strong_induct" ty)
                   handle Option.Option =>
                          raise Fail "strong_induct: ind_th not found."

      val (var_P, var_n) = ind_th |> Thm.concl_of |> dest_Trueprop
                                  |> Term.dest_comb
      val inst = fold (Pattern.match thy) [(var_P, P), (var_n, var)] fo_init
      val ind_th =
          ind_th |> subst_thm ctxt inst
                 |> apply_to_thm (Conv.binop_conv (to_meta_conv ctxt))

      val assum = hd (Drule.cprems_of ind_th)
      val ind_th =
          ind_th |> send_first_to_hyps
                 |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) arbitraries)
                 |> fold Thm.forall_intr (map (Thm.cterm_of ctxt) vars)
                 |> Thm.implies_intr assum

      val t' = case Thm.prop_of ind_th of
                   imp $ A $ B => imp $ rename_abs_term [var] A $ B
                 | _ => raise Fail "strong_induct_cmd"

      val ind_th = ind_th |> Thm.renamed_prop t'

      val prop = prop |> Auto2_Outer.refine_subgoal_th ind_th

      val stmt = prop |> Auto2_State.subgoal_of |> Thm.term_of |> Util.strip_meta_horn |> snd
                      |> fst |> hd |> dest_Trueprop
    in
      state |> Proof.map_contexts (Auto2_State.set_head_th prop)
            |> Proof.map_contexts (Auto2_State.set_induct_stmt stmt)
    end

val arbitrary =
    Scan.option (@{keyword "arbitrary"} |-- Scan.repeat Parse.term)

val _ =
  Outer_Syntax.command @{command_keyword "@strong_induct"}
    "apply strong induction"
    ((Parse.term -- arbitrary) >> (fn (s, t) =>
         Toplevel.proof (fn state => strong_induct_cmd (s, these t) state)))

fun apply_induct_hyp_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state

      val tm = Syntax.read_term ctxt s

      val prop = Auto2_State.get_selected ctxt
      val {induct_stmt, ...} = Auto2_State.get_head ctxt
      val induct_stmt =
          case induct_stmt of
              SOME (_ $ Abs (_, _, body)) => Term.subst_bound (tm, body)
            | _ => raise Fail "apply_induct_hyp_cmd"

      val (_, (As, _)) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> Util.strip_meta_horn
      val goal = Logic.list_implies (As, mk_Trueprop induct_stmt)
      val th = Auto2_Outer.auto2_solve ctxt (Thm.cterm_of ctxt goal)
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th (Auto2_Outer.have_after_qed ctxt th))
    end

val _ =
  Outer_Syntax.command @{command_keyword "@apply_induct_hyp"}
    "apply induction hypothesis"
    (Parse.term >> (fn s =>
         Toplevel.proof (fn state => apply_induct_hyp_cmd s state)))

fun case_induct_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val start = Syntax.read_term ctxt s
      val (f, args) = Term.strip_comb start
      val ind_th = the (get_term_ind_th thy "case_induct" f)
                   handle Option.Option =>
                          raise Fail "case_induct: cannot find theorem."

      (* Obtain list of assumptions *)
      val (_, (As, C)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As

      (* Instantiate the induction theorem *)
      val (_, vars) = ind_th |> Thm.prems_of |> hd |> dest_Trueprop
                             |> Term.strip_comb
      val var_P = ind_th |> concl_of'
      val inst = fold (Pattern.match thy)
                      ((var_P, dest_Trueprop C) :: (vars ~~ args)) fo_init
      val ind_th = subst_thm_thy thy inst ind_th

      val ind_goals =
          ind_th |> Thm.prems_of
                 |> map (fn t => Logic.list_implies (As, t))
                 |> map (Thm.cterm_of ctxt)

      val ths = (map (Auto2_Outer.auto2_solve ctxt) ind_goals)
                    |> map send_all_to_hyps

      val ind_concl = ind_th |> fold Thm.elim_implies ths
                             |> fold Thm.implies_intr (rev cAs)

      val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@case_induct"} "apply induction"
    (Parse.term >>
        (fn s =>
            Toplevel.proof (fn state => case_induct_cmd s state)))

fun prop_induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val (start, stmt) = the_pair (Syntax.read_terms ctxt [s, t])
      val (f, args) = Term.strip_comb start
      val ind_th = the (get_term_ind_th thy "prop_induct" f)
                   handle Option.Option =>
                          raise Fail "prop_induct: cannot find theorem."

      (* Instantiate the induction theorem *)
      val P = fold lambda_abstract (rev args) stmt
      val (var_P, vars) = ind_th |> concl_of' |> Term.strip_comb
      val inst = fold (Pattern.match thy) ((var_P, P) :: (vars ~~ args)) fo_init
      val ind_th = subst_thm_thy thy inst ind_th

      (* Obtain list of assumptions *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As

      val ind_goals =
          ind_th |> Thm.prems_of
                 |> map (fn t => Logic.list_implies (As, t))
                 |> map (Thm.cterm_of ctxt)

      val ths = (map (Auto2_Outer.auto2_solve ctxt) ind_goals)
                    |> map send_all_to_hyps

      val ind_concl = ind_th |> fold Thm.elim_implies ths
                             |> fold Thm.implies_intr (rev cAs)

      val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@prop_induct"} "apply induction"
    ((Parse.term -- Parse.term) >>
        (fn (s, t) =>
            Toplevel.proof (fn state => prop_induct_cmd (s, t) state)))

(* Obtain the induction statement. *)
fun get_induct_stmt ctxt (var, stmt, arbitrary) =
    if is_some stmt then
      UtilLogic.list_obj_horn (arbitrary, ([], Syntax.read_term ctxt (the stmt)))
    else
      let
        val (_, (As, C)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                                |> Thm.term_of |> Util.strip_meta_horn
        val all_vars = var :: arbitrary
        val obj_As = map dest_Trueprop (filter (occurs_frees all_vars) As)
        val obj_C = dest_Trueprop C
      in
        UtilLogic.list_obj_horn (arbitrary, (obj_As, obj_C))
      end

fun induct_cmd (s, t, u, v) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val var = Syntax.read_term ctxt s
      val arbitraries = map (Syntax.read_term ctxt) u
      val stmt = get_induct_stmt ctxt (var, t, arbitraries)
      val ty = type_of var
      val (arbitraries, _) = UtilLogic.strip_obj_horn stmt

      val ind_th = the (get_typed_ind_th thy "var_induct" ty)
                   handle Option.Option =>
                          raise Fail "var_induct: cannot find theorem."

      (* Instantiate the induction theorem *)
      val concl = concl_of' ind_th
      val (var_P, var_n) = Term.dest_comb concl

      val P_inst = Term.lambda var stmt
      val inst = fold (Pattern.match thy) [(var_P, P_inst), (var_n, var)] fo_init
      val ind_th' = subst_thm_thy thy inst ind_th

      (* Obtain list of assumptions *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As
      val use_As = As |> filter_out (occurs_frees (var :: arbitraries))

      fun retrieve_pat t =
          let
            val (vars, (_, C)) = Util.strip_meta_horn t
            val pat_vars = map (fn t => let val (x, T) = Term.dest_Free t in Var ((x,0), T) end) vars
            val arg = C |> dest_Trueprop |> dest_arg |> Term.subst_atomic (vars ~~ pat_vars)
          in
            mk_eq (var, arg)
          end
      val pats = ind_th |> Thm.prems_of |> map retrieve_pat

      val ind_goals =
          ind_th' |> Thm.prems_of
                  |> map (fn t => Logic.list_implies (use_As, t))
                  |> map (Thm.cterm_of ctxt)
                  |> map (UtilLogic.to_meta_conv ctxt)

      fun solve_eq eq =
          let
            val th = Auto2_Outer.auto2_solve ctxt (Thm.rhs_of eq)
          in
            Thm.equal_elim (meta_sym eq) th
          end

      val _ = assert (length pats = length ind_goals)
                     "var_induct: unexpected number of patterns"
  in
    if is_none v then
      let
        val ths = (map solve_eq ind_goals) |> map send_all_to_hyps
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
              val ths' = (ind_goals ~~ ths)
                            |> map (fn (eq, th) => Thm.equal_elim (meta_sym eq) th)
                            |> map send_all_to_hyps
              val ind_concl = ind_th' |> fold Thm.elim_implies ths'
                                      |> fold Thm.implies_intr (rev cAs)
            in
              Auto2_Outer.have_after_qed ctxt ind_concl prop
            end

          val new_frame =
              Auto2_State.multiple_frame (pats ~~ map Thm.rhs_of ind_goals, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val for_stmt =
    Scan.option (@{keyword "for"} |-- Parse.term)

val _ =
  Outer_Syntax.command @{command_keyword "@induct"} "apply induction"
    (Parse.term -- for_stmt -- arbitrary -- Scan.option @{keyword "@with"} >>
        (fn (((s, t), u), v) =>
            Toplevel.proof (fn state => induct_cmd (s, t, these u, v) state)))

end  (* structure Induct_ProofSteps. *)

val add_strong_induct_rule = Induct_ProofSteps.add_strong_induct_rule
val add_case_induct_rule = Induct_ProofSteps.add_case_induct_rule
val add_prop_induct_rule = Induct_ProofSteps.add_prop_induct_rule
val add_var_induct_rule = Induct_ProofSteps.add_var_induct_rule
