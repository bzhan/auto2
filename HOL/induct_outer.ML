(* Outer syntax for induction *)

signature INDUCT_PROOFSTEPS =
sig
  val add_induct_data: string -> term * thm -> theory -> theory
  val add_typed_induct_data: string -> typ * thm -> theory -> theory
  val get_typed_ind_th: theory -> string -> typ -> thm option
  val get_term_ind_th: theory -> string -> term -> thm option

  val check_strong_ind_prop: term -> term list * term
  val check_ind_th: thm -> term * (term * term)

  val add_prfstep_induction: thm -> theory -> theory
  val add_prfstep_strong_induction: thm -> theory -> theory
  val add_case_induct_rule: thm -> theory -> theory
  val add_prop_induct_rule: thm -> theory -> theory
  val add_var_induct_rule: thm -> theory -> theory

  val check_double_ind_th: thm -> (term * term) * (term list * term)
  val add_prfstep_double_induction: thm -> theory -> theory

  val strong_induct_cmd: string * string list -> Proof.state -> Proof.state
  val apply_induct_cmd: string -> Proof.state -> Proof.state
  val induct_cmd:
      string * string list * string option -> Proof.state -> Proof.state
  val double_induct_cmd:
      string * string * string list -> Proof.state -> Proof.state
  val case_induct_cmd: string -> Proof.state -> Proof.state
  val prop_induct_cmd: string * string -> Proof.state -> Proof.state
  val var_induct_cmd: string * string * string option -> Proof.state -> Proof.state
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
              if c = All_name then subst_bound (var, t)
              else error err_ind_hyp
            | _ => error err_ind_hyp
      val (pat_subst, P_vars) =
          cond_ind |> fold dest_one_all pat_vars |> dest_imp
      val _ = assert (P_vars aconv concl) err_ind_hyp
    in
      (pat_vars, pat_subst)
    end

(* Check ind_th for simple induction is in the right form, and extract
   induction variable and hypothesis from ind_th.

   Returns (base, (pat_var, pat_subst)), where base is the base case
   of induction, pat_var is the induction variable ?n, and pat_subst
   is the inductive hypothesis P' ?n.
 *)
fun check_ind_th ind_th =
    let
      fun err str = "Induction: " ^ str
      val (cond_base, ind_th') =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst dest_Trueprop

      (* cond_base must be of form ?P b, where b is base case for ?n. *)
      val err_base_hyp = err "Base assumption of ind_th must be ?P base."
      val base =
          case cond_base of
              P $ b =>
              if Term.is_Var P then b else error err_base_hyp
            | _ => error err_base_hyp
    in
      (base, check_strong_ind_prop ind_th' |> apfst the_single)
    end

fun add_prfstep_induction ind_th thy =
    let
      val (base, (pat_var, pat_subst)) = check_ind_th ind_th
      val name = name_of_thm ind_th

      (* Automatic induction on unique free variables, generalizing no
         other variables.
       *)
      val var = Var (("FREE", 0), type_of pat_var)
      val descs = [WithFact (Not $ (mk_eq (var, base))),
                   Filter (unique_free_filter "FREE")]

      val _ = writeln (
            name ^ "\n" ^ (ProofStep.string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^
            (string_of_terms_global thy [pat_var, pat_subst]))

      val ty_var = type_of pat_var
    in
      thy |> add_typed_induct_data "induct" (ty_var, ind_th)
    end

fun add_prfstep_strong_induction ind_th thy =
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

(* Check ind_th for a double induction is in the right form. *)
fun check_double_ind_th ind_th =
    let
      val thy = Thm.theory_of_thm ind_th
      fun err str = "check_double_ind_th: " ^ str
      val (cond_base1, (cond_base2, ind_th')) =
          ind_th |> Thm.prop_of |> Logic.dest_implies
                 |> apfst dest_Trueprop
                 |> apsnd (Logic.dest_implies #> apfst dest_Trueprop)

      (* cond_base1 must be of form !n. ?P mb n, where mb is the base
         case for ?m.
       *)
      val err_base_hyp1 =
          err "First base assumption of ind_th must be !n. ?P mb n."
      val inst1 = Pattern.first_order_match
                      thy (@{term_pat "!n. ?P ?mb n"}, cond_base1) fo_init
                  handle Pattern.MATCH => error err_base_hyp1
      val mb = lookup_inst inst1 "mb"

      (* cond_base2 must be of form !m. ?P m nb, where nb is the base
         case for ?n.
       *)
      val err_base_hyp2 =
          err "Second base assumption of ind_th must be !m. ?P m nb."
      val inst2 = Pattern.first_order_match
                      thy (@{term_pat "!m. ?P m ?nb"}, cond_base2) fo_init
                  handle Pattern.MATCH => error err_base_hyp2
      val nb = lookup_inst inst2 "nb"
    in
      ((mb, nb), check_strong_ind_prop ind_th')
    end

fun add_prfstep_double_induction ind_th thy =
    let
      val ((mb, nb), (pat_vars, pat_subst)) = check_double_ind_th ind_th
      val name = name_of_thm ind_th
      val err = "Double induction: should have two vars."
      val (pat_var1, pat_var2) =
          the_pair pat_vars handle Fail "the_pair" => error err

      (* Add user invoked proofstep. *)
      val (ty_var1, ty_var2) = apply2 type_of (pat_var1, pat_var2)
      val var1 = Var (("m", 0), ty_var1)
      val var2 = Var (("n", 0), ty_var2)
      val descs = [WithFact (Not $ (mk_eq (var1, mb))),
                   WithFact (Not $ (mk_eq (var2, nb)))]
      val _ = writeln (
            name ^ "\n" ^ (ProofStep.string_of_descs thy descs) ^ "\n" ^
            "Substitution: " ^
            (string_of_terms_global thy [pat_var1, pat_var2, pat_subst]))
      val ty = HOLogic.mk_prodT (ty_var1, ty_var2)
    in
      thy |> add_typed_induct_data "double_induct" (ty, ind_th)
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

fun apply_induct_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state

      val tm = Syntax.read_term ctxt s

      val prop = Auto2_State.get_selected ctxt
      val {induct_stmt, ...} = Auto2_State.get_head ctxt
      val induct_stmt =
          case induct_stmt of
              SOME (_ $ Abs (_, _, body)) => Term.subst_bound (tm, body)
            | _ => raise Fail "apply_induct_cmd"

      val (_, (As, _)) = prop |> Auto2_State.subgoal_of |> Thm.term_of |> Util.strip_meta_horn
      val goal = Logic.list_implies (As, mk_Trueprop induct_stmt)
      val th = Auto2_Outer.auto2_solve ctxt (Thm.cterm_of ctxt goal)
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th (Auto2_Outer.have_after_qed ctxt th))
    end

val _ =
  Outer_Syntax.command @{command_keyword "@apply_induct"}
    "apply induction hypothesis"
    (Parse.term >> (fn s =>
         Toplevel.proof (fn state => apply_induct_cmd s state)))

fun induct_cmd (s, t, u) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val var = s |> Syntax.read_term ctxt

      val arbitraries = map (Syntax.read_term ctxt) t

      val goal = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of |> Thm.term_of
      val (assums, concl) = goal |> Logic.strip_horn
                                 |> apfst (map dest_Trueprop)
                                 |> apsnd dest_Trueprop

      val P = (list_obj_horn (arbitraries, (assums, concl)))
                  |> lambda_abstract var

      val ty = type_of var
      val ind_th = the (get_typed_ind_th thy "induct" ty)
                   handle Option.Option =>
                          raise Fail "induct: ind_th not found."

      val (var_P, var_n) = ind_th |> Thm.concl_of |> dest_Trueprop
                                  |> Term.dest_comb
      val inst = fold (Pattern.match thy) [(var_P, P), (var_n, var)] fo_init
      val ind_th = ind_th |> subst_thm ctxt inst

      fun induct_after_qed ctxt neq0_th _ =
          let
            val ind_th =
                ind_th |> Thm.elim_implies neq0_th
                       |> apply_to_thm (Conv.binop_conv (to_meta_conv ctxt))

            val assum = hd (Drule.cprems_of ind_th)
            val ind_th =
                ind_th |> send_first_to_hyps
                       |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) arbitraries)
                       |> Thm.implies_intr assum

            val t' = case Thm.prop_of ind_th of
                         imp $ A $ B => imp $ rename_abs_term [var] A $ B
                       | _ => raise Fail "strong_induct_cmd"
          in
            ind_th |> Thm.renamed_prop t'
                   |> Goal.protect 1
          end
    in
      if is_none u orelse the u = "@then" then
        let
          val neq0_goal = Thm.cprem_of ind_th 1
          val neq0_th = Auto2_Outer.auto2_solve ctxt neq0_goal
        in
          state |> Proof.map_contexts (
            Auto2_State.map_head_th (induct_after_qed ctxt neq0_th))
        end
      else
        let
          (* Create new block with stmt *)
          val neq0_goal = Thm.prems_of ind_th |> hd |> dest_Trueprop
          val (vars, (assums, concl)) = strip_obj_horn neq0_goal
          val _ = assert (null vars)
                         "induct: subgoal should declare no new variables"
          val stmt = Logic.list_implies (map mk_Trueprop assums,
                                         mk_Trueprop concl)

          val goal = Thm.trivial (Thm.cterm_of ctxt stmt) |> Goal.protect 1
          fun after_qed ths prop =
              let
                val th = the_single ths
                val th' = apply_to_thm (to_obj_conv ctxt) th
              in
                induct_after_qed ctxt th' prop
              end
          val new_frame = Auto2_State.simple_frame (goal, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val _ =
  Outer_Syntax.command @{command_keyword "@induct"}
    "apply induction"
    ((Parse.term -- arbitrary) --
      Scan.option (@{keyword "@with"} || @{keyword "@then"}) >>
      (fn ((s, t), u) =>
         Toplevel.proof (fn state => induct_cmd (s, these t, u) state)))

fun double_induct_cmd (s1, s2, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val (var1, var2) = apply2 (Syntax.read_term ctxt) (s1, s2)

      val arbitraries = map (Syntax.read_term ctxt) t

      val goal = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of |> Thm.term_of
      val (assums, concl) = goal |> Logic.strip_horn
                                 |> apfst (map dest_Trueprop)
                                 |> apsnd dest_Trueprop

      val P = (list_obj_horn (arbitraries, (assums, concl)))
                  |> fold lambda_abstract [var2, var1]  (* Note reversed *)

      val ty = HOLogic.mk_prodT (type_of var1, type_of var2)
      val ind_th = the (get_typed_ind_th thy "double_induct" ty)
                   handle Option.Option =>
                          raise Fail "double_induct: ind_th not found."

      val (var_P, (var_n1, var_n2)) =
          ind_th |> Thm.concl_of |> dest_Trueprop
                 |> Term.strip_comb |> apsnd (the_pair)
      val inst = fold (Pattern.match thy)
                      [(var_P, P), (var_n1, var1), (var_n2, var2)] fo_init
      val ind_th = ind_th |> subst_thm ctxt inst

      val neq0_goals = Drule.cprems_of ind_th |> take 2
      val neq0_ths = map (Auto2_Outer.auto2_solve ctxt) neq0_goals

      val ind_th = ind_th |> fold Thm.elim_implies neq0_ths
                          |> apply_to_thm (Conv.binop_conv (to_meta_conv ctxt))

      val assum = hd (Drule.cprems_of ind_th)
      val ind_th =
          ind_th |> send_first_to_hyps
                 |> fold Thm.forall_elim (map (Thm.cterm_of ctxt) arbitraries)
                 |> Thm.implies_intr assum

      val t' = case Thm.prop_of ind_th of
                   imp $ A $ B => imp $ rename_abs_term [var1, var2] A $ B
                 | _ => raise Fail "double_induct_cmd"

      val ind_th = ind_th |> Thm.renamed_prop t'
                          |> Goal.protect 1
    in
      state |> Proof.map_contexts (Auto2_State.set_head_th ind_th)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@double_induct"}
    "apply double induction"
    (((Parse.term -- Parse.term) -- arbitrary) >>
       (fn ((s1, s2), t) =>
           Toplevel.proof (
             fn state => double_induct_cmd (s1, s2, these t) state)))

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

fun var_induct_cmd (s, t, u) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val (var, stmt) = the_pair (Syntax.read_terms ctxt [s, t])
      val ty = type_of var

      val ind_th = the (get_typed_ind_th thy "var_induct" ty)
                   handle Option.Option =>
                          raise Fail "var_induct: cannot find theorem."

      (* Instantiate the induction theorem *)
      val concl = concl_of' ind_th
      val (var_P, var_n) = Term.dest_comb concl

      val P_inst = Term.lambda var stmt
      val inst =
          fold (Pattern.match thy) [(var_P, P_inst), (var_n, var)] fo_init
      val ind_th = subst_thm_thy thy inst ind_th

      (* Obtain list of assumptions *)
      val (_, (As, _)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As

      val ind_goals =
          ind_th |> Thm.prems_of
                 |> map (fn t => Logic.list_implies (As, t))
                 |> map (Thm.cterm_of ctxt)
    in
      if is_none u then
        let
          val ths = (map (Auto2_Outer.auto2_solve ctxt) ind_goals)
                        |> map send_all_to_hyps
          val ind_concl = ind_th |> fold Thm.elim_implies ths
                                 |> fold Thm.implies_intr (rev cAs)
          val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
        in
          state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
        end
      else
        let
          val ind_goals_th = ind_goals |> map (Goal.protect 1 o Thm.trivial)
          (* Create new block with the subgoals *)
          fun after_qed ths prop =
              let
                val ths' = ths |> map send_all_to_hyps
                val ind_concl = ind_th |> fold Thm.elim_implies ths'
                                       |> fold Thm.implies_intr (rev cAs)
              in
                Auto2_Outer.have_after_qed ctxt ind_concl prop
              end

          val new_frame = Auto2_State.multiple_frame (ind_goals_th, SOME ([], after_qed))
        in
          state |> Proof.map_contexts (Auto2_State.push_head new_frame)
        end
    end

val _ =
  Outer_Syntax.command @{command_keyword "@var_induct"} "apply induction"
    ((Parse.term -- Parse.term) -- Scan.option @{keyword "@with"} >>
        (fn ((s, t), u) =>
            Toplevel.proof (fn state => var_induct_cmd (s, t, u) state)))

end  (* structure Induct_ProofSteps. *)

val add_prfstep_induction = Induct_ProofSteps.add_prfstep_induction
val add_prfstep_strong_induction = Induct_ProofSteps.add_prfstep_strong_induction
val add_case_induct_rule = Induct_ProofSteps.add_case_induct_rule
val add_prop_induct_rule = Induct_ProofSteps.add_prop_induct_rule
val add_var_induct_rule = Induct_ProofSteps.add_var_induct_rule
val add_prfstep_double_induction = Induct_ProofSteps.add_prfstep_double_induction
