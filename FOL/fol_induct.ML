(* Specifying induction using scripts. *)

signature SCRIPT_INDUCT_DATA =
sig
  val add_script_induct_data_gnrc: thm -> Context.generic -> Context.generic
  val add_script_induct_data: thm -> theory -> theory
  val delete_script_induct_data: thm -> theory -> theory
  val lookup_script_induct_data: Proof.context -> term -> thm option

  val induct_cmd: string * string -> Proof.state -> Proof.state

  val add_strong_induct_data_gnrc: thm -> Context.generic -> Context.generic
  val add_strong_induct_data: thm -> theory -> theory
  val lookup_strong_induct_data: Proof.context -> term -> thm option
  val strong_induct_cmd: string * string list -> Proof.state -> Proof.state
end;

structure ScriptInduct_Data : SCRIPT_INDUCT_DATA =
struct

(* Each induction rule is placed under the pattern for its
   precondition.
 *)
structure InductData = Generic_Data (
  type T = (term * thm) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (op aconv o apply2 fst)
)

structure StrongInductData = Generic_Data (
  type T = (term * thm) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (op aconv o apply2 fst)
)

fun add_script_induct_data_gnrc th gnrc =
    let
      val nm = name_of_thm th
      val thy = Context.theory_of gnrc
      val t = Thm.prems_of th |> List.last |> dest_Trueprop
      val _ = writeln ("Add induction rule for premise " ^
                       (t |> pretty_term_thy thy |> str))
    in
      InductData.map (Symtab.update_new (nm, (t, th))) gnrc
    end

val add_script_induct_data =
    Context.theory_map o add_script_induct_data_gnrc

fun delete_script_induct_data_gnrc th =
    InductData.map (Symtab.delete (name_of_thm th))

val delete_script_induct_data =
    Context.theory_map o delete_script_induct_data_gnrc

fun lookup_script_induct_data ctxt t =
    let
      val data = Symtab.dest (InductData.get (Context.Proof ctxt))
      val thy = Proof_Context.theory_of ctxt
      fun match_data (_, (pat, th)) =
          let
            val inst = pattern_fo_match_thy thy (pat, t)
          in
            SOME (subst_thm_thy thy inst th)
          end
          handle Pattern.MATCH => NONE
    in
      get_first match_data data
    end

fun induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val (prem, goal) = the_pair (Syntax.read_terms ctxt [s, t])
    in
      case lookup_script_induct_data ctxt prem of
          NONE => raise Fail "induct: cannot find theorem."
        | SOME th =>
          let
            (* Obtain the induction theorem *)
            val concl = concl_of' th
            val (P, vars) = Term.strip_comb concl
            val _ = assert (Term.is_Var P)
                           "INDUCT_ON: P is not schematic variable."
            val P_inst = fold Term.lambda (rev vars) goal
            val inst = update_env (("P", 0), P_inst) fo_init
            val ind_th = subst_thm_thy thy inst th

            (* Obtain list of assumptions *)
            val {prop, ...} = Auto2_Outer.get_head ctxt
            val (_, body) = prop |> Auto2_Outer.subgoal_of |> Thm.term_of |> Auto2_Outer.strip_goal
            val (As, _) = Logic.strip_horn body
            val cAs = map (cert ctxt) As

            val ind_goals =
                ind_th |> Thm.prems_of
                       |> map (fn t => Logic.list_implies (As, t))

            val ths = (map (Auto2_Outer.auto2_solve ctxt o cert ctxt) ind_goals)
                          |> map send_all_to_hyps

            val ind_concl = (ths MRS ind_th)
                                |> fold Thm.implies_intr (rev cAs)

            val after_qed = Auto2_Outer.have_after_qed ctxt ind_concl
          in
            state |> Proof.map_contexts (Auto2_Outer.map_head_th after_qed)
          end
    end

val _ =
  Outer_Syntax.command @{command_keyword "@induct"} "apply induction"
    ((Parse.term -- Parse.term) >>
        (fn (s, t) =>
            Toplevel.proof (fn state => induct_cmd (s, t) state)))

fun add_strong_induct_data_gnrc th gnrc =
    let
      val nm = name_of_thm th
      val thy = Context.theory_of gnrc
      val t = Thm.prems_of th |> List.last |> dest_Trueprop
      val _ = writeln ("Add strong induction rule for premise " ^
                       (t |> pretty_term_thy thy |> str))
    in
      StrongInductData.map (Symtab.update_new (nm, (t, th))) gnrc
    end

val add_strong_induct_data =
    Context.theory_map o add_strong_induct_data_gnrc

fun lookup_strong_induct_data ctxt t =
    let
      val data = Symtab.dest (StrongInductData.get (Context.Proof ctxt))
      val thy = Proof_Context.theory_of ctxt
      fun match_data (_, (pat, th)) =
          let
            val inst = pattern_fo_match_thy thy (pat, t)
          in
            SOME (subst_thm_thy thy inst th)
          end
          handle Pattern.MATCH => NONE
    in
      get_first match_data data
    end

fun strong_induct_cmd (s, t) state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt
      val prem = s |> Syntax.read_term ctxt

      val arbitraries = map (Syntax.read_term ctxt) t

      val {prop, ...} = Auto2_Outer.get_head ctxt
      val goal = prop |> Auto2_Outer.subgoal_of |> Thm.term_of

      val ind_th = the (lookup_strong_induct_data ctxt prem)
                   handle Option.Option =>
                          error "Strong induction: ind_th not found."

      val (var_P, var) = ind_th |> Thm.concl_of |> dest_Trueprop
                                |> Term.dest_comb

      val (assums, concl) = goal |> Logic.strip_horn
                                 |> apfst (map dest_Trueprop)
                                 |> apfst (remove (op aconv) prem)
                                 |> apsnd dest_Trueprop
      val P = (list_obj_imp (assums, concl))
                  |> fold mk_obj_all (rev arbitraries)
                  |> lambda_abstract var

      val inst = Pattern.match thy (var_P, P) fo_init
      val ind_th =
          ind_th |> subst_thm ctxt inst
                 |> apply_to_thm (Conv.binop_conv (to_meta_all_imp_conv ctxt))

      val assum = hd (Drule.cprems_of ind_th)
      val ind_th =
          ind_th |> send_first_to_hyps
                 |> fold Thm.forall_elim (map (cert ctxt) arbitraries)
                 |> Thm.implies_intr assum

      val t' = case Thm.prop_of ind_th of
                   imp $ A $ B => imp $ rename_abs_term [var] A $ B
                 | _ => error "strong_induct_cmd"

      val ind_th = ind_th |> Thm.renamed_prop t'
                          |> Goal.protect 1
    in
      state |> Proof.map_contexts (Auto2_Outer.set_head_th ind_th)
    end

val arbitrary =
    Scan.option (@{keyword "arbitrary"} |-- Scan.repeat Parse.term)

val _ =
  Outer_Syntax.command @{command_keyword "@strong_induct"}
    "apply strong induction"
    ((Parse.term -- arbitrary) >> (fn (s, t) =>
        Toplevel.proof (fn state => strong_induct_cmd (s, these t) state)))

end  (* structure ScriptInduct_Data *)

val add_script_induct_data_gnrc = ScriptInduct_Data.add_script_induct_data_gnrc
val add_script_induct_data = ScriptInduct_Data.add_script_induct_data
val delete_script_induct_data = ScriptInduct_Data.delete_script_induct_data
val add_strong_induct_data = ScriptInduct_Data.add_strong_induct_data
