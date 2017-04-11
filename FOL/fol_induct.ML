(* Specifying induction using scripts. *)

(* Each induction rule is placed under the pattern for its
   precondition.
 *)
structure ScriptInductData =
Generic_Data (
  type T = (term * thm) Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge (op aconv o apply2 fst)
)

signature SCRIPT_INDUCT_DATA =
sig
  val add_script_induct_data_gnrc: thm -> Context.generic -> Context.generic
  val add_script_induct_data: thm -> theory -> theory
  val delete_script_induct_data: thm -> theory -> theory
  val lookup_script_induct_data: Proof.context -> term -> thm option
  val INDUCT_ON: string -> string -> pre_scripts
end;

structure ScriptInduct_Data : SCRIPT_INDUCT_DATA =
struct

fun add_script_induct_data_gnrc th gnrc =
    let
      val nm = name_of_thm th
      val thy = theory_of_gnrc gnrc
      val t = Thm.prems_of th |> List.last |> dest_Trueprop
      val _ = writeln ("Add induction rule for premise " ^
                       (t |> pretty_term_thy thy |> str))
    in
      ScriptInductData.map (Symtab.update_new (nm, (t, th))) gnrc
    end

val add_script_induct_data =
    Context.theory_map o add_script_induct_data_gnrc

fun delete_script_induct_data_gnrc th =
    ScriptInductData.map (Symtab.delete (name_of_thm th))

val delete_script_induct_data =
    Context.theory_map o delete_script_induct_data_gnrc

fun lookup_script_induct_data ctxt t =
    let
      val data = Symtab.dest (ScriptInductData.get (Context.Proof ctxt))
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

fun INDUCT_ON str_prem str_goal ctxt =
    let
      val thy = Proof_Context.theory_of ctxt
      val prem = read_term ctxt str_prem
      val goal = read_term ctxt str_goal
    in
      case lookup_script_induct_data ctxt prem of
          NONE => raise AUTO2 "INDUCT_ON: cannot find theorem."
        | SOME th =>
          let
            val concl = concl_of' th
            val (P, vars) = Term.strip_comb concl
            val _ = assert (Term.is_Var P)
                           "INDUCT_ON: P is not schematic variable."
            val P_inst = fold Term.lambda (rev vars) goal
            val inst = update_env (("P", 0), P_inst) fo_init
            val th' = subst_thm_thy thy inst th

            fun callback ((id, _), _) =
                Update.apply_horn_clause (id, th') (Update.null_callback)

            val not_True = bTrue |> get_neg |> mk_Trueprop
          in
            [Script_Task {inits = [InitAssum not_True], subs = [],
                          cb = callback, end_vars = []}]
          end
    end

end  (* structure ScriptInduct_Data *)

val add_script_induct_data_gnrc = ScriptInduct_Data.add_script_induct_data_gnrc
val add_script_induct_data = ScriptInduct_Data.add_script_induct_data
val delete_script_induct_data = ScriptInduct_Data.delete_script_induct_data
val INDUCT_ON = ScriptInduct_Data.INDUCT_ON
