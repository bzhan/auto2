(* Unfolding of functional definitions *)

signature UNFOLDING =
sig
  val add_unfolding_rule: thm -> theory -> theory
  val unfold: theory -> conv
  val unfold_cmd: string -> Proof.state -> Proof.state
end;

structure Unfolding : UNFOLDING =
struct

structure Data = Theory_Data (
  type T = thm list Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge_list Thm.eq_thm_prop
)

(* Add the given theorem as an unfolding rule. *)
fun add_unfolding_rule th thy =
    let
      val (lhs, _) = th |> prop_of' |> dest_eq
      val nm = case Term.head_of lhs of
                   Const (nm, _) => nm
                 | _ => raise Fail "add_unfolding_rule"
    in
      thy |> Data.map (Symtab.map_default (nm, []) (cons th))
    end

(* Unfold the given term. *)
fun unfold thy ct =
    let
      val t = Thm.term_of ct
      val nm = case Term.head_of t of
                   Const (nm, _) => nm
                 | _ => raise Fail "unfold"
      val ths = Symtab.lookup_list (Data.get thy) nm
    in
      Conv.first_conv (map rewr_obj_eq ths) ct
    end

fun unfold_cmd s state =
    let
      val {context = ctxt, ...} = Proof.goal state
      val thy = Proof_Context.theory_of ctxt

      val (_, (As, _)) = ctxt |> Auto2_State.get_selected |> Auto2_State.subgoal_of
                              |> Thm.term_of |> Util.strip_meta_horn
      val cAs = map (Thm.cterm_of ctxt) As

      val t = Syntax.read_term ctxt s
      val eq_th = t |> Thm.cterm_of ctxt |> unfold thy
                    |> to_obj_eq
                    |> fold Thm.implies_intr (rev cAs)
      val _ = writeln ("Obtained " ^ (eq_th |> Thm.concl_of
                                            |> Syntax.string_of_term ctxt))

      val after_qed = Auto2_Outer.have_after_qed ctxt eq_th
    in
      state |> Proof.map_contexts (Auto2_State.map_head_th after_qed)
    end

val _ =
  Outer_Syntax.command @{command_keyword "@unfold"} "unfold a term"
    ((Parse.term --| Scan.option @{keyword "@then"}) >>
        (fn s =>
            Toplevel.proof (fn state => unfold_cmd s state)))

end  (* structure Unfolding *)

val add_unfolding_rule = Unfolding.add_unfolding_rule
