(* Proof steps on imperative HOL. *)

structure HeapPreserveCmdData =
Theory_Data (
  type T = thm Termtab.table;
  val empty = Termtab.empty;
  val extend = I;
  val merge = Termtab.merge (op pointer_eq)
)

(* Check th is of proper form, and registers the appropriate pattern. *)
fun register_heap_preserve th =
    let
      val (cond, concl) = (Logic.dest_implies (Thm.prop_of th))
                              |> apply2 (HOLogic.dest_Trueprop)
      val (_, args) = Term.strip_comb cond
      val (h, h') = HOLogic.dest_eq concl
    in
      if length args = 4 andalso nth args 1 = h andalso nth args 2 = h' then
        let
          val ctxt = Proof_Context.init_global (Thm.theory_of_thm th)
          val pat = nth args 0
          val _ = trace_t_ctxt ctxt "register_heap_preserve for pattern:" pat
        in
          HeapPreserveCmdData.map (Termtab.update_new (pat, th))
        end
      else
        raise AUTO2 "register_heap_preserve: wrong form of theorem."
    end

(* Introduce all schematic variables in th as meta forall
   quantifications. The meta forall quantifications will appear in the
   same order as the variables appear in the statement of th.
 *)
fun forall_intr_sch_vars th =
    let
      val thy = Thm.theory_of_thm th
      val sch_vars = map Var (Term.add_vars (Thm.prop_of th) [])
    in
      th |> fold Thm.forall_intr (map (cert_thy thy) sch_vars)
    end

(* Match cmd with each of the patterns. h is the starting heap. *)
fun find_heap_preserve_cmd ctxt cmd h =
    let
      val thy = Proof_Context.theory_of ctxt
      val cmd_data = HeapPreserveCmdData.get thy
      fun match_val (pat, th) =
          let
            val inst = (pattern_fo_match_thy thy (pat, cmd))
                           |> update_env (("h", 0), h)
          in
            SOME (subst_thm ctxt inst th)
          end
          handle Pattern.MATCH => NONE
    in
      (Termtab.get_first match_val cmd_data)
          |> Option.map forall_intr_sch_vars
          |> Option.map (apply_to_thm (to_obj_conv ctxt))
    end

val _ = Theory.setup (
      fold (register_heap_preserve o conj_left_th) [
        @{thm effect_comment}, @{thm effect_assert}, @{thm effect_return},
        @{thm effect_lookup}, @{thm effect_nth}])

fun next_name nm =
    let
      val tokens = space_explode "_" nm
      val (pre, last) = (split_last tokens) |> apfst (space_implode "_")
      val (n, rest) = read_int (raw_explode last)
    in
      case rest of
          [] => pre ^ "_" ^ (string_of_int (n + 1))
        | _ => nm ^ "_1"
    end

(* Used in effect_bind and success_bind below. Obtain name of the next
   heap from name of the starting heap (which is ?h in inst).
 *)
fun get_next_heap_name inst =
    let
      val hval = lookup_inst inst "h"
      val (h_nm, _) =
          Term.dest_Free hval
          handle TERM _ =>
                 raise AUTO2 "effect_var_names: h is not free variable"
    in
      Name.internal (next_name h_nm)
    end

(* Used in effect_bind and success_bind below. Obtain name of the
   return variable (from the abstraction variable in ?g).
 *)
fun get_return_var_name inst =
    case lookup_inst inst "g" of
        Abs (x, _, _) => if x = "uu_" then "r_" else Name.internal x
      | _ => "r_"

val effect_bind =
    prfstep_custom
        "effect_bind"
        [WithFact @{term_pat "effect (?f >>= ?g) ?h ?h' ?r'"}]
        PRIORITY_ADD
        (fn ((id, inst), ths) => fn _ => fn {ctxt, ...} =>
            let
              val fval = lookup_inst inst "f"
              val hval = lookup_inst inst "h"
              val const_opt_th = find_heap_preserve_cmd ctxt fval hval
              val is_f_unit = (fastype_of fval = @{typ "unit Heap"})
              val ex_th =
                  case const_opt_th of
                      NONE => if is_f_unit then ths MRS @{thm effect_bind_unit}
                              else ths MRS @{thm effect_bind}
                    | SOME const_th =>
                      if is_f_unit then
                        (const_th :: ths) MRS @{thm effect_bind_same_unit}
                      else (const_th :: ths) MRS @{thm effect_bind_same}
              val var_names =
                  (if is_some const_opt_th then []
                   else [get_next_heap_name inst]) @
                  (if is_f_unit then [] else [get_return_var_name inst])
            in
              Update.apply_exists (id, ex_th) ctxt var_names
            end)
val _ = Theory.setup (add_prfstep effect_bind)

val success_bind =
    prfstep_custom
        "success_bind"
        [WithFact @{term_pat "success (?f::?'a Heap) ?h"},
         WithGoal @{term_pat "success ((?f::?'a Heap) >>= ?g) ?h"}]
        PRIORITY_ADD
        (fn ((id, inst), ths) => fn _ => fn {ctxt, ...} =>
            let
              val (th_f, _) = the_pair ths
              val fval = lookup_inst inst "f"
              val hval = lookup_inst inst "h"
              val const_opt_th = find_heap_preserve_cmd ctxt fval hval
              val is_f_unit = (fastype_of fval = @{typ "unit Heap"})
              val effect_th =
                  case const_opt_th of
                      NONE =>
                      if is_f_unit then th_f RS @{thm success_to_effect_unit}
                      else th_f RS @{thm success_to_effect}
                    | SOME const_th =>
                      if is_f_unit then
                        [const_th, th_f] MRS @{thm success_to_effect_same_unit}
                      else
                        [const_th, th_f] MRS @{thm success_to_effect_same}
              val var_names =
                  (if is_some const_opt_th then []
                   else [get_next_heap_name inst]) @
                  (if is_f_unit then [] else [get_return_var_name inst])
            in
              Update.apply_exists (id, effect_th) ctxt var_names
            end)
val _ = Theory.setup (add_prfstep success_bind)

fun prfstep_imp_effect_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn (st as {ctxt, ...}) =>
            let
              val init_th = the_single ths
              val init_prop = Thm.prop_of init_th
              val init_prop' = HOLogic.dest_Trueprop init_prop
              val (cmd, h, h', r) =
                  case init_prop' of
                      Const ("Heap_Monad.effect", _) $ cmd $ h $ h' $ r =>
                      (cmd, h, h', r)
                    | _ => raise AUTO2 "imp_effect_induction: wrong input."
              val extra_vars = [h, h', r]
              val (_, ind_vars) = Term.strip_comb cmd
              val gen_vars = ind_vars @ extra_vars
              val var_ctxt = get_var_context id gen_vars st
            in
              case var_ctxt of
                  NONE => []
                | SOME (inits as (_, assums)) =>
                  if member (op aconv) assums init_prop then
                    apply_induction
                        id inits (map (rpair NONE) ind_vars) ctxt ind_th []
                  else []
            end)

fun prfstep_imp_success_induction name descs ind_th =
    prfstep_custom
        name descs PRIORITY_ADD
        (fn ((id, _), ths) => fn _ => fn (st as {ctxt, ...}) =>
            let
              val init_th = the_single ths
              val init_prop = Thm.prop_of init_th
              val init_prop' = HOLogic.dest_Trueprop init_prop
              val (cmd, h) =
                  case init_prop' of
                      Const ("HOL.Not", _) $ (
                        Const ("Heap_Monad.success", _) $ cmd $ h) => (cmd, h)
                    | _ => raise AUTO2 "success_imp_induction: wrong input."
              val extra_vars = [h]
              val (_, ind_vars) = Term.strip_comb cmd
              val gen_vars = ind_vars @ extra_vars
              val var_ctxt = get_var_context id gen_vars st
            in
              case var_ctxt of
                  NONE => []
                | SOME (inits as (_, assums)) =>
                  if member (op aconv) assums init_prop then
                    apply_induction
                        id inits (map (rpair NONE) ind_vars) ctxt ind_th []
                  else []
            end)

fun add_prfstep_imp_induction cmd_pat ind_th thy =
    let
      val name = name_of_thm ind_th

      (* Obtain type 'a Heap. *)
      val ctxt = Proof_Context.init_global thy
      val ty_aHeap = (Term.type_of @{term_pat "effect"})
                         |> Term.dest_Type |> snd |> hd
      val ty_inst = pattern_match_ty ctxt (ty_aHeap, type_of cmd_pat)
      val cmd_inst = update_env (("cmd", 0), cmd_pat) fo_init

      (* First part: induction when have effect cmd h h' r as fact. *)
      val name_effect = name ^ "@effect"
      val effect_pat = @{term_pat "effect (?cmd::?'a Heap) ?h ?h' ?rs"}
                            |> Envir.subst_term_types ty_inst
                            |> Envir.subst_term cmd_inst
      val descs_effect =
          [WithFact effect_pat] @ [Filter (id_filter (equal [0]))]
      val _ = writeln (name_effect ^ "\n" ^ (string_of_descs thy descs_effect))
      val prfstep_effect =
          prfstep_imp_effect_induction name_effect descs_effect ind_th

      (* Second part: induction when have success cmd h as goal. *)
      val name_success = name ^ "@success"
      val success_pat = @{term_pat "~ success (?cmd::?'a Heap) ?h"}
                             |> Envir.subst_term_types ty_inst
                             |> Envir.subst_term cmd_inst
      val descs_success =
          [WithFact success_pat] @ [Filter (id_filter (equal [0]))]
      val _ = writeln (name_success ^ "\n" ^
                       (string_of_descs thy descs_success))
      val prfstep_success =
          prfstep_imp_success_induction name_success descs_success ind_th
    in
      thy |> add_prfstep prfstep_effect
          |> add_prfstep prfstep_success
    end
