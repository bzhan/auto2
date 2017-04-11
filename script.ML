(* Definition of scripts. *)

infixr 0 THEN
infixr 1 WITH

datatype script
  = Script_Task of {inits: init_info list, subs: script list,
                    cb: (box_id * thm) * status -> raw_update list,
                    end_vars: term list}
type scripts = script list
type pre_scripts = Proof.context -> scripts

signature SCRIPT =
sig
  val update_callback: (box_id * thm) * status -> raw_update list
  val no_script: pre_scripts
  val get_end_vars: scripts -> term list
  val get_all_vars: scripts -> term list
  val check_new_vars: Proof.context -> string list -> term -> unit
  val CASE: string -> pre_scripts
  val HAVE: string -> pre_scripts
  val THEN: pre_scripts * pre_scripts -> pre_scripts
  val WITH: pre_scripts * pre_scripts -> pre_scripts

  (* CHOOSE scripts *)
  val CHOOSE: string -> pre_scripts
  val CHOOSES: string list -> pre_scripts
  val LET: string -> pre_scripts
  val CHOOSE_FUN_N: int -> string -> pre_scripts
end

functor Script(Base:UTIL_BASE) : SCRIPT =
struct

structure UtilLogic = UtilLogic(Base)
structure Update = Update(Base)
structure Logic_ProofSteps = Logic_ProofSteps(Base)
open Base
open UtilLogic
open Logic_ProofSteps

fun update_callback ((id, th), _) = [Update.thm_update (id, th)]
val no_script = K []
fun get_end_vars_single (Script_Task {end_vars, ...}) = end_vars
fun get_end_vars scrpt = maps get_end_vars_single scrpt

fun get_all_vars_single (Script_Task {inits, subs, end_vars, ...}) =
    maps Update.dest_init_var inits @ end_vars @ get_all_vars subs

and get_all_vars scrpt = maps get_all_vars_single scrpt |> distinct (op aconv)

(* Check for unexpected new variables in script. *)
fun check_new_vars ctxt nms t =
    let
      val new_nms = (subtract (op =) nms (Term.add_free_names t []))
                        |> filter_out (Variable.is_fixed ctxt)
    in
      if length new_nms = 0 then () else let
        val _ = trace_t_ctxt ctxt "At" t
        val _ = tracing ("Variable " ^ commas new_nms)
      in
        raise AUTO2 "unexpected new variable names."
      end
    end

fun CASE str ctxt =
    let
      val t = read_term ctxt str
      val _ = check_new_vars ctxt [] t
    in
      [Script_Task {inits = [InitAssum (mk_Trueprop t)],
                    subs = [], cb = update_callback, end_vars = []}]
    end

(* Given str in the form !x_1 ... x_k. P_1 --> ... --> P_n --> Q,
   create box with initial variables x_1 to x_k, and initial
   assumptions P_1 to P_n and ~Q. The variables x_1 ... x_k should be
   reserved beforehand and not used when this line is executed.
 *)
fun HAVE str ctxt =
    let
      val t = read_term ctxt str
      val init_infos =
          map (fn (is_var, t) => if is_var then InitVar t
                                 else InitAssum (mk_Trueprop t))
              (extract_init_infos false t)
      val vars = maps Update.dest_init_var init_infos
      val nms = map (fst o Term.dest_Free) vars
      val _ = check_new_vars ctxt nms t
    in
      if exists (Variable.is_fixed ctxt) nms then
        let
          val to_print = filter (Variable.is_fixed ctxt) nms
          val _ = trace_t_ctxt ctxt "At" t
          val _ = tracing ("Variables " ^ commas to_print)
        in
          raise AUTO2 "HAVE: variable name(s) already used."
        end
      else
        [Script_Task {inits = init_infos, subs = [], cb = update_callback,
                      end_vars = []}]
    end

fun (s1 THEN s2) ctxt =
    let
      val s1' = s1 ctxt
      val ctxt' = ctxt |> fold declare_free_term (get_end_vars s1')
    in
      s1' @ (s2 ctxt')
    end

fun (s1 WITH s2) ctxt =
    case s1 ctxt of
        [Script_Task {inits, subs = _, cb, end_vars}] =>
        let
          val vars = maps Update.dest_init_var inits
          val ctxt' = ctxt |> fold declare_free_term (vars @ end_vars)
          val s2' = s2 ctxt'
        in
          [Script_Task {inits = inits, subs = s2', cb = cb,
                        end_vars = end_vars}]
        end
      | _ => raise AUTO2 "WITH: first argument should be single script."

(* Form the exists proposition. conds_spec is a list of pairs ((nm,
   T), cond), where Free (nm, T) is the new variable appearing in
   cond.
 *)
fun form_exists_prop conds_spec concl =
    case conds_spec of
        [] => concl
      | ((nm, T), cond) :: rest =>
        let
          val concl' = form_exists_prop rest concl
        in
          if Free (nm, T) aconv cond then
            mk_exists (nm, T, concl')
          else
            case cond of
                Const (c, _) $ _ $ S =>
                if c = Mem_name then
                  let
                    val bexT = (mk_setT T) --> (T --> boolT) --> boolT
                  in
                    Const (Bex_name, bexT) $ S $ Term.absfree (nm, T) concl'
                  end
                else mk_exists (nm, T, mk_conj (cond, concl'))
              | _ => mk_exists (nm, T, mk_conj (cond, concl'))
        end

(* Given a list of terms, where each term contains exactly one new
   variable that does not appear in ctxt or the previous terms, return
   the list of new variables as a list.
 *)
fun extract_new_vars ctxt ts =
    case ts of
        [] => []
      | t :: ts' =>
        let
          val vars = Term.add_frees t []
          val new_vars =
              filter_out (fn (nm, _) => Variable.is_fixed ctxt nm) vars
        in
          if length new_vars = 1 then
            let
              val (nm, T) = the_single new_vars
              val ctxt' = ctxt |> declare_free_term (Free (nm, T))
            in
              (nm, T) :: extract_new_vars ctxt' ts'
            end
          else
            let
              val _ = trace_t_ctxt ctxt "At" t
              val _ = if length new_vars = 0 then tracing "No new variables"
                      else trace_tlist_ctxt
                               ctxt "New variables:" (map Free new_vars)
            in
              raise AUTO2 "extract_new_vars: number of new variables is not 1."
            end
        end

fun read_choose_str str ctxt =
    let
      val ts = str |> split_commas |> Syntax.read_terms ctxt
      val (conds, concl) = split_last ts
      val new_vars = extract_new_vars ctxt conds

      (* Exist proposition to prove. *)
      val ex_prop = mk_Trueprop (form_exists_prop (new_vars ~~ conds) concl)

      (* Check the variable names are new in ctxt. *)
      val _ = assert (not (exists (Variable.is_fixed ctxt) (map fst new_vars)))
                     "CHOOSE: variable name(s) already used."
      val _ = check_new_vars ctxt (map fst new_vars) ex_prop
    in
      (new_vars, ex_prop)
    end

fun CHOOSE str ctxt =
    let
      val (new_vars, ex_prop) = read_choose_str str ctxt
      fun choose_callback ((id, th), {ctxt, ...}) =
          Update.apply_exists (id, th) ctxt (map fst new_vars)
    in
      [Script_Task {inits = [InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

fun CHOOSES strs =
    case strs of
        [str] => CHOOSE str
      | str :: rest => (CHOOSE str) THEN (CHOOSES rest)
      | _ => raise AUTO2 "CHOOSES: empty argument"

fun LET str ctxt =
    let
      val eqs = str |> split_commas |> Syntax.read_terms ctxt

      fun process_eq ctxt eq =
          let
            val (lhs, rhs) = dest_eq eq
            val nm = lhs |> Term.dest_Free |> fst
            val pat_a = case ex_vardef_th |> prop_of' |> dest_arg of
                            Abs (_, _, b) => dest_arg b
                          | _ => raise AUTO2 "ex_vardef_th"
            val inst = pattern_fo_match ctxt (pat_a, rhs)
            val ex_th = subst_thm ctxt inst ex_vardef_th
            val (ritems, new_th) = Update.apply_exists_ritems ex_th ctxt [nm]
          in
            ritems @ [Update.thm_to_ritem new_th]
          end

      fun let_callback ((id, _), {ctxt, ...}) =
          [AddItems {id = id, sc = NONE,
                     raw_items = maps (process_eq ctxt) eqs}]

      val not_True = bTrue |> get_neg |> mk_Trueprop
    in
      [Script_Task {inits = [InitAssum not_True], subs = [],
                    cb = let_callback, end_vars = map dest_eq_lhs eqs}]
    end

fun CHOOSE_FUN_N n str ctxt =
    let
      val (new_vars, ex_prop) = read_choose_str str ctxt
      val _ = assert (length new_vars = 1)
                     "CHOOSE_FUN_N: only permit defining one function."

      (* Also zero indices *)
      fun split_conj_th' th =
          if is_conj (prop_of' th) then
            Drule.zero_var_indexes (th RS conjunct1_th) ::
            split_conj_th (Drule.zero_var_indexes (th RS conjunct2_th))
          else [th]

      (* Given a theorem about function f, for example

         !x. P (f x) & !y. Q (f x y),

         extract the properties of successive applications of f,
         returning them as term_def items. In the example above, the
         result would be [(f ?x, P (f ?x)), (f ?x ?y1), Q (f ?x ?y1)].
       *)
      fun prop_f_to_updt ctxt count id (f, prop_f_th) =
          case prop_of' prop_f_th of
              Const (c, _) $ Abs (nm, T, _) =>
              if c = All_name then
                let
                  val sch_var = Var ((nm, count), T)
                  val (ths, next) =
                      prop_f_th |> apply_to_thm (Conv.rewr_conv (
                                                    meta_sym atomize_all_th))
                                |> Thm.forall_elim (cert ctxt sch_var)
                                |> split_conj_th' |> split_last
                  val pat = f $ sch_var
                  fun to_updt th = term_def_updt (id, (pat, th))
                in
                  if count = n - 1 then
                    maps to_updt (ths @ [next])
                  else
                    maps to_updt ths @
                    prop_f_to_updt ctxt (count + 1) id (pat, next)
                end
              else raise AUTO2 "CHOOSE_FUN_N: wrong form of prop_f_th."
            | _ => raise AUTO2 "CHOOSE_FUN_N: wrong form of prop_f_th."

      fun choose_callback ((id, th), {ctxt, ...}) =
          let
            val (ritems, th) =
                Update.apply_exists_ritems th ctxt (map fst new_vars)

            (* When choosing function F, this is the theorem !x. P (F i). *)
            val prop_f_th = th |> split_conj_th' |> List.last
            val f = Free (the_single new_vars)
          in
            AddItems {id = id, sc = NONE,
                      raw_items = ritems @ [Update.thm_to_ritem th]} ::
            prop_f_to_updt ctxt 0 id (f, prop_f_th)
          end
    in
      [Script_Task {inits = [InitAssum (get_neg' ex_prop)], subs = [],
                    cb = choose_callback, end_vars = map Free new_vars}]
    end

end  (* structure Script. *)
