(* Automation for structures *)

type field_info = {
  name_th: thm,
  accessor_th: thm
}

signature STRUCTURE =
sig
  (* Some basic results on sets *)
  val empty_set: term
  val is_cons: term -> bool
  val is_finite_set: term -> bool
  val strip_set: term -> term list

  (* Table of field data *)
  val get_unfold_thms_by_name: theory -> string -> thm list
  val get_unfold_thms: theory -> term -> thm list
  val add_field_data: term * term -> theory -> theory
  val get_field_data: theory -> term -> field_info
  val field_name_rewrite: theory -> term -> thm
  val rewr_accessor: theory -> conv

  val succ_neq_resolve: thm -> thm
  val succ_neq: Proof.context -> term * term -> thm
  val succ_neq_names: Proof.context -> term * term -> thm
  val not_mem_field_names: Proof.context -> term * term -> thm
  val mem_th: Proof.context -> term * term -> thm
  val is_func_graph: Proof.context -> term -> thm
  val accessor_eqs: Proof.context -> term -> thm list
  val forall_cons_dest: conv
  val rewr_conj_fields: theory -> conv
  val struct_eq_th: Proof.context -> thm -> thm -> thm

  val dest_struct_cv: conv
  val add_struct_cv: conv
  val add_structure_prfsteps: theory -> theory
end;

structure Structure : STRUCTURE =
struct

val empty_set = @{term Empty_set}

fun is_cons t =
    case t of
        Const (@{const_name cons}, _) $ _ $ _ => true
      | _ => false

fun is_finite_set t =
    if t aconv empty_set then true
    else case t of Const (@{const_name cons}, _) $ _ $ S => is_finite_set S
                 | _ => false

(* Given a set of elements S, return the elements as a list. *)
fun strip_set S =
    if is_cons S then
      let
        val (a, T) = Util.dest_binop_args S
      in
        a :: strip_set T
      end
    else []

(* Register of field names and accessors. *)
structure Data = Theory_Data (
  type T = field_info Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  val merge = Symtab.merge pointer_eq
)

fun get_unfold_thms_by_name thy nm =
    let
      val simp_nm = nm ^ ".simps"
      val def_nm = nm ^ "_def"
    in
      Global_Theory.get_thms thy simp_nm
      handle ERROR _ => Global_Theory.get_thms thy def_nm
                        handle ERROR _ => raise Fail "get_unfold_thms"
    end

fun get_unfold_thms thy t =
    get_unfold_thms_by_name thy (Util.get_head_name t)

fun add_field_data (name, accessor) thy =
    let
      val (s1, _) = Term.dest_Const name
      val (s2, _) = Term.dest_Const accessor
      val name_th = the_single (get_unfold_thms thy name)
      val accessor_th = the_single (get_unfold_thms thy accessor)
      val field_info = {name_th = name_th, accessor_th = accessor_th}
    in
      Data.map (
        fold Symtab.update_new [(s1, field_info), (s2, field_info)]) thy
    end

fun get_field_data thy t =
    let
      val (nm, _) = Term.dest_Const t
    in
      the (Symtab.lookup (Data.get thy) nm)
    end

(* Given the name of a field, get equation rewriting it to succ(...) form. *)
fun field_name_rewrite thy t =
    t |> get_unfold_thms thy |> the_single

(* Given ct of the form graph_eval(S, field_name), rewrite to field(S). *)
fun rewr_accessor thy ct =
    let
      val t = Thm.term_of ct
      val (_, field_name) = t |> Util.dest_binop_args
      val {accessor_th, ...} = get_field_data thy field_name
    in
      rewr_obj_eq (obj_sym accessor_th) ct
    end

(* Show a contradiction from an equality between two terms of the form
   succ(succ(...)), that are actually not equal. *)
fun succ_neq_resolve th =
    let
      val (m, n) = th |> prop_of' |> dest_eq
    in
      if m aconv empty_set then
        [@{thm succ_nonzero}, obj_sym th] MRS UtilBase.contra_triv_th
      else if n aconv empty_set then
        [@{thm succ_nonzero}, th] MRS UtilBase.contra_triv_th
      else
        succ_neq_resolve (th RS @{thm succ_inj})
    end

(* Given two terms of the form succ(succ(...)) that are not equal,
   obtain a theorem showing this inequality. *)
fun succ_neq ctxt (s, t) =
    let
      val s_eq_t = mk_eq (s, t) |> mk_Trueprop |> Thm.cterm_of ctxt
    in
      s_eq_t |> Thm.assume |> succ_neq_resolve
             |> Thm.implies_intr s_eq_t
             |> apply_to_thm UtilLogic.rewrite_from_contra_form
    end

(* Given two names s and t, obtain theorem showing they are not equal. *)
fun succ_neq_names ctxt (s, t) =
    let
      val thy = Proof_Context.theory_of ctxt
      val s_eq = field_name_rewrite thy s
      val t_eq = field_name_rewrite thy t
      val (_, s') = dest_eq (prop_of' s_eq)
      val (_, t') = dest_eq (prop_of' t_eq)
      val neq = succ_neq ctxt (s', t')
    in
      neq |> apply_to_thm' (
        Conv.arg_conv (
          Conv.every_conv [Conv.arg1_conv (rewr_obj_eq (obj_sym s_eq)),
                           Conv.arg_conv (rewr_obj_eq (obj_sym t_eq))]))
    end

(* Produce theorems of the form x ~: S, where S is a set of field names. *)
fun not_mem_field_names ctxt (x, S) =
    if S aconv empty_set then
      let
        val inst = fo_init |> Util.update_env (("x",0), x)
      in
        Util.subst_thm ctxt inst @{thm empty_set}
      end
    else
      let
        val (a, T) = S |> Util.dest_binop_args
        val neq_th = succ_neq_names ctxt (x, a)
        val not_mem_th = not_mem_field_names ctxt (x, T)
      in
        [neq_th, not_mem_th] MRS @{thm not_mem_cons}
      end

(* Given x and a set S containing x, return the theorem x : S. *)
fun mem_th ctxt (x, S) =
    let
      val (y, T) = S |> Util.dest_binop_args
    in
      if x aconv y then
        let
          val inst = fo_init |> Util.update_env (("x",0), x)
                             |> Util.update_env (("S",0), T)
        in
          Util.subst_thm ctxt inst @{thm mem_cons_head}
        end
      else
        let
          val inst = fo_init |> Util.update_env (("y",0), y)
          val subst_th = Util.subst_thm ctxt inst @{thm mem_cons_tail}
          val th = mem_th ctxt (x, T)
        in
          th RS subst_th
        end
    end

(* Given F in the graph form {<field_name1, val1>, <field_name2,
   val2>, ...}, produce a theorem of the form is_func_graph(F,S),
   where S is a set of field names.
 *)
fun is_func_graph ctxt F =
    if F aconv empty_set then
      @{thm is_func_graph_empty}
    else
      let
        val (p, G) = F |> Util.dest_binop_args
        val (a, b) = p |> Util.dest_binop_args
        val rec_th = is_func_graph ctxt G
        val X = rec_th |> prop_of' |> dest_arg
        val not_mem_th = not_mem_field_names ctxt (a, X)
        val inst = fo_init |> Util.update_env (("b",0), b)
        val subst_th = Util.subst_thm ctxt inst @{thm is_func_graph_cons}
      in
        [rec_th, not_mem_th] MRS subst_th
      end

(* Given F in the graph from as above, produce the rewrites of
   accessors of F.
 *)
fun accessor_eqs ctxt F =
    let
      val ps = strip_set F
      val func_graph_th = is_func_graph ctxt F
      val S = func_graph_th |> prop_of' |> dest_arg
      val thy = Proof_Context.theory_of ctxt

      fun get_for_pair p =
          let
            val (a, _) = Util.dest_binop_args p
            val p_mem = mem_th ctxt (p, F)
            val a_mem = mem_th ctxt (a, S)

            (* graph_eval(F,field_name) = b *)
            val th = [func_graph_th, p_mem, a_mem] MRS @{thm is_func_graphD3}
          in
            (* Convert to field(F) = b *)
            th |> apply_to_thm' (Conv.arg1_conv (rewr_accessor thy))
          end
    in
      map get_for_pair ps
    end

(* Given !x:S. P(x) where S is a finite set, rewrite to a conjunction
   of P(a) for a : S.
 *)
fun forall_cons_dest ct =
    case Thm.term_of ct of
        Const (@{const_name Ball}, _) $ S $ _ =>
        if not (is_cons S) then
          raise Fail "forall_cons_dest"
        else if dest_arg S aconv empty_set then
          rewr_obj_eq @{thm forall_single} ct
        else
          Conv.every_conv [rewr_obj_eq @{thm forall_cons},
                           Conv.arg_conv forall_cons_dest] ct
      | _ => raise Fail "forall_cons_dest2"

(* Given a conjunction of graph_eval(F,field_name) =
   graph_eval(G,field_name), rewrite to field(F) = field(G) in each
   conjunct.
 *)
fun rewr_conj_fields thy ct =
    if is_conj (Thm.term_of ct) then
      Conv.every_conv [Conv.arg1_conv (Conv.binop_conv (rewr_accessor thy)),
                       Conv.arg_conv (rewr_conj_fields thy)] ct
    else
      Conv.binop_conv (rewr_accessor thy) ct

(* Given two theorems is_func_graph(F,X) and is_func_graph(G,X), where
   X is a set of field names, return the theorem implying F = G.
 *)
fun struct_eq_th ctxt th1 th2 =
    let
      val (_, X) = th1 |> prop_of' |> Util.dest_binop_args
      val (_, X') = th2 |> prop_of' |> Util.dest_binop_args
      val _ = assert (X aconv X') "struct_eq_th"
      val th = [th1, th2] MRS @{thm graph_eq}
      val thy = Proof_Context.theory_of ctxt
    in
      th |> apply_to_thm (UtilLogic.to_obj_conv ctxt)
         |> apply_to_thm' (Conv.arg1_conv forall_cons_dest)
         |> apply_to_thm' (Conv.arg1_conv (rewr_conj_fields thy))
    end

val dest_struct_cv = rewr_obj_eq @{thm Struct_def}
val add_struct_cv = rewr_obj_eq (obj_sym @{thm Struct_def})

val add_structure_prfsteps =
    fold add_prfstep_custom [
      ("is_func_graph",
       [WithTerm @{term_pat "Struct(?F)"}],
       PRIORITY_ADD,
       fn ((id, inst), _) => fn _ => fn ctxt =>
          let
            val F = Util.lookup_inst inst "F"
            val th =
                (is_func_graph ctxt F)
                    |> apply_to_thm' (Conv.arg1_conv add_struct_cv)
            val eq_ths =
                (accessor_eqs ctxt F)
                    |> map (apply_to_thm' (
                               Conv.arg1_conv (Conv.arg_conv add_struct_cv)))
          in
            [AddItems {id = id, sc = SOME 1,
                       raw_items = map Update.thm_to_ritem (th :: eq_ths)}]
          end),

      ("struct_eq",
       [WithFact @{term_pat "is_func_graph(?F,?X)"},
        WithFact @{term_pat "is_func_graph(?G,?X)"},
        Filter (neq_filter @{term_pat "(?F::i) ~= ?G"}),
        Filter (order_filter "F" "G")],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn ctxt =>
          if not (is_finite_set (Util.lookup_inst inst "X")) then []
          else let
            val (th1, th2) = the_pair ths
            val th = struct_eq_th ctxt th1 th2
          in
            [AddItems {id = id, sc = SOME 1,
                       raw_items = [Update.thm_to_ritem th]}]
          end)
    ]

end  (* structure Structure. *)

val _ = Theory.setup Structure.add_structure_prfsteps
val add_field_data = Structure.add_field_data
