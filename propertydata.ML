signature PROPERTY_DATA =
sig
  val clean_resolved: box_id -> Proof.context -> Proof.context

  val get_property_for_term: Proof.context -> term -> (box_id * thm) list
  val add_property_raw: box_id * thm -> Proof.context -> Proof.context
  val convert_property: Proof.context -> box_id * thm -> box_id * thm -> box_id * thm

  val get_property: Proof.context -> box_id * cterm -> (box_id * thm) list
  val get_property_t: Proof.context -> box_id * term -> (box_id * thm) list
  val apply_property_update_rule:
      Proof.context -> box_id -> thm option -> (box_id * thm) list
  val apply_property_update_on_term:
      Proof.context -> box_id -> term -> (box_id * thm) list
  val process_update_property:
      (box_id * thm) list -> Proof.context -> Proof.context
  val process_rewrite_property: box_id * thm -> Proof.context -> Proof.context
  val add_property: box_id * thm -> Proof.context -> Proof.context
  val get_new_property: int -> Proof.context -> (term * (box_id * thm)) list
end;

structure PropertyData : PROPERTY_DATA =

struct

structure Data = Proof_Data
(
  type T = ((box_id * thm) list) Termtab.table
  fun init _ = Termtab.empty
)

fun clean_resolved id ctxt =
    let
      fun clean_property tb =
          tb |> Termtab.map
             (fn _ => filter_out (BoxID.is_eq_ancestor ctxt id o fst))
    in
      ctxt |> Data.map clean_property
    end

(* Retrieve the current list of properties for a term t. *)
fun get_property_for_term ctxt t =
    let
      val property = Data.get ctxt
    in
      the_default [] (Termtab.lookup property t)
    end

(* Add a new property. Similar to add_equiv_raw. *)
fun add_property_raw (cur_info as (_, th)) ctxt =
    let
      val t = Property.get_property_arg (prop_of' th)
      val property_t = get_property_for_term ctxt t
    in
      if exists (fn info => BoxID.info_eq_better ctxt info cur_info)
                property_t then ctxt
      else
        ctxt |> Data.map (
          Termtab.update (
            t, property_t |> filter_out (BoxID.info_eq_better ctxt cur_info)
                          |> cons cur_info))
    end

(* Convert property P s to P t using equality s == t. Merge boxes
   corresponding to the two theorems.
 *)
fun convert_property ctxt (id', eq_th) (id, th) =
    (BoxID.merge_boxes ctxt (id, id'),
     th |> apply_to_thm' (Conv.arg_conv (Conv.rewr_conv eq_th)))

(* Attempt to retrieve property with the given statement from the table. *)
fun get_property ctxt (id, cprop) =
    let
      val ct = Thm.dest_arg cprop
      val t = Thm.term_of ct
      fun head_agrees (_, th) =
          Term.head_of (prop_of' th) aconv Term.head_of (Thm.term_of cprop)

      val property_t =
          if RewriteTable.in_table_raw_for_id ctxt (id, t) then
            (get_property_for_term ctxt t)
                |> filter head_agrees
          else let
            fun process_head_rep (id', eq_th) =
                (get_property_for_term ctxt (Util.rhs_of eq_th))
                    |> filter head_agrees
                    |> map (convert_property ctxt (id', meta_sym eq_th))
          in
            (RewriteTable.subterm_simplify_info ctxt ct)
                |> maps (RewriteTable.get_head_rep_with_id_th ctxt)
                |> maps process_head_rep
          end
    in
      property_t |> BoxID.merge_box_with_info ctxt id
                 |> Util.max_partial (BoxID.info_eq_better ctxt)
    end

fun get_property_t ctxt (id, prop) =
    get_property ctxt (id, Thm.cterm_of ctxt prop)

(* th is an instantiated property update rule (without schematic
   variables). All premises and conclusions of th should be
   properties. Apply this rule at id and below to get new property.
 *)
fun apply_property_update_rule ctxt id th_opt =
    case th_opt of
        NONE => []
      | SOME th =>
        let
          val cprems = map UtilLogic.dest_cTrueprop (Drule.cprems_of th)
        in
          if null cprems then [(id, th)]
          else let
            val p_ths = (map (get_property ctxt) (map (pair id) cprems))
                            |> BoxID.get_all_merges_info ctxt
                            |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
            fun process_p_th (id', ths) = (id', ths MRS th)
          in
            map process_p_th p_ths
          end
        end

(* Find relevant property updates for term t, apply these to get list
   of new properties.
 *)
fun apply_property_update_on_term ctxt id t =
    if fastype_of t = boolT then [] else
    case head_of t of
        Const (c, _) =>
        let
          val thy = Proof_Context.theory_of ctxt
          val updt_rules = Property.lookup_property_update thy c
          fun process_updt_rule th =
              th |> Property.instantiate_property_update ctxt t
                 |> apply_property_update_rule ctxt id
        in
          maps process_updt_rule updt_rules
        end
      | _ => []

(* Work out all consequences of updating the list of properties in the
   rewrite table. This works in a similar manner to process_update_simp. One
   complication is the need to apply property update rules.
 *)
fun process_update_property inits ctxt =
    let
      val thy = Proof_Context.theory_of ctxt

      fun eq_property ((id, th), (id', th')) =
          (id = id' andalso Thm.prop_of th aconv Thm.prop_of th')

      fun process_property (id, th) (to_process, ctxt) =
          let
            val t = Property.get_property_arg (prop_of' th)
            val property_t = get_property_for_term ctxt t
          in
            if exists (fn info => BoxID.info_eq_better ctxt info (id, th)) property_t then
              (to_process, ctxt)
            else
              (insert eq_property (id, th) to_process, add_property_raw (id, th) ctxt)
          end

      fun update_step (to_process, ctxt) =
          case to_process of
              [] => ([], ctxt)
            | (id, th) :: rest =>
              let
                val t = Property.get_property_arg (prop_of' th)

                (* Neighbors of t. Here th: P t, th': t = t', result: P t'. *)
                fun process_neigh (id', eq_th) =
                    convert_property ctxt (id', eq_th) (id, th)
                val new_property_neigh = map process_neigh (RewriteTable.equiv_neighs ctxt t)

                (* Derived properties of t. *)
                val ts = Property.strip_property_field thy t
                val c = Property.get_property_name (prop_of' th)
                val updt_rules = Property.lookup_property_update thy c
                fun process_updt_rule (t, th) =
                    th |> Property.instantiate_property_update ctxt t
                       |> apply_property_update_rule ctxt id
                val new_property_t = maps process_updt_rule
                                          (Util.all_pairs (ts, updt_rules))

                (* Derived properties of parent terms of t. *)
                val parents_t = map (Thm.term_of) (RewriteTable.immediate_contains ctxt t)
                val new_property_ps =
                    maps (apply_property_update_on_term ctxt id) parents_t
              in
                (rest, ctxt) |> fold process_property new_property_neigh
                             |> fold process_property new_property_t
                             |> fold process_property new_property_ps
                             |> update_step
              end
    in
      ([], ctxt) |> fold process_property inits |> update_step |> snd
    end

fun process_rewrite_property (id, th) ctxt =
    let
      val (t1, t2) = (Util.lhs_of th, Util.rhs_of th)

      (* New properties. *)
      val t1_property = get_property_for_term ctxt t1
      val t2_property = get_property_for_term ctxt t2
      val t1_newp = t2_property |> map (convert_property ctxt (id, meta_sym th))
      val t2_newp = t1_property |> map (convert_property ctxt (id, th))
    in
      ctxt |> process_update_property (t1_newp @ t2_newp)
    end

(* First make sure t is in the table. Add property P t to the table,
   and work out any consequences. The result is a consistent rewrite
   table.
 *)
fun add_property (id, th) ctxt =
    let
      val ct = Property.get_property_arg_th th
    in
      ctxt |> RewriteTable.add_term (id, ct) |> snd
           |> process_update_property [(id, th)]
    end

(* Return the list of new properties, as a list of (id, th). *)
fun get_new_property prim_id ctxt =
    let
      val property = Data.get ctxt
    in
      property |> Termtab.dest_list
               |> filter (fn (_, (id, _)) => BoxID.is_eq_ancestor ctxt [prim_id] id)
    end

end  (* structure PropertyData *)
