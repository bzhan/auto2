(* Updating of all data maintained at proof time. *)

type custom_data =
     {add_term_fn: box_id * cterm -> Proof.context -> Proof.context,
      add_rewrite_fn: box_id * thm -> Proof.context -> Proof.context,
      add_fact_fn: box_id * thm -> Proof.context -> Proof.context,
      match_fn: Proof.context -> term -> (box_id * thm) list,
      resolve_fn: Proof.context -> (box_id * thm) list,
      clean_resolved: box_id -> Proof.context -> Proof.context}

signature AUTO2_DATA =
sig
  val add_custom_data: string * custom_data -> theory -> theory
  val invoke_match: term -> Proof.context -> (box_id * thm) list
  val invoke_resolve: Proof.context -> (box_id * thm) list
  val invoke_clean_resolved: box_id -> Proof.context -> Proof.context
  val classify_th: theory -> thm -> string
  val relevant_terms_single: theory -> thm -> cterm list
  val add_terms: (box_id * thm) list -> (box_id * cterm) list ->
                 Proof.context -> Proof.context
  val add_infos: (box_id * thm) list -> box_id * thm list -> Proof.context ->
                 Proof.context
  val get_incr_type:
      Proof.context -> (box_id * thm) list -> box_id * thm list -> incr_context
end;

structure Auto2Data : AUTO2_DATA =
struct

fun join_infos _ (d1, d2) =
    if pointer_eq (d1, d2) then d1 else raise Fail "custom_data: join"

structure Data = Theory_Data
(
  type T = custom_data Symtab.table
  val empty = Symtab.empty
  val extend = I
  val merge = Symtab.join join_infos
)

fun add_custom_data (nm, data) thy =
    Data.map (Symtab.update (nm, data)) thy
(* Use strings normally reserved for ty_str for convenience only. Does
   not indicate the original ty_str of the item.
 *)
fun classify_th thy th =
    if is_eq_term (prop_of' th) then "EQ"
    else if Property.is_property_const thy (prop_of' th) then "PROPERTY"
    else "PROP"

(* Helper function for the two functions below. *)
fun relevant_terms_single thy th =
    if classify_th thy th <> "EQ" then [] else
    let
      val (lhs, rhs) = cdest_eq (cprop_of' th)
    in
      [lhs, rhs]
    end

fun get_custom_data ctxt =
    ctxt |> Proof_Context.theory_of |> Data.get
         |> Symtab.dest |> map snd

fun invoke_add_term (id, ct) ctxt =
    let
      fun invoke1 {add_term_fn, ...} ctxt = add_term_fn (id, ct) ctxt
    in
      ctxt |> fold invoke1 (get_custom_data ctxt)
    end

fun invoke_add_rewrite (id, th) ctxt =
    let
      fun invoke1 {add_rewrite_fn, ...} ctxt = add_rewrite_fn (id, th) ctxt
    in
      ctxt |> fold invoke1 (get_custom_data ctxt)
    end

fun invoke_add_fact (id, th) ctxt =
    let
      fun invoke1 {add_fact_fn, ...} ctxt = add_fact_fn (id, th) ctxt
    in
      ctxt |> fold invoke1 (get_custom_data ctxt)
    end

fun invoke_match t ctxt =
    let
      fun invoke1 {match_fn, ...} = match_fn ctxt t
    in
      maps invoke1 (get_custom_data ctxt)
    end

fun invoke_resolve ctxt =
    let
      fun invoke1 {resolve_fn, ...} = resolve_fn ctxt
    in
      maps invoke1 (get_custom_data ctxt)
    end

fun invoke_clean_resolved id ctxt =
    let
      fun invoke1 {clean_resolved, ...} ctxt = clean_resolved id ctxt
    in
      ctxt |> fold invoke1 (get_custom_data ctxt)
    end

fun add_terms infos term_infos ctxt =
    let
      val ts = map (Thm.term_of o snd) term_infos
      val (edges, ctxt') = RewriteTable.add_term_list term_infos ctxt
      val new_ts = map (Thm.term_of o snd)
                       (RewriteTable.get_new_terms (ctxt, ctxt'))
      val imm_properties =
          maps (PropertyData.apply_property_update_on_term ctxt' []) ts
    in
      ctxt' |> PropertyData.process_update_property imm_properties
            |> fold PropertyData.process_rewrite_property edges
            |> fold WellformData.initialize_wellform_data ts
            |> WellformData.complete_wellform_data_for_terms infos new_ts
            |> fold invoke_add_term term_infos
            |> fold invoke_add_rewrite edges
    end

(* Add the given (id, th) pairs to the rewrite table. Consider three
   cases: where th is an equalitiy, a property, and an ordinary
   theorem.
 *)
fun add_infos infos (id, new_infos) ctxt =
    if exists (fn th => not (is_Trueprop (Thm.prop_of th))) new_infos then
      raise Fail "add_info"
    else let
      val thy = Proof_Context.theory_of ctxt

      val relevant_terms =
          new_infos |> maps (relevant_terms_single thy)
                    |> RewriteTable.get_reachable_terms true ctxt
                    |> map Thm.term_of

      val relevant_props =
          filter (fn (_, th) => classify_th thy th = "PROP")
                 (map (pair id) new_infos) @
          filter (fn (_, th) => Util.has_subterm relevant_terms (prop_of' th)) infos

      fun add_one_info th ctxt =
          case classify_th thy th of
              "EQ" =>
              let
                val (edges, ctxt') = RewriteTable.add_rewrite (id, th) ctxt
              in
                ctxt' |> fold PropertyData.process_rewrite_property edges
                      |> fold invoke_add_rewrite edges
              end
            | "PROPERTY" => PropertyData.add_property (id, th) ctxt
            | _ => invoke_add_fact (id, th) ctxt
    in
      ctxt |> fold add_one_info new_infos
           |> WellformData.complete_wellform_data relevant_props
    end

(* Obtain the incremental context corresponding to the given (id, th)
   pairs. Consider three cases: when th is an equality, a property,
   and an ordinary theorem.
 *)
fun get_incr_type ctxt infos (id, new_infos) =
    if exists (fn th => not (is_Trueprop (Thm.prop_of th))) new_infos then
      raise Fail "get_incr_type"
    else let
      val thy = Proof_Context.theory_of ctxt

      val (prim_id, ctxt') = BoxID.add_prim_id [] ctxt

      val relevant_terms =
          new_infos |> maps (relevant_terms_single thy)
                    |> RewriteTable.get_reachable_terms true ctxt
                    |> map Thm.term_of

      val relevant_props =
          filter (fn (_, th) => classify_th thy th = "PROP")
                 (map (pair [prim_id]) new_infos) @
          filter (fn (_, th) => Util.has_subterm relevant_terms (prop_of' th)) infos

      fun add_one_info th ctxt =
          case classify_th thy th of
              "EQ" =>
              let
                val (edges, ctxt') = RewriteTable.add_rewrite ([prim_id], th) ctxt
              in
                ctxt' |> fold PropertyData.process_rewrite_property edges
                      |> fold invoke_add_rewrite edges
              end
            | "PROPERTY" => PropertyData.add_property ([prim_id], th) ctxt
            | _ => invoke_add_fact (id, th) ctxt

      val ctxt'' = ctxt' |> fold add_one_info new_infos
                         |> WellformData.complete_wellform_data relevant_props

      val new_ts = (maps (relevant_terms_single thy) new_infos @
                    maps (Property.get_property_arg_th_gen o snd o snd)
                         (PropertyData.get_new_property prim_id ctxt'') @
                    map (Thm.cterm_of ctxt o fst)
                        (WellformData.get_new_wellform_data prim_id ctxt''))
                       |> distinct (op aconvc)
    in
      LAST (ctxt'', id, RewriteTable.get_reachable_terms true ctxt new_ts)
    end

end  (* Auto2Data *)
