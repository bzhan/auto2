local

  open Nat_Order

  (* Set up rewrite table and rtype. *)
  val x = @{term "x::nat"}
  val x' = @{term "x'::nat"}
  val y = @{term "y::nat"}
  val y' = @{term "y'::nat"}
  val z = @{term "z::nat"}
  val w = @{term "w::nat"}
  val px = @{term_pat "?x::nat"}
  val py = @{term_pat "?y::nat"}
  val ctxt = @{context}
                  |> fold Variable.declare_term [x, x', y, y', z, w, px, py]

  val tbl = RewriteTable.empty ctxt |> RewriteTable.add_rewrite [] (x, x')
  val rtype = RewriteTable.SINGLE tbl
  val st = Status.empty_status ctxt

  (* Read strings as terms in ctxt'. *)
  fun read_as_term t = t |> Proof_Context.read_term_pattern ctxt
in

fun convert_prop_to_nat_order prop =
    let
      val ritem = Fact ("PROP", [prop], prop |> HOLogic.mk_Trueprop
                                             |> assume_thm ctxt)
      val item = mk_box_item ([], 0, ritem)

      fun apply_prfsteps item =
          maps (fn {func, ...} => func [item] rtype st) to_nat_order_prfsteps

      fun process_raw_item ritem =
          case ritem of
              Fact ("NAT_ORDER", tname, _) =>
              let val (x, y, diff_t) = the_triple tname in
                (x, y, dest_numc diff_t)
              end
            | _ => raise AUTO2 "convert_prop_to_nat_order: unexpected ritem."

      fun process_raw_update updt =
          case updt of
              Update.AddItems {raw_items, ...} => map process_raw_item raw_items
            | _ => raise AUTO2 "convert_prop_to_nat_order: unexpected update."
    in
      maps process_raw_update (apply_prfsteps item)
    end

val test_parse_prop =
    let
      fun string_of_spec (x, y, diff) =
          "(" ^ ([x, y, Nat_Arith.mk_nat diff]
                     |> pretty_terms ctxt |> str) ^ ")"
      fun eq_specs ((x1, y1, diff1), (x2, y2, diff2)) =
          x1 aconv x2 andalso y1 aconv y2 andalso diff1 = diff2

      fun test (prop_str, specs_str) =
          let
            val prop = read_as_term prop_str
            fun read_spec (x_str, y_str, diff) =
                (read_as_term x_str, read_as_term y_str, diff)
            val specs = map read_spec specs_str
            val specs' = convert_prop_to_nat_order prop
          in
            if eq_set eq_specs (specs, specs') then ()
            else let
              val _ = tracing ("Expected:" ^
                               (string_of_list string_of_spec specs))
              val _ = tracing ("Actual:" ^
                               (string_of_list string_of_spec specs'))
            in
              raise AUTO2 "test_parse_prop"
            end
          end

      val test_data = [
        ("x <= y", [("x", "y", 0)]),
        ("x + 1 <= y", [("x", "y", ~1)]),
        ("x - 1 <= y", [("x", "y", 1), ("x-1", "y", 0)]),
        ("x <= y + 1", [("x", "y", 1)]),
        ("x <= y - 1", [("x", "y", 0), ("x", "y-1", 0)]),  (* special case *)
        ("x < y", [("x", "y", ~1)]),
        ("x + 1 < y", [("x", "y", ~2)]),
        ("x - 1 < y", [("x", "y", 0), ("x-1", "y", ~1)]),
        ("x < y + 1", [("x", "y", 0)]),
        ("x < y - 1", [("x", "y", ~2), ("x", "y-1", ~1)]),
        ("x <= 3", [("x", "0::nat", 3)]),
        ("x < 3", [("x", "0::nat", 2)]),
        ("x <= 0", [("x", "0::nat", 0)]),
        ("x < 0", [("x", "0::nat", ~1)]),
        ("x >= 3", [("0::nat", "x", ~3)]),
        ("x > 3", [("0::nat", "x", ~4)]),
        ("x >= 0", [("0::nat", "x", 0)]),
        ("x > 0", [("0::nat", "x", ~1)]),
        ("x + 1 <= 3", [("x", "0::nat", 2)]),
        ("x - 1 <= 3", [("x", "0::nat", 4), ("x-1", "0::nat", 3)])
      ]
      val _ = map test test_data
    in
      ()
    end

val test_nat_order_match_side =
    let
      fun test (pat_str, x_str, res_strs) =
          let
            val pat = read_as_term pat_str
            val x = read_as_term x_str
            val res = map read_as_term res_strs
            val res' = nat_order_match_side pat x tbl ([], fo_init)
            fun check_inst ((_, inst), _, eq_th) =
                (Envir.subst_term inst pat) aconv (lhs_of eq_th)
            fun eq_th_of (_, _, eq_th) = eq_th
            val check_res =
                eq_list (op aconv) (res, map (rhs_of o eq_th_of) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist_ctxt ctxt "pat, x:" [pat, x]
              val _ = trace_tlist_ctxt ctxt "Expected:" res
              val _ = trace_tlist_ctxt ctxt "Actual:"
                                       (map (Thm.prop_of o eq_th_of) res')
            in
              raise AUTO2 "test_nat_order_match_side"
            end
          end

      val test_data = [
        ("?x", "x", ["x"]),
        ("?x + 1", "x", ["x + 1"]),
        ("1 + ?x", "x", ["x + 1"]),
        ("?x - 1", "x", ["x - 1"]),
        ("min ?a ?b + 1", "min x y", ["min x y + 1"]),
        ("3::nat", "0::nat", ["(0::nat) + 3"]),
        ("0::nat", "0::nat", ["0::nat"]),
        ("?x", "0::nat", []),
        ("min ?a ?b", "0::nat", [])
      ]
      val _ = map test test_data
    in
      ()
    end

val test_nat_order_match =
    let
      fun test (pat_str, prop_str, res_strs) =
          let
            val pat = read_as_term pat_str |> HOLogic.mk_Trueprop
            val prop = read_as_term prop_str
            val order_specs = convert_prop_to_nat_order prop
            val (x, y, diff) =
                the_single order_specs
                handle List.Empty =>
                       raise AUTO2 "test_nat_order_match: ambiguous prop"
            val ritem = get_nat_order_ritem (
                  x, y, diff, assume_thm ctxt (order_info_to_prop (x, y, diff)))
            val item = mk_box_item ([], 0, ritem)
            val res = map (HOLogic.mk_Trueprop o read_as_term) res_strs
            val res' = nat_order_match pat item tbl ([], fo_init)
            fun check_inst ((_, inst), th) =
                (Envir.subst_term inst pat) aconv (Thm.prop_of th)
            val check_res =
                eq_list (op aconv) (res, map (Thm.prop_of o snd) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist_ctxt ctxt "pat, prop:" [pat, prop]
              val _ = trace_tlist_ctxt ctxt "Expected:" res
              val _ = trace_tlist_ctxt ctxt "Actual:"
                                       (map (Thm.prop_of o snd) res')
            in
              raise AUTO2 "test_nat_order_match"
            end
          end

      val test_data = [
        ("x <= y", "x <= y", ["x <= y"]),
        ("x < y", "x <= y", []),
        ("x < y", "x < y", ["x < y"]),
        ("x <= y", "x < y", ["x <= y"]),
        ("x <= y", "x' <= y", ["x <= y"]),
        ("x' <= y", "x <= y", ["x' <= y"]),
        ("x + 1 <= y", "x <= y", []),
        ("x - 1 <= y", "x <= y", ["x - 1 <= y"]),
        ("x <= y + 1", "x <= y", ["x <= y + 1"]),
        ("min ?a ?b <= z", "min x y <= z", ["min x y <= z"]),
        ("min ?a ?b + 1 <= z", "min x y <= z", []),
        ("min ?a ?b - 1 <= z", "min x y <= z", ["min x y - 1 <= z"]),
        ("min ?a ?b <= z + 1", "min x y <= z", ["min x y <= z + 1"]),
        ("?x <= y", "x < y", ["x <= y"]),
        ("?x <= ?y", "x < y", ["x <= y"]),
        ("?x < ?y + 1", "x < y", ["x < y + 1"]),
        ("?x < ?y - 1", "x + 1 < y", ["x < y - 1"]),
        ("0 < ?x", "x > 3", ["0 < x"]),
        ("0 < ?x", "x >= 0", []),
        ("0 <= ?x", "x >= 0", ["0 <= x"]),
        ("?x <= 0", "x < 1", ["x <= 0"]),
        ("?x <= 0", "x < 2", []),
        ("~ x < y", "x >= y", ["~ x < y"]),
        ("~ x < 3", "x > 3", ["~ x < 3"]),
        ("~ ?x < ?y", "x >= y", ["~ x < y"]),
        ("~ x <= y", "x > y", ["~ x <= y"]),
        ("~ min (?a::nat) ?b <= min ?c ?d", "min x y < min z w",
         ["~ min z w <= min x y"])
      ]
      val _ = map test test_data
    in
      ()
    end

val test_single_resolve_match =
    let
      fun test t_str =
          let
            val th = t_str |> read_as_term |> HOLogic.mk_Trueprop
                           |> assume_thm ctxt
            val res = single_resolve_match [] rtype th
          in
            if length res = 1 andalso
               res |> the_single |> snd |> Thm.prop_of aconv prop_False then ()
            else let
              val _ = trace_t_ctxt ctxt "Input:" (Thm.prop_of th)
              val _ = trace_tlist_ctxt
                          ctxt "Output:" (map (Thm.prop_of o snd) res)
            in
              raise AUTO2 "test_single_resolve_match"
            end
          end

      val test_data = ["x < x", "x + 1 <= x", "x < x'", "x + 1 <= x'",
                       "x' + 1 <= x", "x < x - 1", "x < x' - 1", "x' < x - 1",
                       "~ x <= x", "~ x >= x", "(3::nat) <= 2", "(3::nat) < 3",
                       "~ (3::nat) >= 3", "~ (3::nat) > 2"]
      val _ = map test test_data
    in
      ()
    end

end
