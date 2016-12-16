(* Unit test for order.ML. *)

local

  open Nat_Order
  val ctxt = @{context}
  val thy = @{theory}

  (* Set up rewrite table and rtype. *)
  val x = Free ("x", natT)
  val x' = Free ("x'", natT)
  val y = Free ("y", natT)
  val y' = Free ("y'", natT)
  val z = Free ("z", natT)
  val w = Free ("w", natT)
  val px = Var (("x", 0), natT)
  val py = Var (("y", 0), natT)
  val ctxt' = ctxt |> fold Variable.declare_term [x, x', y, y', z, w, px, py]

  val tbl = (RewriteTable.empty ctxt')
                |> RewriteTable.add_rewrite [] (assume_eq thy (x, x'))
  val rtype = SINGLE tbl
  val st = Status.empty_status ctxt'

  (* Read strings as terms in ctxt'. *)
  val read_as_term = read_pat ctxt'
in

(* Convert proposition to nat_order item, by applying one of the
   proofsteps in to_nat_order_prfsteps.
 *)
fun convert_prop_to_nat_order prop =
    let
      val err_str = "convert_prop_to_nat_order: "
      val th = prop |> mk_Trueprop |> assume_thm ctxt'
      val item = BoxItem.mk_box_item (0, [], 0, Fact ("PROP", [prop], th))

      fun apply_prfsteps item =
          maps (apply_prfstep rtype st [item]) to_nat_order_prfsteps

      fun process_raw_update updt =
          case updt of
              AddItems {raw_items, ...} =>
              map (fn ritem => BoxItem.mk_box_item (0, [], 0, ritem)) raw_items
            | _ => raise AUTO2 (err_str ^ "unexpected update.")
    in
      maps process_raw_update (apply_prfsteps item)
    end

val test_parse_prop =
    let
      fun string_of_spec (x, y, diff) =
          "(" ^ ([x, y, mk_nat diff] |> pretty_terms ctxt' |> str) ^ ")"

      fun item_to_spec item =
          let val (x, y, n, _) = get_nat_order_info item in (x, y, n) end

      fun eq_specs ((x1, y1, diff1), (x2, y2, diff2)) =
          x1 aconv x2 andalso y1 aconv y2 andalso diff1 = diff2

      fun test (prop_str, specs_str) =
          let
            val prop = read_as_term prop_str
            fun read_spec (x_str, y_str, diff) =
                (read_as_term x_str, read_as_term y_str, diff)
            val specs = map read_spec specs_str
            val specs' = convert_prop_to_nat_order prop |> map item_to_spec
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
                (subst_term_norm inst pat) aconv (lhs_of eq_th)
            fun eq_th_of (_, _, eq_th) = eq_th
            val check_res =
                eq_list (op aconv) (res, map (rhs_of o eq_th_of) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist_ctxt ctxt' "pat, x:" [pat, x]
              val _ = trace_tlist_ctxt ctxt' "Expected:" res
              val _ = trace_tlist_ctxt ctxt' "Actual:"
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
      fun test match_fn (pat_str, prop_str, res_strs) =
          let
            val pat = read_as_term pat_str
            val prop = read_as_term prop_str
            val items = convert_prop_to_nat_order prop
            val item = the_single items
                       handle List.Empty => raise AUTO2 "ambiguous input"
            val res = map (mk_Trueprop o read_as_term) res_strs
            val res' = match_fn pat item tbl ([], fo_init)
            fun check_inst ((_, inst), th) =
                (subst_term_norm inst pat) aconv (prop_of' th)
            val check_res =
                eq_list (op aconv) (res, map (Thm.prop_of o snd) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist_ctxt ctxt' "pat, prop:" [pat, prop]
              val _ = trace_tlist_ctxt ctxt' "Expected:" res
              val _ = trace_tlist_ctxt ctxt' "Actual:"
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
      val _ = map (test nat_order_match) test_data

      val test_noteq_data = [
        ("x ~= y", "x < y", ["x ~= y"]),
        ("x ~= y", "y < x", ["x ~= y"]),
        ("x ~= y", "x <= y", []),
        ("x ~= y", "y <= x", []),
        ("x ~= 0", "x > 0", ["x ~= 0"]),
        ("x ~= 0", "x > 3", ["x ~= 0"]),
        ("?a ~= y", "x < y", [])
      ]
      val _ = map (test (#match nat_order_noteq_matcher)) test_noteq_data
    in
      ()
    end

val test_nat_order_single_match =
    let
      fun test ineq_str =
          let
            val ineq = ineq_str |> read_as_term
            val res = nat_order_single_match
                          ineq BoxItem.null_item tbl ([], fo_init)
          in
            if length res = 1 andalso
               res |> the_single |> snd |> prop_of' aconv ineq then ()
            else let
              val _ = trace_t_ctxt ctxt' "ineq:" ineq
              val _ = trace_tlist_ctxt ctxt' "Output:"
                                       (map (Thm.prop_of o snd) res)
            in
              raise AUTO2 "test_nat_order_single_match"
            end
          end

      val test_data = [
        "x >= x", "x + 1 > x", "x >= x'", "x + 1 > x'", "x' + 1 > x",
        "x >= x - 1", "x >= x' - 1", "x' >= x - 1",
        "~ x > x", "~ x < x", "(3::nat) < 4", "(3::nat) <= 3"
      ]

      val _ = map test test_data
    in
      ()
    end

end
