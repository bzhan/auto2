(* Unit test for order.ML. *)

local

  val ctxt = @{context}
  val thy = @{theory}

  (* Set up rewrite table and incremental context. *)
  val x = Free ("x", natT)
  val x' = Free ("x'", natT)
  val y = Free ("y", natT)
  val y' = Free ("y'", natT)
  val z = Free ("z", natT)
  val w = Free ("w", natT)
  val px = Var (("x", 0), natT)
  val py = Var (("y", 0), natT)
  val ctxt' = ctxt |> fold Variable.declare_term [x, x', y, y', z, w, px, py]
                   |> RewriteTable.add_rewrite ([], assume_eq thy (x, x')) |> snd
  val ictxt = SINGLE ctxt'
in

(* Convert proposition to nat_order item, by applying one of the
   proofsteps in to_nat_order_prfsteps.
 *)
fun convert_prop_to_nat_order prop =
    let
      val th = prop |> mk_Trueprop |> Util.assume_thm ctxt'
      val mk_box_item = BoxItem.mk_box_item ctxt'
      val item = mk_box_item (0, [], 0, Fact (TY_PROP, [prop], th))

      fun apply_prfsteps item =
          maps (ProofStep.apply_prfstep ictxt [item]) Nat_Order.to_nat_order_prfsteps

      fun process_raw_update updt =
          case updt of
              AddItems {raw_items, ...} =>
              map (fn ritem => mk_box_item (0, [], 0, ritem)) raw_items
            | _ => []
    in
      maps process_raw_update (apply_prfsteps item)
    end

val test_parse_prop =
    let
      fun string_of_spec (x, y, diff) =
          "(" ^ (Util.string_of_terms ctxt [x, y, mk_nat diff]) ^ ")"

      fun item_to_spec item =
          let
            val (cx, cy, n, _) = Nat_Order.get_nat_order_info item
          in
            (Thm.term_of cx, Thm.term_of cy, n)
          end

      fun eq_specs ((x1, y1, diff1), (x2, y2, diff2)) =
          x1 aconv x2 andalso y1 aconv y2 andalso diff1 = diff2

      fun test (prop_str, specs_str) =
          let
            val prop = Syntax.read_term ctxt' prop_str
            fun read_spec (x_str, y_str, diff) =
                (Syntax.read_term ctxt' x_str,
                 Syntax.read_term ctxt' y_str, diff)
            val specs = map read_spec specs_str
            val specs' = convert_prop_to_nat_order prop |> map item_to_spec
          in
            if eq_set eq_specs (specs, specs') then ()
            else let
              val _ = tracing (
                    "Expected:" ^ (Util.string_of_list string_of_spec specs) ^ "\n" ^
                    "Actual:" ^ (Util.string_of_list string_of_spec specs'))
            in
              raise Fail "test_parse_prop"
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
            val pat = Proof_Context.read_term_pattern ctxt' pat_str
            val cx = Thm.cterm_of ctxt' (Syntax.read_term ctxt' x_str)
            val res = Syntax.read_terms ctxt' res_strs
            val res' = Nat_Order.nat_order_match_side ctxt' (pat, cx) ([], fo_init)
            fun check_inst ((_, inst), _, eq_th) =
                (Util.subst_term_norm inst pat) aconv (Util.lhs_of eq_th)
            fun eq_th_of (_, _, eq_th) = eq_th
            val check_res =
                eq_list (op aconv) (res, map (Util.rhs_of o eq_th_of) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist ctxt' "pat, x:" [pat, x]
              val _ = trace_tlist ctxt' "Expected:" res
              val _ = trace_tlist ctxt' "Actual:"
                                       (map (Thm.prop_of o eq_th_of) res')
            in
              raise Fail "test_nat_order_match_side"
            end
          end

      val test_data = [
        ("?x", "x", ["x"]),
        ("?x + 1", "x", ["x + 1"]),
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
            val pat = Proof_Context.read_term_pattern ctxt' pat_str
            val prop = Syntax.read_term ctxt' prop_str
            val items = convert_prop_to_nat_order prop
            val item = the_single items
                       handle List.Empty => raise Fail "ambiguous input"
            val res = map (mk_Trueprop o Syntax.read_term ctxt') res_strs
            val res' = match_fn pat item ctxt' ([], fo_init)
            fun check_inst ((_, inst), th) =
                (Util.subst_term_norm inst pat) aconv (prop_of' th)
            val check_res =
                eq_list (op aconv) (res, map (Thm.prop_of o snd) res')
          in
            if forall check_inst res' andalso check_res then ()
            else let
              val _ = trace_tlist ctxt' "pat, prop:" [pat, prop]
              val _ = trace_tlist ctxt' "Expected:" res
              val _ = trace_tlist ctxt' "Actual:" (map (Thm.prop_of o snd) res')
            in
              raise Fail "test_nat_order_match"
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
      val _ = map (test Nat_Order.nat_order_match) test_data

      val test_noteq_data = [
        ("x ~= y", "x < y", ["x ~= y"]),
        ("x ~= y", "y < x", ["x ~= y"]),
        ("x ~= y", "x <= y", []),
        ("x ~= y", "y <= x", []),
        ("x ~= 0", "x > 0", ["x ~= 0"]),
        ("x ~= 0", "x > 3", ["x ~= 0"]),
        ("?a ~= y", "x < y", [])
      ]
      val _ = map (test (#match Nat_Order.nat_order_noteq_matcher)) test_noteq_data
    in
      ()
    end

val test_nat_order_single_match =
    let
      fun test ineq_str =
          let
            val ineq = Syntax.read_term ctxt' ineq_str
            val res = Nat_Order.nat_order_single_match
                          ineq BoxItem.null_item ctxt' ([], fo_init)
          in
            if length res = 1 andalso
               res |> the_single |> snd |> prop_of' aconv ineq then ()
            else let
              val _ = trace_t ctxt' "ineq:" ineq
              val _ = trace_tlist ctxt' "Output:"
                                       (map (Thm.prop_of o snd) res)
            in
              raise Fail "test_nat_order_single_match"
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
