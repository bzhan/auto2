(* Unit test for acdata.ML. *)

local

  open ACUtil

  val thy = @{theory}
  val thy' = thy |> add_logic_ac_data |> Nat_Arith.add_arith_ac_data
                 |> add_list_ac_data
  val ctxt = @{context}
in

val test_comb_ac_equiv =
    let
      fun err n = "test_comb_ac_equiv: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let
            val ac_info = the (get_head_ac_info thy' t1)
                          handle Option.Option =>
                                 raise AUTO2 "test_comb_ac_equiv: ac_info"
            val ts1 = dest_ac ac_info t1
            val ts2 = dest_ac ac_info t2
            fun eq (t1', t2') =
                Thm.assume (cert_thy thy' (Logic.mk_equals (t1', t2')))
            val eqs = map eq (ts1 ~~ ts2)
            val th = comb_ac_equiv ac_info eqs
          in
            if Thm.prop_of th aconv Logic.mk_equals (t1, t2) then ()
            else raise AUTO2CT (err n, [Thm.cprop_of th])
          end
      val _ = test 0 (@{term "(a::nat) + b + c"}, @{term "(d::nat) + e + f"})
      val _ = test 1 (@{term "A | B | C | D"}, @{term "E | F | G | H"})
    in () end

(* Generic function for testing conv with ac_info argument. *)
fun test_ac_conv_gen with_inv ctxt cv err_str (str1, str2) =
    let
      val t1 = Proof_Context.read_term_pattern ctxt str1
      val ac_info = the (get_head_ac_info_gen with_inv thy' t1)
                    handle Option.Option => raise AUTO2 "test_ac_conv: ac_info"
    in
      test_conv ctxt (cv ac_info) err_str (str1, str2)
    end

val test_ac_conv = test_ac_conv_gen false
val test_ac_conv_with_inv = test_ac_conv_gen true

val test_normalize_cu =
    let
      val test_data = [
        ("(a::nat) + e + c + b + d", "(a::nat) + b + c + d + e"),
        ("(a::nat) + c * b + gcd e f + g", "(a::nat) + g + gcd e f + c * b"),
        ("A | C | D | B", "A | B | C | D"),
        ("(B | A) | C", "C | (B | A)"),
        ("(0::nat) + e + b + c + 0", "(b::nat) + c + e"),
        ("(1::nat) * a * b * c * d * 1", "(a::nat) * b * c * d"),
        ("(1::nat) * a * b * c * d", "(a::nat) * b * c * d"),
        ("True & A & C & B & True", "A & B & C")
      ]
    in
      map (test_ac_conv ctxt normalize_cu "test_normalize_cu") test_data
    end

val test_normalize_assoc =
    let
      val test_data = [
        ("(a::nat) + (b + d) + (c + e)", "(a::nat) + b + d + c + e"),
        ("A & (B & D) & (C & E)", "A & B & D & C & E"),
        ("((a::nat) + 0) + (b + 0)", "(a::nat) + 0 + b + 0")
      ]
    in
      map (test_ac_conv ctxt normalize_assoc "test_normalize_assoc") test_data
    end

val test_normalize_minus =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [@{term "a::int"}]
      val test_data = [
        ("-a", "-a"),
        ("-0::int", "0::int"),
        ("a + b", "a + b"),
        ("-(a + b)", "(-a) + (-b)"),
        ("-(-a)", "a"),
        ("-(a + (-b))", "(-a) + b"),
        ("-(-a + b)", "a + (-b)"),
        ("a - b", "a + (-b)"),
        ("a - 0", "a + 0"),
        ("a - b - c", "a + (-b) + (-c)"),
        ("a - b - c + d - e", "a + (-b) + (-c) + d + (-e)"),
        ("a - (b + c)", "a + (-b + (-c))"),
        ("a - (b - c)", "a + (-b + c)"),
        ("a - (-b + c)", "a + (b + (-c))"),
        ("a - (-b - c)", "a + (b + c)"),
        ("(a - b) - (c - d)", "(a + (-b)) + (-c + d)")
      ]
    in
      map (test_ac_conv_with_inv ctxt' normalize_minus "test_normalize_minus")
          test_data
    end

val test_normalize_minus_full =
    let
      val ctxt' = ctxt |> fold Variable.declare_term [@{term "r::rat"}]
      val test_data = [
        ("-r", "-r"),
        ("r - s", "r + (-s)"),
        ("- (r - s)", "-r + s"),
        ("r / s", "r * inverse s"),
        ("r / s - u / v", "r * inverse s + (-(u * inverse v))")
      ]
    in
      map (test_conv ctxt' (normalize_minus_full thy')
                     "test_normalize_minus_full") test_data
    end

val test_move_outmost =
    let
      val err_str = "test_move_outmost"
      fun test (stru, (str1, str2)) =
          let
            val t1 = Proof_Context.read_term_pattern ctxt str1
            val u = Proof_Context.read_term_pattern ctxt stru
            val ac_info =
                the (get_head_ac_info thy' t1)
                handle Option.Option => raise AUTO2 (err_str ^ ": ac_info")
          in
            test_conv ctxt (move_outmost ac_info u) err_str (str1, str2)
          end
      val test_data = [
        ("a::nat", ("(a::nat) + b", "(b::nat) + a")),
        ("a::nat", ("(a::nat) + b + c", "(b::nat) + c + a")),
        ("a::nat", ("(b::nat) + a", "(b::nat) + a")),
        ("a::nat", ("(b::nat) + a + c", "(b::nat) + c + a")),
        ("A::bool", ("A & B & C", "A & B & C")),
        ("A::bool", ("C & B & A", "A & C & B"))
      ]
    in
      map test test_data
    end

fun default_matcher (id, env) (t, u) =
    case ACUtil.get_head_ac_info_with_inv thy' t of
        NONE =>
        ([((id, Pattern.match thy (t, u) env), Thm.reflexive (cert ctxt u))]
         handle Pattern.MATCH => [])
      | SOME ac_info =>
        match_ac thy ac_info default_matcher (id, env) (t, (u, []))

fun assert_eq_info (insts_t, exp_insts_t) =
    if eq_set (op aconv) (insts_t, exp_insts_t) then true
    else let
      val _ = trace_tlist_ctxt ctxt "Expected:" exp_insts_t
      val _ = trace_tlist_ctxt ctxt "Actual:" insts_t
    in
      false
    end

(* Check th is actually t(env) == u. *)
fun check_info (t, u) ((_, inst), th) =
    let
      val t' = subst_term_norm inst t
      val (lhs, rhs) = Logic.dest_equals (Thm.prop_of th)
    in
      if lhs aconv t' andalso rhs aconv u then true
      else let
        val _ = tracing "th is not t(env) == u"
        val _ = trace_thm_ctxt ctxt "th:" th
        val _ = trace_t_ctxt ctxt "t(env):" t'
      in
        false
      end
    end

val test_match_ac =
    let
      fun test ctxt (t_str, u_str, exp_insts_t_strs) =
          let
            val t = Proof_Context.read_term_pattern ctxt t_str
            val u = Syntax.read_term ctxt u_str
            val exp_insts_t = map (Syntax.read_term ctxt) exp_insts_t_strs
            val ac_info = the (get_head_ac_info_with_inv thy' t)
                          handle Option.Option =>
                                 raise AUTO2 "test_ac_conv: ac_info"
            val insts = match_ac thy ac_info default_matcher ([], fo_init)
                                 (t, (u, []))
            val insts_t = map (fn ((_, _), th) => lhs_of th) insts
          in
            if forall (check_info (t, u)) insts andalso
               assert_eq_info (insts_t, exp_insts_t) then ()
            else let
              val _ = trace_t_ctxt ctxt "t:" t
              val _ = trace_t_ctxt ctxt "u:" u
            in
              raise AUTO2 "test_match_ac"
            end
          end

      (* m, n, p reserved for natural numbers. L, M, N, etc reserved
         for lists, and r, s, t reserved for rationals.
       *)
      val ctxt' = ctxt |> fold Variable.declare_term [
            Var (("m", 0), natT), Free ("m", natT),
            @{term_pat "?L::nat list"}, @{term "L::nat list"},
            @{term_pat "?r::rat"}, @{term "r::rat"}
          ]

      val test_data_nat = [
        ("?m + ?n", "m + n", ["m + n", "n + m"]),
        ("?m + n", "m + n", ["m + n"]),
        ("?n + m", "m + n", ["n + m"]),
        ("?m + n", "m + n + p", ["(m + p) + n"]),
        ("n + ?m", "m + n + p", ["n + (m + p)"]),
        ("?m * ?n", "m * n", ["m * n", "n * m"])
      ]
      val _ = map (test ctxt') test_data_nat

      val test_data_list = [
        ("?L @ ?M", "L @ M", ["L @ M"]),
        ("?L @ M @ ?N", "L @ M @ N", ["L @ M @ N"]),
        ("?L @ M @ ?N", "L @ M @ M @ N", ["L @ M @ (M @ N)", "(L @ M) @ M @ N"])
      ]
      val _ = map (test ctxt') test_data_list

      val test_data_rat = [
        ("?r + ?s", "r + s", ["r + s", "s + r"]),
        ("?r + ?s", "r + (-s)", ["r + (-s)", "(-s) + r"]),
        ("?r + (-?s)", "r + (-s)", ["r + (-s)"]),
        ("-?r", "-r", ["-r"]),
        ("?r - ?s", "r + (-s)", ["r - s"]),
        ("?r - ?r", "r + (-r)", ["r - r"]),
        ("?r + ?s - ?s", "r + s + (-s)", ["r + s - s"]),
        ("?r + ?s - ?s", "r + s + t + (-s)", ["r + t + s - s"]),
        ("?r - ?s", "(-r) + (-s)", ["-r - s", "-s - r"]),
        ("?r / ?s", "r * inverse s", ["r / s"]),
        ("1 / ?r", "inverse r", ["1 / r"]),
        ("?r / 2", "r * inverse 2", ["r / 2"]),
        ("?r / 2 + ?r / 2", "r * inverse 2 + r * inverse 2", ["r / 2 + r / 2"]),
        ("?r * ?s / ?r", "r * s * inverse r", ["r * s / r"]),
        ("-?r", "r + (-s)", ["-(s + (-r))"]),
        ("-?r", "r + s", []),
        ("?r - ?s", "r + s + (-t)", ["r + s - t", "r - (t + -s)",
                                     "s - (t + -r)"]),
        ("?r + -?s", "r + s + (-t)", ["r + s + -t", "r + -(t + -s)",
                                      "s + -(t + -r)"]),
        ("?r - ?r", "r + s + (-r) + (-s)",
         ["r + s - (r + s)", "r + -s - (r + -s)", "s + -r - (s + -r)"])
      ]
      val _ = map (test ctxt') test_data_rat
    in
      ()
    end

end;  (* local *)
