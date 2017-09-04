(* Unit test for alg_ring.ML. *)

local

val ctxt = @{context}
val G = @{term "G::i"}
val ring_th = Thm.assume @{cprop "is_comm_ring(G)"}
val rat_info = comm_ring_rat_info ring_th
val info = AlgCommRing.comm_ring_alg_data ring_th
val test_wfconv = WfTerm.test_wfconv ctxt (rat_fheads G)

in

val test_rat_add =
    let
      val wfcv = rat_add rat_info
      val test_data = [
        ("plus(G,of_nat(G,1),of_nat(G,1))", "of_nat(G,2)"),
        ("plus(G,of_nat(G,1),neg(G,of_nat(G,1)))", "of_nat(G,0)")
      ]
    in
      map (test_wfconv wfcv "test_rat_add") test_data
    end

val test_rat_inv =
    let
      val wfcv = rat_inv rat_info
      val test_data = [
        ("inv(G,of_nat(G,1))", "of_nat(G,1)")
      ]
    in
      map (test_wfconv wfcv "test_rat_inv") test_data
    end

val test_rat_uminus =
    let
      val wfcv = rat_uminus rat_info
      val test_data = [
        ("neg(G,of_nat(G,1))", "neg(G,of_nat(G,1))"),
        ("neg(G,neg(G,of_nat(G,1)))", "of_nat(G,1)"),
        ("neg(G,divide(G,of_nat(G,1),of_nat(G,2)))",
         "divide(G,neg(G,of_nat(G,1)),of_nat(G,2))"),
        ("neg(G,divide(G,neg(G,of_nat(G,1)),of_nat(G,2)))",
         "divide(G,of_nat(G,1),of_nat(G,2))"),
        ("neg(G,of_nat(G,0))", "of_nat(G,0)")
      ]
    in
      map (test_wfconv wfcv "test_rat_uminus") test_data
    end

val test_rat_minus =
    let
      val wfcv = rat_minus rat_info
      val test_data = [
        ("minus(G,of_nat(G,2),of_nat(G,1))", "of_nat(G,1)"),
        ("minus(G,of_nat(G,1),of_nat(G,2))", "neg(G,of_nat(G,1))")
      ]
    in
      map (test_wfconv wfcv "test_rat_minus") test_data
    end

val test_rat_divide =
    let
      val wfcv = rat_divide rat_info
      val test_data = [
        ("divide(G,of_nat(G,4),of_nat(G,2))", "of_nat(G,2)"),
        ("divide(G,of_nat(G,1),neg(G,of_nat(G,2)))",
         "divide(G,neg(G,of_nat(G,1)),of_nat(G,2))")
      ]
    in
      map (test_wfconv wfcv "test_rat_divide") test_data
    end

fun test_norm_term G (str1, str2) =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val t2' = AlgCommRing.norm_term G t1
    in
      if t2' aconv t2 then ()
      else let
        val _ = trace_t ctxt "Input" t1
        val _ = trace_t ctxt "Expected" t2
        val _ = trace_t ctxt "Actual" t2'
      in
        raise Fail "test_norm_term"
      end
    end

val test_norm =
    let
      val wfcv = AlgCommRing.norm_full info
      val test_data = [
        ("neg(G,a)", "times(G,a,neg(G,of_nat(G,1)))"),
        ("times(G,neg(G,a),neg(G,a))", "times(G,a,a)"),
        ("divide(G,a,of_nat(G,2))",
         "times(G,a,divide(G,of_nat(G,1),of_nat(G,2)))"),
        ("plus(G,divide(G,a,of_nat(G,2)),divide(G,a,of_nat(G,2)))", "a::i"),
        ("inv(G,neg(G,a))", "times(G,inv(G,a),neg(G,of_nat(G,1)))"),
        ("minus(G,plus(G,a,b),a)", "b::i"),
        ("plus(G,of_nat(G,0),a)", "a::i"),
        ("plus(G,a,of_nat(G,0))", "a::i"),
        ("minus(G,of_nat(G,0),of_nat(G,0))", "of_nat(G,0)"),
        ("inv(G,of_nat(G,1))", "of_nat(G,1)"),
        ("times(G,a,inv(G,a))", "of_nat(G,1)"),
        ("times(G,times(G,a,b),inv(G,a))", "b::i"),
        ("inv(G,inv(G,a))", "a::i"),
        ("inv(G,times(G,a,inv(G,a)))", "of_nat(G,1)"),
        ("plus(G,inv(G,a),inv(G,neg(G,a)))", "of_nat(G,0)"),
        ("zero(G)", "of_nat(G,0)"),
        ("plus(G,a,zero(G))", "a::i"),
        ("plus(G,zero(G),a)", "a::i"),
        ("one(G)", "of_nat(G,1)"),
        ("times(G,a,one(G))", "a::i"),
        ("times(G,one(G),a)", "a::i")
      ]

      val _ = map (test_wfconv wfcv "test_norm") test_data
      val _ = map (test_norm_term @{term "G::i"}) test_data
    in
      ()
    end

end  (* local *)
