(* Unit test for subterms.ML *)

local

  open Subterms

  val thy = @{theory}
  val thy' = thy |> Nat_Arith.add_arith_ac_data
  val ctxt' = Proof_Context.init_global thy'
in

val test_dest_subterms =
    let
      val ctxt'' = ctxt' |> fold Variable.auto_fixes [
            @{term "[a::nat, b, c]"}, @{term "[A::bool, B, C, D]"}]

      fun test (str, str', subs_str) =
          let
            val t = read_term ctxt'' str
            val t' = read_pat ctxt'' str'
            val subs = map (read_term ctxt'') subs_str
            val (t'', subs') = dest_subterms t
          in
            if t' aconv t'' andalso eq_list (op aconv) (subs, subs') then ()
            else
              raise AUTO2CT ("test_dest_subterms",
                             map (cert_thy thy') (t'' :: subs'))
          end

      val test_data = [
        ("a", "a", []),
        ("a dvd b", "(?SUB::nat) dvd ?SUB1", ["a", "b"]),
        ("a * (b * c)", "(?SUB::nat) * ?SUB1", ["a", "b * c"]),
        ("(a + b) * c", "(?SUB::nat) * ?SUB1", ["a + b", "c"]),
        ("ALL a. b dvd a", "ALL (a::nat). ?SUB dvd a", ["b"]),
        ("ALL A. A & B & C", "ALL A. A & ?SUB", ["B & C"]),
        ("ALL B. A & B & C", "ALL B. ?SUB & B & ?SUB1", ["A", "C"]),
        ("ALL C. A & B & C", "ALL C. ?SUB & ?SUB1 & C", ["A", "B"]),
        ("ALL A. (A & B) & C", "ALL A. (A & ?SUB) & ?SUB1", ["B", "C"]),
        ("ALL (A::bool). (B & C) & D", "ALL (A::bool). ?SUB", ["(B & C) & D"]),
        ("ALL A. C & (ALL B. A & B & D)", "ALL A. ?SUB & (!B. A & B & ?SUB1)",
         ["C", "D"]),
        ("~ (A | B)", "~ ?SUB", ["A | B"])
      ]
    in
      map test test_data
    end

val test_get_all_subterms =
    let
      val ctxt'' = ctxt' |> Variable.auto_fixes @{term "[a::nat, b, c]"}

      fun test (str, subs_str) =
          let
            val t = read_term ctxt'' str
            val subs = map (read_term ctxt'') subs_str
            val subs' = get_all_subterms t
          in
            if eq_list (op aconv) (subs, subs') then ()
            else raise AUTO2CT ("test_get_all_subterms",
                                map (cert_thy thy') subs')
          end

      val test_data = [
        ("a * (b * c)", ["a * (b * c)", "a", "b * c", "b", "c"])
      ]
    in
      map test test_data
    end

val test_build_equiv =
    let
      fun test_raw (t, equivs) =
          let
            val eq_th = build_equiv ctxt' equivs t
            val lsubs = map lhs_of equivs
            val rsubs = map rhs_of equivs
          in
            if lhs_of eq_th aconv (subst_subterms (t, lsubs)) andalso
               rhs_of eq_th aconv (subst_subterms (t, rsubs)) then ()
            else
              raise AUTO2CT ("test_build_equiv", [Thm.cprop_of eq_th])
          end

      val ctxt'' = ctxt' |> Variable.auto_fixes @{term "[a::nat, b, c]"}
      fun test (str, equivs_str) =
          let
            val t = read_pat ctxt'' str
            val equivs = map (Thm.assume o cert ctxt'' o read_term ctxt'')
                             equivs_str
          in
            test_raw (t, equivs)
          end

      (* Name conflict in abs. *)
      val dvd = Const ("Rings.dvd_class.dvd", @{typ "nat => nat => bool"})
      val trm = Abs ("x", natT, Abs ("x", natT, dvd $ (Bound 0) $ (Bound 1)))
      val _ = test_raw (trm, [])

      (* Other tests. *)
      val test_data = [
        ("(?SUB::nat) * ?SUB1", ["a == b", "c == d"]),
        ("ALL a. a + (?SUB::nat) = 0", ["b == c"]),
        ("ALL a. a + (?SUB::nat) = 0", ["b == b"]),
        ("ALL a. a + (?SUB::nat) = 0", ["a == a"])
      ]
    in
      map test test_data
    end

end;  (* local *)
