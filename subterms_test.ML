(* Unit test for subterms.ML *)

local

  open Subterms

  val thy = @{theory}
  val thy' = thy |> add_logic_ac_data |> Nat_Arith.add_arith_ac_data
  val ctxt' = Proof_Context.init_global thy'

  val a = @{term "a::nat"}
  val b = @{term "b::nat"}
  val c = @{term "c::nat"}
  val A = @{term "A::bool"}
  val B = @{term "B::bool"}
  val C = @{term "C::bool"}
  val D = @{term "D::bool"}
in

val test_dest_subterms =
    let
      fun err n = "test_dest_subterms: " ^ (string_of_int n)
      fun test n (t, t', subs) =
          let
            val (t'', subs') = dest_subterms thy' true t
          in
            if t' aconv t'' andalso eq_list (op aconv) (subs, subs') then ()
            else raise AUTO2CT (err n, map (cert_thy thy') (t'' :: subs'))
          end
      val _ = test 0 (a, a, [])
      val _ = test 1 (@{term "(a::nat) dvd b"},
                      @{term_pat "(?SUB::nat) dvd ?SUB1"}, [a, b])
      val _ = test 2 (@{term "(a::nat) * b * c"},
                      @{term_pat "(?SUB::nat) * ?SUB1 * ?SUB2"}, [a, b, c])
      val _ = test 3 (@{term "(a::nat) * (b * c)"},
                      @{term_pat "(?SUB::nat) * ?SUB1"},
                      [a, @{term "(b::nat) * c"}])
      val _ = test 4 (@{term "((a::nat) + b) * c"},
                      @{term_pat "(?SUB::nat) * ?SUB1"},
                      [@{term "(a::nat) + b"}, c])
      val _ = test 5 (@{term "!(a::nat). b dvd a"},
                      @{term_pat "!(a::nat). ?SUB dvd a"}, [b])
      val _ = test 6 (@{term "if (a::nat) = 0 then (b::nat) else c"},
                      @{term_pat "if ?SUB then (b::nat) else c"},
                      [@{term "(a::nat) = 0"}])
      val _ = test 7 (@{term "!A. A & B & C"},
                      @{term_pat "!A. A & ?SUB & ?SUB1"}, [B, C])
      val _ = test 8 (@{term "!B. A & B & C"},
                      @{term_pat "!B. ?SUB & B & ?SUB1"}, [A, C])
      val _ = test 9 (@{term "!C. A & B & C"},
                      @{term_pat "!C. ?SUB & ?SUB1 & C"}, [A, B])
      val _ = test 10 (@{term "!A. (A & B) & C"},
                       @{term_pat "!A. (A & ?SUB) & ?SUB1"}, [B, C])
      val _ = test 11 (@{term "!(A::bool). (B & C) & D"},
                       @{term_pat "!(A::bool). ?SUB"}, [@{term "(B & C) & D"}])
      val _ =
          test 12
               (@{term "if (if A then (B::bool) else C) then (a::nat) else b"},
                @{term_pat "if ?SUB then (a::nat) else b"},
                [@{term "if A then (B::bool) else C"}])
      val _ = test 13 (@{term "!A. C & (!B. A & B & D)"},
                       @{term_pat "!A. ?SUB & (!B. A & B & ?SUB1)"}, [C, D])
      val _ =
          test 14 (@{term "!(a::nat). if a = b then (A::bool) else B"},
                   @{term_pat "!(a::nat). if a = ?SUB then (A::bool) else B"},
                   [b])
      val _ = test 15 (@{term "~ (A | B)"},
                       @{term_pat "~ ?SUB"}, [@{term "A | B"}])
      val _ = test 16 (@{term "A | B | C | D"},
                       @{term_pat "?SUB | ?SUB1 | ?SUB2 | ?SUB3"}, [A, B, C, D])
    in () end

val test_get_all_subterms =
    let
      fun err n = "test_get_all_subterms: " ^ (string_of_int n)
      fun test n (t, subs) =
          let
            val subs' = get_all_subterms thy' true t
          in
            if eq_list (op aconv) (subs, subs') then ()
            else raise AUTO2CT (err n, map (cert_thy thy') subs')
          end
      val _ = test 0 (@{term "(a::nat) * b * c"},
                      [@{term "(a::nat) * b * c"}, a, b, c])
      val _ = test 1 (@{term "(a::nat) * (b * c)"},
                      [@{term "(a::nat) * (b * c)"}, a, @{term "(b::nat) * c"},
                       b, c])
    in () end

val test_build_equiv =
    let
      fun err n = "test_build_equiv: " ^ (string_of_int n)
      fun test n (t, equivs) =
          let
            val eq_th = build_equiv ctxt' equivs t
            val lsubs = map lhs_of equivs
            val rsubs = map rhs_of equivs
          in
            if lhs_of eq_th aconv (subst_subterms (t, lsubs)) andalso
               rhs_of eq_th aconv (subst_subterms (t, rsubs)) then ()
            else raise AUTO2CT (err n, [Thm.cprop_of eq_th])
          end
      val _ = test 0 (@{term_pat "(?SUB::nat) * ?SUB1"},
                      [Thm.assume @{cterm "(a::nat) == b"},
                       Thm.assume @{cterm "(c::nat) == d"}])
      val _ = test 1 (@{term_pat "!a. a + (?SUB::nat) = 0"},
                      [Thm.assume @{cterm "(b::nat) == c"}])
      val dvd = Const ("Rings.dvd_class.dvd", @{typ "nat => nat => bool"})
      val trm = Abs ("x", @{typ nat},
                     Abs ("x", @{typ nat}, dvd $ (Bound 0) $ (Bound 1)))
      val _ = test 2 (trm, [])
      (* build_equiv is not a conversion, so don't use conv facilities. *)
      val _ = test 3 (@{term_pat "!a. a + (?SUB::nat) = 0"},
                      [Thm.assume @{cterm "(b::nat) == b"}])
      (* Another possible name conflict. *)
      val _ = test 4 (@{term_pat "!a. a + (?SUB::nat) = 0"},
                      [Thm.assume @{cterm "(a::nat) == a"}])
    in () end

val test_rearrange =
    let
      fun err n = "test_rearrange: " ^ (string_of_int n)
      fun test n (t, t') =
          let
            val ac_itm_opt = get_head_ac_item thy' t
            val _ = assert (is_some ac_itm_opt) (err n)
            val ac_itm = the ac_itm_opt
            val t'' = rearrange_fast thy' t
            val _ = if t' aconv t'' then () else
                    raise AUTO2CT (err n, [cert_thy thy' t''])
            val eq_th = rearrange_subterms thy' ac_itm (cert_thy thy' t)
            val (l, r) = Logic.dest_equals (Thm.prop_of eq_th)
          in
            if l aconv t andalso r aconv t' then ()
            else raise AUTO2CT (err n, [Thm.cprop_of eq_th])
          end
      val _ = test 0 (@{term "C & A & B"}, @{term "A & B & C"})
      val _ = test 1 (@{term "EX (k::nat). a + b < k & k < n"},
                      @{term "EX (k::nat). k < n & a + b < k"})
      val _ = test 2 (@{term "EX (k::nat) l. a + l < k & k < l"},
                      @{term "EX (k::nat) l. k < l & a + l < k"})
      val _ = test 3 (@{term "C & A & B & True"}, @{term "A & B & C"})
    in () end

end;  (* local *)
