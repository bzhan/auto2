(* Unit test for acdata.ML. *)

local

  open ACUtil

  val thy = @{theory}
  val thy' = thy |> add_logic_ac_data |> Nat_Arith.add_arith_ac_data
in

val test_comb_ac_equiv =
    let
      fun err n = "test_comb_ac_equiv: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let
            val ac_itm = the (get_head_ac_item thy' t1)
                         handle Option.Option =>
                                raise AUTO2 "test_comb_ac_equiv: ac_itm"
            val ts1 = dest_ac ac_itm t1
            val ts2 = dest_ac ac_itm t2
            fun eq (t1', t2') =
                Thm.assume (cert_thy thy' (Logic.mk_equals (t1', t2')))
            val eqs = map eq (ts1 ~~ ts2)
            val th = comb_ac_equiv thy' ac_itm eqs
          in
            if Thm.prop_of th aconv Logic.mk_equals (t1, t2) then ()
            else raise AUTO2CT (err n, [Thm.cprop_of th])
          end
      val _ = test 0 (@{term "(a::nat) + b + c"}, @{term "(d::nat) + e + f"})
      val _ = test 1 (@{term "A | B | C | D"}, @{term "E | F | G | H"})
    in () end

val test_rearrange_fast =
    let
      fun err n = "test_rearrange_fast: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let val t2' = rearrange_fast thy' t1
          in if t2' aconv t2 then ()
             else raise AUTO2CT (err n, [cert_thy thy' t2']) end
      val _ = test 0 (@{term "(a::nat) + e + c + b + d"},
                      @{term "(a::nat) + b + c + d + e"})
      val _ = test 1 (@{term "(a::nat) + (c * b) + (gcd e f) + g"},
                      @{term "(a::nat) + g + gcd e f + c * b"})
      val _ = test 2 (@{term "A | C | D | B"}, @{term "A | B | C | D"})
      val _ = test 3 (@{term "(B | A) | C"}, @{term "C | (B | A)"})
      val _ = test 4 (@{term "(0::nat) + e + b + c + 0"},
                      @{term "(b::nat) + c + e"})
    in () end

val test_rearrange_assoc_full =
    let
      fun err n = "test_rearrange_assoc_full: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let
            val ct1 = cert_thy thy' t1
            val ct2' = Thm.rhs_of (rearrange_assoc_full thy' ct1)
          in
            if t2 aconv (Thm.term_of ct2') then ()
            else raise AUTO2CT (err n, [ct2'])
          end

      val _ = test 0 (@{term "(a::nat) + (b + d) + (c + e)"},
                      @{term "(a::nat) + b + d + c + e"})
      val _ = test 1 (@{term "A & (B & D) & (C & E)"},
                      @{term "A & B & D & C & E"})
      val _ = test 2 (@{term "((a::nat) + c) + (b + d) = c + (e + f)"},
                      @{term "(a::nat) + c + b + d = c + e + f"})
      val _ = test 3 (@{term "((a::nat) + 0) + (b + 0) = c + (0 + f)"},
                      @{term "(a::nat) + 0 + b + 0 = c + 0 + f"})
      val _ = test 4 (@{term "(q::nat) dvd q * (p * p)"},
                      @{term "(q::nat) dvd q * p * p"})
    in () end

val test_rearrange_ac =
    let
      fun err n = "test_rearrange_ac: " ^ (string_of_int n)
      fun test n (t1, t2) =
          let val ct2' = Thm.rhs_of (rearrange_ac thy' (cert_thy thy' t1))
          in if t2 aconv (Thm.term_of ct2') then ()
             else raise AUTO2CT (err n, [ct2']) end

      val _ = test 0 (@{term "(a::nat) + (c * b) + (gcd (f * e * d) g) + h"},
                      @{term "(a::nat) + h + b * c + gcd g (d * e * f)"})
      val _ = test 1 (@{term "(a::nat) + (d * b + c)"},
                      @{term "(a::nat) + (c + b * d)"})
      val _ = test 2 (@{term "!(a::nat). a + (d * b + c) = 0"},
                      @{term "!(a::nat). a + (c + b * d) = 0"})
      val _ = test 3 (@{prop "((d::nat) + e) * c = d * c + e * c"},
                      @{prop "c * ((d::nat) + e) = c * d + c * e"})
      val _ = test 4 (@{term "A | C | (c::nat) + b + a = 0 | B"},
                      @{term "A | B | C | a + b + (c::nat) = 0"})
      val _ = test 5 (@{term "(1::nat) * a * b * c * d * 1"},
                      @{term "(a::nat) * b * c * d"})
      val _ = test 6 (@{term "(1::nat) * a * b * c * d"},
                      @{term "(a::nat) * b * c * d"})
      val _ = test 7 (@{term "(1::nat) * b * c * 1 * a * d"},
                      @{term "(a::nat) * b * c * d"})
      val _ = test 8 (@{term "True & A & C & B & True"},
                      @{term "A & B & C"})
    in () end

end;  (* local *)
