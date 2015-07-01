(* Unit test for util.ML. *)

val test_inplace_abstract =
    let
      fun err n = "test_inplace_abstract: " ^ (string_of_int n)
      val pat1 = @{term_pat "!(x::nat) (y::nat). (?p_::nat) + ?q_1 = 0"}
      val trm1 = inplace_abstract_over pat1
      val _ = assert (trm1 aconv @{term "!x y. (x::nat) + y = 0"}) (err 0)
      val pat2 =
          @{term_pat "!(x::nat). (?p_::nat) = 0 & (!(y::nat). ?p_+?q_1 = 0)"}
      val trm2 = inplace_abstract_over pat2
      val _ = assert (trm2 aconv @{term "!x. x = 0 & (!y. (x::nat) + y = 0)"})
                     (err 1)
    in
      ()
    end

val test_normalize_pred_comm =
    let
      fun test (ct1, ct2) =
          let
            val th = Logic_ProofSteps.normalize_pred_comm ct1
            val (ct1', ct2') = Thm.dest_equals (Thm.cprop_of th)
          in
            if ct1 aconvc ct1' andalso ct2 aconvc ct2' then ()
            else raise AUTO2CT ("test_normalize_pred_comm", [ct1', ct2'])
          end
      val _ = test (@{cterm "EX i j. ka = p ^ i & y = p ^ j"},
                    @{cterm "EX i j. ka = p ^ i & y = p ^ j"})
      val _ = test (@{cterm "EX i j. ka = p ^ j & y = p ^ i"},
                    @{cterm "EX j i. ka = p ^ j & y = p ^ i"})
      val _ = test (@{cterm "ka = p ^ j & y = p ^ i"},
                    @{cterm "ka = p ^ j & y = p ^ i"})
    in () end

fun assert_eq_prop t txt th =
    let val _ = assert (t aconv (Thm.prop_of th)) txt in th end

val test_prop1 =
    let
      fun err n = "test_prop1: " ^ (string_of_int n)
      val thm = @{thm Meson.make_pos_rule'}
    in
      thm |> assert_eq_prop (@{term_pat "?P | ?Q ==> ~ ?P ==> ?Q"})
          (err 0)
          |> rewrite_thm_to_contra_form
          |> assert_eq_prop (@{term_pat "?P | ?Q ==> ~ ?P ==> ~ ?Q ==> False"})
          (err 1)
          |> apply_to_thm (move_to_front_conv 2)
          |> assert_eq_prop (@{term_pat "~ ?Q ==> ?P | ?Q ==> ~ ?P ==> False"})
          (err 2)
          |> rewrite_thm_from_contra_form
          |> assert_eq_prop (@{term_pat "~ ?Q ==> ?P | ?Q ==> ?P"}) (err 3)
    end

val test_prop2 =
    let
      fun err n = "test_prop2: " ^ (string_of_int n)
      val thm = @{thm HOL.conjI}
    in
      thm |> assert_eq_prop (@{term_pat "?P ==> ?Q ==> ?P & ?Q"}) (err 0)
          |> rewrite_thm_to_contra_form
          |> assert_eq_prop (@{term_pat "?P ==> ?Q ==> ~ (?P & ?Q) ==> False"})
          (err 1)
          |> rotate_prems_conv_thm
          (map HOLogic.mk_Trueprop
               [@{term_pat "?Q::bool"}, @{term_pat "~ (?P & ?Q)"},
                @{term_pat "?P::bool"}])
          |> assert_eq_prop (@{term_pat "?Q ==> ~ (?P & ?Q) ==> ?P ==> False"})
          (err 2)
          |> rewrite_thm_from_contra_form
          |> assert_eq_prop (@{term_pat "?Q ==> ~ (?P & ?Q) ==> ~ ?P"}) (err 3)
    end

val test_to_obj_conv =
    let
      fun err n = "test_to_obj_conv: " ^ (string_of_int n)
      val ctxt = @{context}
      fun assert_eq th ct txt =
          let val ct' = Thm.rhs_of th
          in if ct' aconvc ct then () else raise AUTO2CT (txt, [ct']) end
      val ct1 = @{cprop "A ==> B ==> (!!(n::nat). C n) ==> D"}
      val ct2 = @{cprop "A --> B --> (!(n::nat). C n) --> D"}
      val ct3 = @{cprop "!(y::nat) (x::nat). P x y --> (!z. Q x y z)"}
      val _ = assert_eq (to_obj_conv ctxt ct1) ct2 (err 0)
      val _ = assert_eq (to_meta_imp_conv ct2)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 1)
      val _ = assert_eq (to_meta_all_conv ctxt ct3)
              @{cprop "!!(y::nat) (x::nat). (P x y --> (!z. Q x y z))"} (err 2)
      val _ = assert_eq (to_obj_conv_on_horn ctxt ct1)
              @{cprop "A ==> B ==> (!(n::nat). C n) ==> D"} (err 4)
    in () end
