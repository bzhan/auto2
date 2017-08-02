(* Proof steps for intervals. *)

signature INTERVAL_STEPS =
sig
  val add_interval_proofsteps: theory -> theory
end;

structure IntervalSteps : INTERVAL_STEPS =
struct

open NatArith
open FieldSteps

fun mk_rat_divide_th info (r, n) =
    let
      val {cG, ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val divide_exp =
          WfComb (divide_ct,
                  [WfTerm cG, mk_rat_wfterm info r, mk_int_wfterm rat_info n],
                  [in_carrier_rat info r, of_nat_unit_th info n])
    in
      snd (rat_divide rat_info divide_exp)
    end

val add_interval_proofsteps =
    fold add_prfstep_custom [
      ("mem_closed_interval",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithGoal @{term_pat "mem(?NUMC,closed_interval(?G,?NUMC1,?NUMC2))"}],
       PRIORITY_RESOLVE,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val (ord_field_th, th) = the_pair ths
            val xt = lookup_inst inst "NUMC"
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G xt andalso is_rat G rt andalso is_rat G st) then []
            else let
              val x = dest_rat xt
              val r = dest_rat rt
              val s = dest_rat st
            in
              if Rat.le r x andalso Rat.le x s then
                let
                  val info = ord_field_alg_info ord_field_th
                  val le_th1 = mk_rat_le_th info (r, x)
                  val le_th2 = mk_rat_le_th info (x, s)
                  val mem_th = [ord_field_th, le_th1, le_th2]
                                   MRS @{thm closed_interval_memI}
                in
                  [Update.thm_update (id, [th, mem_th] MRS contra_triv_th)]
                end
              else []
            end
          end),

      ("not_mem_closed_interval",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithFact @{term_pat "mem(?NUMC,closed_interval(?G,?NUMC1,?NUMC2))"}],
       PRIORITY_RESOLVE,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val (ord_field_th, th) = the_pair ths
            val xt = lookup_inst inst "NUMC"
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G xt andalso is_rat G rt andalso is_rat G st) then []
            else let
              val x = dest_rat xt
              val r = dest_rat rt
              val s = dest_rat st
            in
              if Rat.lt x r then
                let
                  val info = ord_field_alg_info ord_field_th
                  val less_th = mk_rat_less_th info (x, r)
                  val contra_th = [ord_field_th, less_th, th]
                                       MRS @{thm closed_interval_not_memI(1)}
                in
                  [Update.thm_update (id, contra_th)]
                end
              else if Rat.lt s x then
                let
                  val info = ord_field_alg_info ord_field_th
                  val less_th = mk_rat_less_th info (s, x)
                  val contra_th = [ord_field_th, less_th, th]
                                       MRS @{thm closed_interval_not_memI(2)}
                in
                  [Update.thm_update (id, contra_th)]
                end
              else []
            end
          end),

      ("add_const_in_closed_interval",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithWellForm (@{term_pat "plus(?G,?x,?NUMC)"},
                      @{term_pat "mem(?x, carrier(?G))"}),
        WithGoal (mk_mem (@{term_pat "plus(?G,?x,?NUMC)"},
                          @{term_pat "closed_interval(?G,?NUMC1,?NUMC2)"}))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val (ord_field_th, mem_x, th) = the_triple ths
            val G = lookup_inst inst "G"
            val yt = lookup_inst inst "NUMC"
            val at = lookup_instn inst ("NUMC", 1)
            val bt = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G yt andalso is_rat G at andalso is_rat G bt) then []
            else let
              val info = ord_field_alg_info ord_field_th
              val (y, a, b) = (dest_rat yt, dest_rat at, dest_rat bt)
              val th2 = [ord_field_th, mem_x, in_carrier_rat info a,
                         in_carrier_rat info b, in_carrier_rat info y, th]
                            MRS @{thm closed_interval_plus}
              val eq1 = mk_rat_minus_th info (a, y)
              val eq2 = mk_rat_minus_th info (b, y)
              val th3 = th2 |> apply_to_thm' (
                    Conv.arg_conv (
                      Conv.arg_conv (
                        Conv.every_conv [Conv.arg1_conv (Conv.rewr_conv eq1),
                                         Conv.arg_conv (Conv.rewr_conv eq2)])))
            in
              [Update.thm_update (id, th3)]
            end
          end),

      ("diff_const_in_closed_interval",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithWellForm (@{term_pat "minus(?G,?x,?NUMC)"},
                      @{term_pat "mem(?x, carrier(?G))"}),
        WithGoal (mk_mem (@{term_pat "minus(?G,?x,?NUMC)"},
                          @{term_pat "closed_interval(?G,?NUMC1,?NUMC2)"}))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val (ord_field_th, mem_x, th) = the_triple ths
            val G = lookup_inst inst "G"
            val yt = lookup_inst inst "NUMC"
            val at = lookup_instn inst ("NUMC", 1)
            val bt = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G yt andalso is_rat G at andalso is_rat G bt) then []
            else let
              val info = ord_field_alg_info ord_field_th
              val (y, a, b) = (dest_rat yt, dest_rat at, dest_rat bt)
              val th2 = [ord_field_th, mem_x, in_carrier_rat info a,
                         in_carrier_rat info b, in_carrier_rat info y, th]
                            MRS @{thm closed_interval_minus}
              val eq1 = mk_rat_add_th info (a, y)
              val eq2 = mk_rat_add_th info (b, y)
              val th3 = th2 |> apply_to_thm' (
                    Conv.arg_conv (
                      Conv.arg_conv (
                        Conv.every_conv [Conv.arg1_conv (Conv.rewr_conv eq1),
                                         Conv.arg_conv (Conv.rewr_conv eq2)])))
            in
              [Update.thm_update (id, th3)]
            end
          end),

      ("mult_const_in_closed_interval",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithWellForm (@{term_pat "times(?G,?NUMC,?x)"},
                      @{term_pat "mem(?x, carrier(?G))"}),
        WithGoal (mk_mem (@{term_pat "times(?G,?NUMC,?x)"},
                          @{term_pat "closed_interval(?G,?NUMC1,?NUMC2)"}))],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val (ord_field_th, mem_x, th) = the_triple ths
            val G = lookup_inst inst "G"
            val yt = lookup_inst inst "NUMC"
            val at = lookup_instn inst ("NUMC", 1)
            val bt = lookup_instn inst ("NUMC", 2)
          in
            if not (is_of_nat G yt andalso is_rat G at andalso is_rat G bt
                    andalso dest_of_nat yt > 0) then []
            else let
              val info = ord_field_alg_info ord_field_th
              val (y, a, b) = (dest_of_nat yt, dest_rat at, dest_rat bt)
              val th2 = [ord_field_th, mem_x, in_carrier_rat info a,
                         in_carrier_rat info b,
                         mk_rat_less_th info (rat_zero, Rat.of_int y), th]
                            MRS @{thm closed_interval_times}
              val eq1 = mk_rat_divide_th info (a, y)
              val eq2 = mk_rat_divide_th info (b, y)
              val th3 = th2 |> apply_to_thm' (
                    Conv.arg_conv (
                      Conv.arg_conv (
                        Conv.every_conv [Conv.arg1_conv (Conv.rewr_conv eq1),
                                         Conv.arg_conv (Conv.rewr_conv eq2)])))
            in
              [Update.thm_update (id, th3)]
            end
          end)
    ]

end  (* IntervalSteps *)

val _ = Theory.setup IntervalSteps.add_interval_proofsteps
