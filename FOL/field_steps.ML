(* Proof steps on fields. *)

signature FIELD_STEPS =
sig
  type ord_field_info
  val ord_field_alg_info: thm -> ord_field_info
  val of_nat_unit_th: ord_field_info -> int -> thm
  val mk_rat_wfterm: ord_field_info -> Rat.rat -> wfterm
  val in_carrier_rat: ord_field_info -> Rat.rat -> thm
  val mk_rat_add_th: ord_field_info -> Rat.rat * Rat.rat -> thm
  val mk_rat_mult_th: ord_field_info -> Rat.rat * Rat.rat -> thm
  val mk_rat_minus_th: ord_field_info -> Rat.rat * Rat.rat -> thm
  val mk_rat_ge_zero_th: ord_field_info -> Rat.rat -> thm
  val mk_rat_gt_zero_th: ord_field_info -> Rat.rat -> thm
  val mk_rat_le_th: ord_field_info -> Rat.rat * Rat.rat -> thm
  val mk_rat_less_th: ord_field_info -> Rat.rat * Rat.rat -> thm
  val is_rat_gen: term -> bool
  val add_field_proofsteps: theory -> theory
end;

structure FieldSteps : FIELD_STEPS =
struct

type ord_field_info = {
  G: term,
  cG: cterm,
  ord_ring_info: OrdRingSteps.ord_ring_info,
  of_nat_unit: thm, (* n ~= 0 ==> of_nat(R,n) : units(R) *)
  nat_ge_zero: thm, (* n : nat ==> of_nat(R,n) >= 0 *)
  nat_gt_zero: thm, (* n : nat ==> of_nat(R,n) > 0 *)
  rat_ge_zero: thm, (* m : nat ==> n ~= 0 ==> of_nat(R,m) / of_nat(R,n) >= 0 *)
  rat_gt_zero: thm, (* m ~= 0 ==> n ~= 0 ==> of_nat(R,m) / of_nat(R,n) > 0 *)
  switch_le': thm,  (* 0 <= y - x ==> x <= y *)
  switch_less': thm (* 0 < y - x ==> x < y *)
}

fun ord_field_alg_info ord_field_th =
    let
      val G = dest_arg (prop_of' ord_field_th)
      val cG = Thm.dest_arg (cprop_of' ord_field_th)
      val ord_ring_th = ord_field_th RS @{thm is_ord_fieldD(1)}
    in
      {G = G,
       cG = cG,
       ord_ring_info = OrdRingSteps.ord_ring_alg_data ord_ring_th,
       of_nat_unit  = ord_field_th RS @{thm ord_field_char_zero},
       nat_ge_zero  = ord_ring_th RS @{thm ord_ring_of_nat_ge_zero'},
       nat_gt_zero  = ord_ring_th RS @{thm ord_ring_of_nat_greater_zero'},
       rat_ge_zero  = ord_field_th RS @{thm ord_field_rat_ge_zero},
       rat_gt_zero  = ord_field_th RS @{thm ord_field_rat_greater_zero},
       switch_le'   = ord_ring_th RS @{thm ord_ring_le_switch_left'},
       switch_less' = ord_ring_th RS @{thm ord_ring_less_switch_left'}
      }
    end

(* Product the theorem n ~= 0. *)
fun nat_neq_zero n =
    if n <= 0 then raise AUTO2 "nat_neq_zero"
    else let
      val nt = mk_nat (n - 1)
      val inst = update_env (("n",0), nt) fo_init
      val ctxt = @{context}
    in
      (subst_thm ctxt inst @{thm nat_Suc_not_zero}) RS @{thm not_sym}
    end

(* Given integer n ~= 0, return the theorem of_nat(R,n) : units(R). *)
fun of_nat_unit_th info n =
    if n <= 0 then raise AUTO2 "of_nat_unit_th"
    else let
      val {of_nat_unit, ...} = info
      val in_nat_th = in_nat_raw' n
      val neq_th = nat_neq_zero n
    in
      [in_nat_th, neq_th] MRS of_nat_unit
    end

(* Construct wfterm corresponding to rational r. *)
fun mk_rat_wfterm info r =
    let
      val {cG, ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val (p, q) = Rat.dest r
    in
      if q = 1 then mk_int_wfterm rat_info p
      else let
        val wf_p = mk_int_wfterm rat_info p
        val wf_q = mk_int_wfterm rat_info q
      in
        WfComb (divide_ct, [WfTerm cG, wf_p, wf_q],
                [in_carrier_int rat_info p, of_nat_unit_th info q])
      end
    end

fun in_carrier_rat info r =
    let
      val {ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val {divide_type, ...} = rat_info
      val (p, q) = Rat.dest r
    in
      if q = 1 then in_carrier_int rat_info p
      else let
        val p_in_carrier = in_carrier_int rat_info p
        val q_in_unit = of_nat_unit_th info q
      in
        [p_in_carrier, q_in_unit] MRS divide_type
      end
    end

fun mk_rat_add_th info (r, s) =
    let
      val {cG, ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val plus_exp =
          WfComb (plus_ct,
                  [WfTerm cG, mk_rat_wfterm info r, mk_rat_wfterm info s],
                  [in_carrier_rat info r, in_carrier_rat info s])
    in
      snd (rat_add rat_info plus_exp)
    end

fun mk_rat_mult_th info (r, s) =
    let
      val {cG, ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val times_exp =
          WfComb (times_ct,
                  [WfTerm cG, mk_rat_wfterm info r, mk_rat_wfterm info s],
                  [in_carrier_rat info r, in_carrier_rat info s])
    in
      snd (rat_mult rat_info times_exp)
    end

fun mk_rat_minus_th info (r, s) =
    let
      val {cG, ord_ring_info, ...} = info
      val {ring_info, ...} = ord_ring_info
      val {rat_info, ...} = ring_info
      val minus_exp =
          WfComb (minus_ct,
                  [WfTerm cG, mk_rat_wfterm info r, mk_rat_wfterm info s],
                  [in_carrier_rat info r, in_carrier_rat info s])
    in
      snd (rat_minus rat_info minus_exp)
    end

(* Given n >= 0, produce of_nat(R,n) >= 0. *)
fun mk_nat_ge_zero_th info n =
    let
      val {nat_ge_zero, ...} = info
      val n_in_nat = in_nat_raw' n
    in
      n_in_nat RS nat_ge_zero
    end

(* Given n > 0, produce of_nat(R,n) > 0. *)
fun mk_nat_gt_zero_th info n =
    let
      val {nat_gt_zero, ...} = info
      val n_in_nat = in_nat_raw' n
      val n_neq_0 = nat_neq_zero n
    in
      [n_in_nat, n_neq_0] MRS nat_gt_zero
    end

(* Given r >= 0, produce the corresponding theorem. *)
fun mk_rat_ge_zero_th info r =
    let
      val {rat_ge_zero, ...} = info
      val (p, q) = Rat.dest r
      val _ = assert (p >= 0 andalso q > 0) "rat_ge_zero"
    in
      if q = 1 then mk_nat_ge_zero_th info p
      else let
        val p_in_nat = in_nat_raw' p
        val q_in_nat = in_nat_raw' q
        val q_neq_0 = nat_neq_zero q
      in
        [p_in_nat, q_in_nat, q_neq_0] MRS rat_ge_zero
      end
    end

(* Given r > 0, produce the corresponding theorem. *)
fun mk_rat_gt_zero_th info r =
    let
      val {rat_gt_zero, ...} = info
      val (p, q) = Rat.dest r
      val _ = assert (p > 0 andalso q > 0) "rat_gt_zero"
    in
      if q = 1 then mk_nat_gt_zero_th info p
      else let
        val p_in_nat = in_nat_raw' p
        val p_neq_0 = nat_neq_zero p
        val q_in_nat = in_nat_raw' q
        val q_neq_0 = nat_neq_zero q
      in
        [p_in_nat, q_in_nat, p_neq_0, q_neq_0] MRS rat_gt_zero
      end
    end

(* Given r, s with r <= s, produce the corresponding theorem. *)
fun mk_rat_le_th info (r, s) =
    let
      val _ = assert (Rat.le r s) "rat_le_th"
      val {switch_le', ...} = info
      val diff = Rat.add s (Rat.neg r)
      (* 0 <= diff *)
      val nonneg_th1 = mk_rat_ge_zero_th info diff
      (* s - r = diff *)
      val sub_eq = mk_rat_minus_th info (s, r)
      (* 0 <= s - r *)
      val nonneg_th2 =
          apply_to_thm' (Conv.arg_conv (Conv.rewr_conv (meta_sym sub_eq)))
                        nonneg_th1
    in
      (* r <= s *)
      [in_carrier_rat info r, in_carrier_rat info s, nonneg_th2] MRS switch_le'
    end

(* Given r, s with r < s, produce the corresponding theorem. *)
fun mk_rat_less_th info (r, s) =
    let
      val _ = assert (Rat.lt r s) "rat_less_th"
      val {switch_less', ...} = info
      val diff = Rat.add s (Rat.neg r)
      (* 0 < diff *)
      val pos_th1 = mk_rat_gt_zero_th info diff
      (* s - r = diff *)
      val sub_eq = mk_rat_minus_th info (s, r)
      (* 0 < s - r *)
      val pos_th2 =
          apply_to_thm' (Conv.arg_conv (Conv.rewr_conv (meta_sym sub_eq)))
                        pos_th1
    in
      (* r < s *)
      [in_carrier_rat info r, in_carrier_rat info s, pos_th2] MRS switch_less'
    end

fun is_rat_gen t =
    let
      val (_, args) = Term.strip_comb t
    in
      if length args = 0 then false else is_rat (hd args) t
    end

datatype ord_type = LE | LT | NOT_LE | NOT_LT

fun dest_order_t pat =
    case pat of
        Const (@{const_name le}, _) $ G $ a $ b => SOME (LE, G, a, b)
      | Const (@{const_name less}, _) $ G $ a $ b => SOME (LT, G, a, b)
      | Const (@{const_name Not}, _) $ (
          Const (@{const_name le}, _) $ G $ a $ b) => SOME (NOT_LE, G, a, b)
      | Const (@{const_name Not}, _) $ (
          Const (@{const_name less}, _) $ G $ a $ b) => SOME (NOT_LT, G, a, b)
      | _ => NONE

fun dest_order pat =
    case dest_order_t pat of
        NONE => NONE
      | SOME (ty, G, at, bt) =>
        if is_rat G at andalso is_rat G bt then
          SOME (ty, G, dest_rat at, dest_rat bt)
        else NONE

fun can_mk_const_order_th (ord_type, a, b) =
    case ord_type of
        LE => Rat.le a b
      | LT => Rat.lt a b
      | NOT_LE => not (Rat.le a b)
      | NOT_LT => not (Rat.lt a b)

fun mk_const_order_th (ord_field_th, ord_type, a, b) =
    let
      val info = ord_field_alg_info ord_field_th
    in
      case ord_type of
          LE => mk_rat_le_th info (a, b)
        | LT => mk_rat_less_th info (a, b)
        | NOT_LE =>  (* b < a ==> ~(a <= b) *)
          [ord_field_th, mk_rat_less_th info (b, a)]
              MRS @{thm ord_field_less_to_neg}
        | NOT_LT =>  (* b <= a ==> ~(a < b) *)
          [ord_field_th, mk_rat_le_th info (b, a)]
              MRS @{thm ord_field_le_to_neg}
    end

val null_const_order_matcher =
    let
      fun pre_match pat _ _ = is_some (dest_order pat)

      fun match pat _ tbl (id, inst) =
          if is_none (dest_order pat) then []
          else let
            val (ord_type, G, a, b) = the (dest_order pat)
          in
            if not (can_mk_const_order_th (ord_type, a, b)) then []
            else let
              val ord_field_t = @{term is_ord_field} $ G
              val ord_field_ths =
                  RewriteTable.get_property_t tbl (id, ord_field_t)

              fun process_ord_field_th (id', th) =
                  let
                    val order_th = mk_const_order_th (th, ord_type, a, b)
                  in
                    ((id', inst), order_th)
                  end
            in
              map process_ord_field_th ord_field_ths
            end
          end
    in
      {pre_match = pre_match, match = match}
    end

val add_field_proofsteps =
    fold Consts.add_const_data [
      ("rat", is_rat_gen)

    ] #> fold ItemIO.add_prop_matcher [
      (TY_NULL, null_const_order_matcher)

    ] #> fold add_prfstep_custom [
      ("eval_add_consts",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithTerm @{term_pat "plus(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if is_rat G rt andalso is_rat G st then
              let
                val info = ord_field_alg_info (hd ths)
                val eq_th = mk_rat_add_th info (dest_rat rt, dest_rat st)
              in
                [Update.thm_update (id, to_obj_eq eq_th)]
              end
            else []
          end),

      ("eval_mult_consts",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithTerm @{term_pat "times(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if is_rat G rt andalso is_rat G st then
              let
                val info = ord_field_alg_info (hd ths)
                val eq_th = mk_rat_mult_th info (dest_rat rt, dest_rat st)
              in
                [Update.thm_update (id, to_obj_eq eq_th)]
              end
            else []
          end),

      ("eval_minus_consts",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithTerm @{term_pat "minus(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if is_rat G rt andalso is_rat G st then
              let
                val info = ord_field_alg_info (hd ths)
                val eq_th = mk_rat_minus_th info (dest_rat rt, dest_rat st)
              in
                [Update.thm_update (id, to_obj_eq eq_th)]
              end
            else []
          end),

      ("le_consts",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithGoal @{term_pat "le(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_SHADOW,
       fn ((id, inst), ths) => fn items => fn _ =>
          let
            val (ord_field_th, th) = the_pair ths
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G rt andalso is_rat G st) then []
            else if Rat.le (dest_rat rt) (dest_rat st) then
              let
                val info = ord_field_alg_info ord_field_th
                val le_th = mk_rat_le_th info (dest_rat rt, dest_rat st)
              in
                [Update.thm_update (id, [th, le_th] MRS contra_triv_th)]
              end
            else
              [ShadowItem {id = id, item = the_single items}]
          end),

      ("less_consts",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithGoal @{term_pat "less(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_SHADOW,
       fn ((id, inst), ths) => fn items => fn _ =>
          let
            val (ord_field_th, th) = the_pair ths
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if not (is_rat G rt andalso is_rat G st) then []
            else if Rat.lt (dest_rat rt) (dest_rat st) then
              let
                val info = ord_field_alg_info ord_field_th
                val less_th = mk_rat_less_th info (dest_rat rt, dest_rat st)
              in
                [Update.thm_update (id, [th, less_th] MRS contra_triv_th)]
              end
            else
              [ShadowItem {id = id, item = the_single items}]
          end),

      ("le_consts_shadow",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithFact @{term_pat "le(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_SHADOW,
       fn ((id, inst), _) => fn items => fn _ =>
          let
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if is_rat G rt andalso is_rat G st andalso
               Rat.le (dest_rat rt) (dest_rat st) then
              [ShadowItem {id = id, item = the_single items}]
            else []
          end),

      ("less_consts_shadow",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithFact @{term_pat "less(?G,?NUMC1,?NUMC2)"}],
       PRIORITY_SHADOW,
       fn ((id, inst), _) => fn items => fn _ =>
          let
            val G = lookup_inst inst "G"
            val rt = lookup_instn inst ("NUMC", 1)
            val st = lookup_instn inst ("NUMC", 2)
          in
            if is_rat G rt andalso is_rat G st andalso
               Rat.lt (dest_rat rt) (dest_rat st) then
              [ShadowItem {id = id, item = the_single items}]
            else []
          end),

      ("inv_of_nat_case",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithTerm @{term_pat "inv(?G,of_nat(?G,?NUMC))"}],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val n = lookup_inst inst "NUMC"
            val (ord_field_th, _) = the_pair ths
          in
            if is_nat n andalso dest_nat n > 0 then
              let
                val info = ord_field_alg_info ord_field_th
              in
                [Update.thm_update (id, of_nat_unit_th info (dest_nat n))]
              end
            else []
          end),

      ("divide_of_nat_case",
       [WithProperty @{term_pat "is_ord_field(?G)"},
        WithTerm @{term_pat "divide(?G,?x,of_nat(?G,?NUMC))"}],
       PRIORITY_ADD,
       fn ((id, inst), ths) => fn _ => fn _ =>
          let
            val n = lookup_inst inst "NUMC"
            val (ord_field_th, _) = the_pair ths
          in
            if is_nat n andalso dest_nat n > 0 then
              let
                val info = ord_field_alg_info ord_field_th
              in
                [Update.thm_update (id, of_nat_unit_th info (dest_nat n))]
              end
            else []
          end)
    ]

end  (* FieldSteps *)

val _ = Theory.setup FieldSteps.add_field_proofsteps
