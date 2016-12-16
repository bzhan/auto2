(* Proof steps related to rational numbers. *)

signature RAT_ARITH =
sig
  val ratT: typ
  val lookup_numc: Type.tyenv * Envir.tenv -> int -> Rat.rat
  val lookup_numc0: Type.tyenv * Envir.tenv -> Rat.rat
  val lookup_numc1: Type.tyenv * Envir.tenv -> Rat.rat
  val lookup_numc2: Type.tyenv * Envir.tenv -> Rat.rat

  val rat_le_th: Proof.context -> typ -> Rat.rat -> Rat.rat -> thm
  val rat_less_th: Proof.context -> typ -> Rat.rat -> Rat.rat -> thm

  val add_rat_arith_proofsteps: theory -> theory
end;

structure Rat_Arith : RAT_ARITH =
struct

val ratT = @{typ rat}
fun rat_eq (r, s) = (Rat.ord (r, s) = EQUAL)

val mk_rat = Ring_Arith.mk_rat

fun lookup_numc inst n = dest_numc_rat (lookup_instn inst ("NUMC", n))
fun lookup_numc0 inst = lookup_numc inst 0
fun lookup_numc1 inst = lookup_numc inst 1
fun lookup_numc2 inst = lookup_numc inst 2

(* Obtain the theorem r <= s. *)
fun rat_le_th ctxt T r s =
    if not (Rat.le r s) then raise AUTO2 "rat_le_th: input"
    else let
      val ctxt' = ctxt addsimps [
            @{thm zero_less_Fract_iff}, @{thm zero_le_Fract_iff}]
    in
      prove_by_simp ctxt' [] (
        Const (@{const_name less_eq}, T --> T --> boolT)
              $ mk_rat T r $ mk_rat T s)
    end

(* Obtain the theorem r < s. *)
fun rat_less_th ctxt T r s =
    if not (Rat.lt r s) then raise AUTO2 "nat_less_th: input"
    else let
      val ctxt' = ctxt addsimps [
            @{thm zero_less_Fract_iff}, @{thm zero_le_Fract_iff}]
    in
      prove_by_simp ctxt' [] (
        Const (@{const_name less}, T --> T --> boolT)
              $ mk_rat T r $ mk_rat T s)
    end

fun ring_pat str =
    let
      val ctxt = @{context}
      val ctxt' = ctxt |> fold Variable.declare_term
                       [@{term_pat "?NUMC1::(?'a::linordered_idom)"},
                        @{term_pat "?a::(?'a::linordered_idom)"},
                        @{term_pat "?s::(?'a::linordered_idom)"}]
    in
      read_pat ctxt' str
    end

val add_rat_arith_proofsteps =
    fold add_prfstep_custom [
      ("rat_is_positive",
       [WithTerm @{term_pat "?NUMC::?'a::linordered_field"}],
       PRIORITY_ADD,
       (fn ((id, inst), _) => fn _ => fn {ctxt, ...} =>
           let
             val t = lookup_inst inst "NUMC"
             val n = dest_numc_rat t
             val T = fastype_of t
           in
             if Rat.lt rat_zero n then
               let
                 val cv = rewr_obj_eq (obj_sym @{thm is_positive_def})
                 val th = apply_to_thm' cv  (rat_less_th ctxt T rat_zero n)
               in
                 [Update.thm_update (id, th)]
               end
             else []
           end)),

      (* Resolve equality facts with constants. *)
      ("compare_rat_consts",
       [WithFact (ring_pat "?NUMC1 = ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (rat_eq (lookup_numc1 inst, lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)]),

      (* Resolve inequality facts with constants. *)
      ("le_rat_consts",
       [WithFact (ring_pat "?NUMC1 <= ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (Rat.le (lookup_numc1 inst) (lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)]),

      ("less_rat_consts",
       [WithFact (ring_pat "?NUMC1 < ?NUMC2"),
        Filter (fn _ => fn (_, inst) =>
                   not (Rat.lt (lookup_numc1 inst) (lookup_numc2 inst)))],
       PRIORITY_RESOLVE,
       fn ((id, _), ths) => fn _ => fn {ctxt, ...} =>
          [Update.thm_update (id, contra_by_simp ctxt ths)])
    ]

end  (* structure Rat_Arith. *)

val _ = Theory.setup Rat_Arith.add_rat_arith_proofsteps

(* Prop-matching for negation of order. *)
val neg_order_matcher =
    let
      fun pre_match pat {tname, ...} (tbl as {ctxt, ...}) =
          if is_neg pat andalso is_linorder ctxt (the_single tname) andalso
             get_arg_type (the_single tname) <> natT then
            let
              val neg_pat = pat |> cert ctxt |> neg_ineq_cv |> rhs_of
            in
              Matcher.pre_match tbl (neg_pat, the_single tname)
            end
          else false

      fun match pat {tname, prop, ...} (tbl as {ctxt, ...}) (id, inst) =
          if is_neg pat andalso is_linorder ctxt (the_single tname) andalso
             get_arg_type (the_single tname) <> natT then
            let
              val neg_pat = pat |> cert ctxt |> neg_ineq_cv |> rhs_of
              val t = the_single tname
              val insts' = Matcher.rewrite_match tbl (neg_pat, t) (id, inst)
              fun process_inst (inst, eq_th) =
                  (inst,
                   prop |> Thm.equal_elim (make_trueprop_eq (meta_sym eq_th))
                        |> apply_to_thm' neg_ineq_back_cv)
            in
              map process_inst insts'
            end
          else []
    in
      {pre_match = pre_match, match = match}
    end

val _ = Theory.setup (ItemIO_Data.add_prop_matcher (TY_PROP, neg_order_matcher))
