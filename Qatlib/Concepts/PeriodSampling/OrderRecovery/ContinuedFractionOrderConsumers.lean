/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CfOrder.CountedContinuedFractionDecoder
import Qatlib.Concepts.PeriodSampling.OrderRecovery.PairLCMOrderRecovery
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HspRecovery.CfOrder
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery
open scoped Classical
set_option maxHeartbeats 2000000

def cfReducedOrderDecode (N M : ℕ) (y : Fin M) : Option (ℕ × ℕ) × ℕ × ℕ :=
  cfRationalDecode N M (reducedOrderNumerator M y)

def cfPairLCMOrderDecode (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (yz : Fin M × Fin M) :
    Option ℕ × ℕ × ℕ × ℕ :=
  let x := cfReducedOrderDecode N M yz.1
  let y := cfReducedOrderDecode N M yz.2
  match x.1, y.1 with
  | some (_, q), some (_, v) =>
    let r := Nat.lcm q v
    (if orderVerificationProduct N a r = 1 then some r else none,
      x.2.1 + y.2.1, x.2.2 + y.2.2, r)
  | _, _ => (none, x.2.1 + y.2.1, x.2.2 + y.2.2, 0)

private theorem cfReducedOrderDecode_eq (N M : ℕ) (y : Fin M) (hs : 2 * N ^ 2 < M) :
    (cfReducedOrderDecode N M y).1 = (reducedOrderDecode N M y).1 := by
  apply cfRationalDecode_eq_bounded N M _ hs
  unfold reducedOrderNumerator
  split <;> omega

theorem cfPairLCMOrderDecode_eq (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (yz : Fin M × Fin M) (hs : 2 * N ^ 2 < M) :
    (cfPairLCMOrderDecode N M a yz).1 = (pairLCMOrderDecode N M a yz).1 := by
  unfold cfPairLCMOrderDecode pairLCMOrderDecode
  (try dsimp only)
  rw [cfReducedOrderDecode_eq N M yz.1 hs, cfReducedOrderDecode_eq N M yz.2 hs]
  cases (reducedOrderDecode N M yz.1).1 <;> cases (reducedOrderDecode N M yz.2).1 <;> rfl

theorem continued_fraction_actual_pair_order_and_factor_consumer
    (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (s t : Fin (orderOf a)) (y z : Fin M)
    (hN : 1 < N) (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M)
    (hc : Nat.Coprime (Nat.gcd s.val t.val) (orderOf a))
    (hy : phaseDistance ((s.val : ℝ) / (orderOf a : ℝ)) ((y.val : ℝ) / M) ≤ 1 / (M : ℝ))
    (hz : phaseDistance ((t.val : ℝ) / (orderOf a : ℝ)) ((z.val : ℝ) / M) ≤ 1 / (M : ℝ)) :
    (cfPairLCMOrderDecode N M a (y, z)).1 = some (orderOf a) ∧
    (cfPairLCMOrderDecode N M a (y, z)).2.1 ≤ 2 * (cfDepth M + 1) ∧
    (cfPairLCMOrderDecode N M a (y, z)).2.2.1 ≤ (cfDepth M + 1) * (cfDepth M + 2) ∧
    (cfPairLCMOrderDecode N M a (y, z)).2.2.2 = orderOf a := by
  have hd := (cfReducedOrderDecode_eq N M y hsize).trans
    (reduced_order_denominator_of_every_good_phase N M a s y hN hr hsize hy)
  have he := (cfReducedOrderDecode_eq N M z hsize).trans
    (reduced_order_denominator_of_every_good_phase N M a t z hN hr hsize hz)
  have hl := reduced_order_pair_lcm_arithmetic (orderOf a) s.val t.val
    (modular_order_pos N a) s.isLt t.isLt hc
  have hx := continued_fraction_bad_output_soundness_and_work N M (reducedOrderNumerator M y)
  have hw := continued_fraction_bad_output_soundness_and_work N M (reducedOrderNumerator M z)
  change (cfReducedOrderDecode N M y).2.1 ≤ _ ∧ (cfReducedOrderDecode N M y).2.2 ≤ _ ∧ _ at hx
  change (cfReducedOrderDecode N M z).2.1 ≤ _ ∧ (cfReducedOrderDecode N M z).2.2 ≤ _ ∧ _ at hw
  simp only [cfPairLCMOrderDecode, hd, he, hl, orderVerificationProduct_eq_pow,
    pow_orderOf_eq_one, if_true]
  have htri := Nat.div_mul_le_self ((cfDepth M + 1) * (cfDepth M + 2)) 2
  refine ⟨trivial, ?_, ?_, trivial⟩ <;> omega

theorem continued_fraction_actual_fresh_order_probability_and_factor_soundness
    (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (hM : 0 < M)
    (hN : 1 < N) (hr : 1 < orderOf a) (hsize : 2 * N ^ 2 < M) :
    (∑ yz ∈ Finset.univ.filter (fun yz : Fin M × Fin M =>
        (cfPairLCMOrderDecode N M a yz).1 = some (orderOf a)),
      (modularOrderLaw N M a hM).prob yz.1 * (modularOrderLaw N M a hM).prob yz.2) ≥
        (8 / Real.pi ^ 2) ^ 2 / 4 ∧
    (∀ (yz : Fin M × Fin M) (d : ℕ),
      ((cfPairLCMOrderDecode N M a yz).1.bind (orderFactor N a)) = some d →
        1 < d ∧ d < N ∧ d ∣ N) := by
  constructor
  · simp_rw [cfPairLCMOrderDecode_eq N M a _ hsize]
    exact pair_lcm_order_actual_fresh_success_bound N M a hM hN hr hsize
  · intro yz d hd
    cases hq : (cfPairLCMOrderDecode N M a yz).1 with
    | none => simp [hq] at hd
    | some q => exact orderFactor_sound N a q d (by simpa [hq] using! hd)
end Qatlib.Concepts.PeriodSampling.OrderRecovery
