/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery

def orderFactor (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (r : ℕ) : Option ℕ :=
  if r % 2 = 0 then
    let t := ((orderVerificationProduct N a (r / 2) : (ZMod N)ˣ) : ZMod N).val
    let d := Nat.gcd N (t - 1)
    if 1 < d ∧ d < N ∧ d ∣ N then some d else none
  else none

theorem orderFactor_sound (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (r d : ℕ)
    (h : orderFactor N a r = some d) : 1 < d ∧ d < N ∧ d ∣ N := by
  unfold orderFactor at h
  split at h
  · (try dsimp only at h)
    split at h
    · cases Option.some.inj h
      assumption
    · simp at h
  · simp at h

theorem modular_order_verification_work_and_factor_soundness :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M),
      (verifiedOrderDecode N M a y).2.1 ≤ N * (N + 1) / 2 ∧
        (verifiedOrderDecode N M a y).2.2 ≤ N ∧
        (∀ q, (verifiedOrderDecode N M a y).1 = some q → a ^ q = 1) ∧
        ∀ (r d : ℕ), orderFactor N a r = some d → 1 < d ∧ d < N ∧ d ∣ N := by
  intro N M _ a y
  obtain ⟨hc, hm, hs⟩ := verifiedOrderDecode_sound_and_work N M a y
  exact ⟨hc, hm, hs, fun r d => orderFactor_sound N a r d⟩

theorem modular_order_fifteen_decode :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    (verifiedOrderDecode 15 1024 a (⟨256, by omega⟩ : Fin 1024)).1 = some 4 := by
  decide

theorem modular_order_fifteen_factor :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    orderFactor 15 a 4 = some 3 := by
  decide

theorem orderFactor_half_power_val_ne_zero (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (r : ℕ) :
    ((orderVerificationProduct N a (r / 2) : (ZMod N)ˣ) : ZMod N).val ≠ 0 := by
  letI : Fact (1 < N) := ⟨hN⟩
  rw [ZMod.val_ne_zero]
  exact (orderVerificationProduct N a (r / 2)).isUnit.ne_zero

theorem modular_order_fifteen_order :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    orderOf a = 4 := by
  (try dsimp only)
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

theorem modular_order_fifteen_actual_factor_consumer :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    (verifiedOrderDecode 15 1024 a (⟨256, by omega⟩ : Fin 1024)).1 = some 4 ∧
      orderFactor 15 a 4 = some 3 ∧
      (∑ y ∈ Finset.univ.filter (fun y : Fin 1024 =>
        (verifiedOrderDecode 15 1024 a y).1 = some 4),
        (modularOrderLaw 15 1024 a (by omega)).prob y) ≥ 4 / Real.pi ^ 2 := by
  (try dsimp only)
  refine ⟨modular_order_fifteen_decode, modular_order_fifteen_factor, ?_⟩
  have h := modular_order_actual_verified_success_lower_bound 15 1024
    (Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)) (by omega) (by omega)
    (by rw [modular_order_fifteen_order]; omega) (by omega)
  rw [modular_order_fifteen_order] at h
  have hphi : Nat.totient 4 = 2 := by decide
  rw [hphi] at h
  norm_num only [Nat.cast_ofNat] at h
  convert! h using 1
  ring

end Qatlib.Concepts.PeriodSampling.OrderRecovery
