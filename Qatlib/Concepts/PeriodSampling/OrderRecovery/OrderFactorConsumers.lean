/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.BoundedRationalOrderDecoder

/-!
# Factor extraction from modular order candidates

This module defines `orderFactor`, which checks an even exponent and tests the gcd of `N` with
the predecessor of the corresponding half-power residue. Every returned result is a nontrivial
divisor, as required by the factoring reduction in [Shor1997].

The module combines this soundness result with the work bounds for `verifiedOrderDecode` and
gives a concrete base-two example modulo fifteen.

## Main statements

* `modular_order_verification_work_and_factor_soundness`: decoder work bounds and sound exponent
  and divisor outputs.
* `modular_order_fifteen_actual_factor_consumer`: recovery of order four, extraction of factor
  three, and a success probability bound for modulus fifteen.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.OrderRecovery

/-- For even `r`, tests the gcd of `N` with the predecessor of the residue of `a ^ (r / 2)` and
returns it when it is a nontrivial divisor. -/
def orderFactor (N : ℕ) [NeZero N] (a : (ZMod N)ˣ) (r : ℕ) : Option ℕ :=
  if r % 2 = 0 then
    let t := ((orderVerificationProduct N a (r / 2) : (ZMod N)ˣ) : ZMod N).val
    let d := Nat.gcd N (t - 1)
    if 1 < d ∧ d < N ∧ d ∣ N then some d else none
  else none

/-- Every divisor returned by `orderFactor` lies strictly between one and `N` and divides `N`. -/
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

/-- The verified order decoder satisfies its scan and verification bounds and returns only
exponents with `a ^ q = 1`; every successful factor extraction returns a nontrivial divisor
[Shor1997]. -/
theorem modular_order_verification_work_and_factor_soundness :
    ∀ (N M : ℕ) [NeZero N] (a : (ZMod N)ˣ) (y : Fin M),
      (verifiedOrderDecode N M a y).2.1 ≤ N * (N + 1) / 2 ∧
        (verifiedOrderDecode N M a y).2.2 ≤ N ∧
        (∀ q, (verifiedOrderDecode N M a y).1 = some q → a ^ q = 1) ∧
        ∀ (r d : ℕ), orderFactor N a r = some d → 1 < d ∧ d < N ∧ d ∣ N := by
  intro N M _ a y
  obtain ⟨hc, hm, hs⟩ := verifiedOrderDecode_sound_and_work N M a y
  exact ⟨hc, hm, hs, fun r d => orderFactor_sound N a r d⟩

/-- For base two modulo fifteen and clock size 1024, the verified decoder sends sample 256 to
order candidate four. -/
theorem modular_order_fifteen_decode :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    (verifiedOrderDecode 15 1024 a (⟨256, by omega⟩ : Fin 1024)).1 = some 4 := by
  decide

/-- For base two modulo fifteen, exponent four makes `orderFactor` return three. -/
theorem modular_order_fifteen_factor :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    orderFactor 15 a 4 = some 3 := by
  decide

/-- For `1 < N`, the residue value of the half-exponent verification product is nonzero. -/
theorem orderFactor_half_power_val_ne_zero (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (r : ℕ) :
    ((orderVerificationProduct N a (r / 2) : (ZMod N)ˣ) : ZMod N).val ≠ 0 := by
  letI : Fact (1 < N) := ⟨hN⟩
  rw [ZMod.val_ne_zero]
  exact (orderVerificationProduct N a (r / 2)).isUnit.ne_zero

/-- The unit represented by two modulo fifteen has multiplicative order four. -/
theorem modular_order_fifteen_order :
    let a : (ZMod 15)ˣ := Units.mkOfMulEqOne (2 : ZMod 15) 8 (by decide)
    orderOf a = 4 := by
  (try dsimp only)
  apply (orderOf_eq_iff (by decide : 0 < 4)).mpr
  refine ⟨by decide, ?_⟩
  intro m hm hm0
  interval_cases m <;> decide

/-- For base two modulo fifteen, sample 256 at clock size 1024 decodes to four and yields factor
three; the total probability of decoding four is at least `4 / π²` [Shor1997]. -/
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
