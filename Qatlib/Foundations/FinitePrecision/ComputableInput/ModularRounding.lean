/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-! A public scalar center-and-round bridge for actual modular observations.
This module proves deterministic integer identities and bounds. It does not
provide a full list decoder, sampling guarantee, or resource comparison. -/

set_option autoImplicit false

namespace Qatlib.Foundations.FinitePrecision.ComputableInput.ModularRounding

open scoped BigOperators

/-- Canonical centered lift, with the positive representative at a half-modulus tie. -/
def pqcSyndromeCenter {q : ℕ} (y : ZMod q) : ℤ := y.valMinAbs

/-- Integer nearest-grid rounding; exact half-grid ties round toward positive infinity. -/
def pqcSyndromeRound (k c : ℤ) : ℤ := (2 * c + k) / (2 * k)

/-- Public scalar processing takes only the modulus observation and grid scale. -/
def pqcSyndromePublicRound {q : ℕ} (k : ℤ) (y : ZMod q) : ℤ :=
  pqcSyndromeRound k (pqcSyndromeCenter y)

/-- The actual integer program satisfies `pqc_syndrome_center_spec` under the complete displayed premises. -/
theorem pqc_syndrome_center_spec
    {q : ℕ} [NeZero q] (y : ZMod q) :
    ((pqcSyndromeCenter y : ℤ) : ZMod q) = y ∧
      -(q : ℤ) < 2 * pqcSyndromeCenter y ∧
      2 * pqcSyndromeCenter y ≤ (q : ℤ) := by
  refine ⟨ZMod.coe_valMinAbs y, ?_⟩
  simpa only [pqcSyndromeCenter, Set.mem_Ioc, mul_comm] using y.valMinAbs_mem_Ioc

/-- Congruence and the canonical centered interval uniquely determine the lift. -/
theorem pqc_syndrome_center_unique_lift
    {q : ℕ} [NeZero q] (y : ZMod q) (t : ℤ)
    (hobs : (t : ZMod q) = y)
    (hrange : -(q : ℤ) < 2 * t ∧ 2 * t ≤ (q : ℤ)) :
    pqcSyndromeCenter y = t := by
  apply (ZMod.valMinAbs_spec y t).2
  exact ⟨hobs.symm, by simpa only [Set.mem_Ioc, mul_comm] using hrange⟩

/-- Strict no-wrap recovers the actual integer behind the modular observation. -/
theorem pqc_syndrome_center_of_no_wrap
    {q : ℕ} [NeZero q] (y : ZMod q) (t : ℤ)
    (hobs : (t : ZMod q) = y) (hwrap : 2 * |t| < (q : ℤ)) :
    pqcSyndromeCenter y = t := by
  apply pqc_syndrome_center_unique_lift y t hobs
  have hneg := neg_abs_le t
  have hpos := le_abs_self t
  constructor <;> linarith

/-- Translation by an integer grid vector commutes with this exact rounding rule. -/
theorem pqc_syndrome_round_translate
    (k z η : ℤ) (hk : 0 < k) :
    pqcSyndromeRound k (k * z + η) = z + pqcSyndromeRound k η := by
  have h2k : 2 * k ≠ 0 := ne_of_gt (by linarith)
  unfold pqcSyndromeRound
  rw [show 2 * (k * z + η) + k = (2 * η + k) + z * (2 * k) by ring,
    Int.add_mul_ediv_right _ _ h2k]
  ring

/-- The residual lies in the half-open nearest-grid interval. -/
theorem pqc_syndrome_round_residual_bounds
    (k η : ℤ) (hk : 0 < k) :
    -k ≤ 2 * (η - k * pqcSyndromeRound k η) ∧
      2 * (η - k * pqcSyndromeRound k η) < k := by
  have h2k : 0 < 2 * k := by linarith
  have hlo := Int.mul_ediv_self_le (x := 2 * η + k) (k := 2 * k) (ne_of_gt h2k)
  have hhi := Int.lt_mul_ediv_self_add (x := 2 * η + k) (k := 2 * k) h2k
  unfold pqcSyndromeRound
  constructor <;> nlinarith

/-- A strict half-grid noise bound forces the rounding displacement to zero. -/
theorem pqc_syndrome_round_zero_of_small
    (k η : ℤ) (hnoise : 2 * |η| < k) :
    pqcSyndromeRound k η = 0 := by
  unfold pqcSyndromeRound
  apply Int.ediv_eq_zero_of_lt
  · have hneg := neg_abs_le η
    linarith
  · have hpos := le_abs_self η
    linarith

/-- Even outside the strict-correctness regime, the displacement is controlled
by the actual integer noise. The zero-displacement case is handled separately. -/
theorem pqc_syndrome_round_displacement_abs
    (k η : ℤ) (hk : 0 < k) :
    |k * pqcSyndromeRound k η| ≤ 2 * |η| := by
  by_cases hz : pqcSyndromeRound k η = 0
  · simp only [hz, mul_zero, abs_zero]
    exact mul_nonneg (by decide) (abs_nonneg η)
  have hlarge : k ≤ 2 * |η| := by
    by_contra h
    have hsmall : 2 * |η| < k := lt_of_not_ge h
    exact hz (pqc_syndrome_round_zero_of_small k η hsmall)
  have hbounds := pqc_syndrome_round_residual_bounds k η hk
  have hneg := neg_abs_le η
  have hpos := le_abs_self η
  apply abs_le.mpr
  constructor <;> nlinarith [hbounds.1, hbounds.2]

/-- Squared form of the displacement bound, with no division in the conclusion. -/
theorem pqc_syndrome_round_displacement_energy
    (k η : ℤ) (hk : 0 < k) :
    k ^ 2 * (pqcSyndromeRound k η) ^ 2 ≤ 4 * η ^ 2 := by
  have h := pqc_syndrome_round_displacement_abs k η hk
  have hs := (sq_le_sq₀ (abs_nonneg (k * pqcSyndromeRound k η))
    (mul_nonneg (by decide) (abs_nonneg η))).2 h
  simpa [sq_abs, mul_pow] using hs

/-- Exact displacement for the same actual modular observation, under no-wrap. -/
theorem pqc_syndrome_public_round_error
    {q : ℕ} [NeZero q] (k z η : ℤ) (hk : 0 < k) (y : ZMod q)
    (hobs : ((k * z + η : ℤ) : ZMod q) = y)
    (hwrap : 2 * |k * z + η| < (q : ℤ)) :
    pqcSyndromePublicRound k y - z = pqcSyndromeRound k η := by
  unfold pqcSyndromePublicRound
  rw [pqc_syndrome_center_of_no_wrap y (k * z + η) hobs hwrap,
    pqc_syndrome_round_translate k z η hk]
  ring

/-- Strict scalar recovery uses both actual no-wrap and actual small noise. -/
theorem pqc_syndrome_public_round_correct
    {q : ℕ} [NeZero q] (k z η : ℤ) (hk : 0 < k) (y : ZMod q)
    (hobs : ((k * z + η : ℤ) : ZMod q) = y)
    (hwrap : 2 * |k * z + η| < (q : ℤ))
    (hnoise : 2 * |η| < k) :
    pqcSyndromePublicRound k y = z := by
  have h := pqc_syndrome_public_round_error k z η hk y hobs hwrap
  rw [pqc_syndrome_round_zero_of_small k η hnoise] at h
  linarith

/-- A no-division error bound for the actual public scalar output. -/
theorem pqc_syndrome_public_round_error_abs
    {q : ℕ} [NeZero q] (k z η : ℤ) (hk : 0 < k) (y : ZMod q)
    (hobs : ((k * z + η : ℤ) : ZMod q) = y)
    (hwrap : 2 * |k * z + η| < (q : ℤ)) :
    |k * (pqcSyndromePublicRound k y - z)| ≤ 2 * |η| := by
  rw [pqc_syndrome_public_round_error k z η hk y hobs hwrap]
  exact pqc_syndrome_round_displacement_abs k η hk

/-- The actual integer program satisfies `pqc_syndrome_public_round_error_energy` under the complete displayed premises. -/
theorem pqc_syndrome_public_round_error_energy
    {q : ℕ} [NeZero q] (k z η : ℤ) (hk : 0 < k) (y : ZMod q)
    (hobs : ((k * z + η : ℤ) : ZMod q) = y)
    (hwrap : 2 * |k * z + η| < (q : ℤ)) :
    k ^ 2 * (pqcSyndromePublicRound k y - z) ^ 2 ≤ 4 * η ^ 2 := by
  rw [pqc_syndrome_public_round_error k z η hk y hobs hwrap]
  exact pqc_syndrome_round_displacement_energy k η hk

/-- A deterministic vector L1 certificate for the actual public outputs.
The integer inequality |delta|<=delta^2 turns the scalar energy bounds into
a finite error-radius certificate. No error-list enumeration, probability,
or construction cost is asserted. -/
theorem pqc_syndrome_public_round_vector_l1
    {q : ℕ} [NeZero q] {J : Type} [Fintype J]
    (k : ℤ) (hk : 0 < k) (z η : J → ℤ) (y : J → ZMod q) (L : ℕ)
    (hobs : ∀ i, ((k * z i + η i : ℤ) : ZMod q) = y i)
    (hwrap : ∀ i, 2 * |k * z i + η i| < (q : ℤ))
    (hbudget : 4 * (∑ i : J, (η i) ^ 2) ≤ k ^ 2 * (L : ℤ)) :
    (∑ i : J, |pqcSyndromePublicRound k (y i) - z i|) ≤ (L : ℤ) := by
  have hpos : 0 < k ^ 2 := by simpa only [pow_two] using mul_pos hk hk
  refine Int.le_of_mul_le_mul_left ?_ hpos
  calc
    k ^ 2 * (∑ i : J, |pqcSyndromePublicRound k (y i) - z i|) =
        ∑ i : J, k ^ 2 * |pqcSyndromePublicRound k (y i) - z i| := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i : J, 4 * (η i) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      calc
        k ^ 2 * |pqcSyndromePublicRound k (y i) - z i| ≤
            k ^ 2 * (pqcSyndromePublicRound k (y i) - z i) ^ 2 := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg k)
          simpa only [sq_abs] using
            Int.le_self_sq |pqcSyndromePublicRound k (y i) - z i|
        _ ≤ 4 * (η i) ^ 2 :=
          pqc_syndrome_public_round_error_energy k (z i) (η i) hk (y i)
            (hobs i) (hwrap i)
    _ = 4 * (∑ i : J, (η i) ^ 2) := by rw [Finset.mul_sum]
    _ ≤ k ^ 2 * (L : ℤ) := hbudget

end Qatlib.Foundations.FinitePrecision.ComputableInput.ModularRounding
