/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SwitchAdiab12.MainResults.ExpansionModel
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section


/-! # A noncontractive idempotent satisfying the literal expansion interface

The source spectral projection has analytic and geometric structure absent
from the old `IsProjection` predicate. This concrete instance diagnoses that
interface; it does not refute the source operator theorem.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.SwitchAdiab12.MainResults.ProjectionProbe
open ExpansionModel

/-- A shear projection on the product equipped with its ordinary maximum norm. -/
def shear : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ +
    (12 : ℂ) • ContinuousLinearMap.snd ℂ ℂ ℂ).prod 0

/-- Its concrete action makes both idempotence and noncontractivity visible. -/
theorem shearApply (x : ℂ × ℂ) : shear x = (x.1 + 12 * x.2, 0) := by
  simp [shear]

/-- The shear is a genuine idempotent bounded operator. -/
theorem shearIdem : shear * shear = shear := by
  apply ContinuousLinearMap.ext
  intro x
  simp [mul_apply_eq_comp, shearApply]

/-- Its operator norm is at least twelve, by applying it to the unit second vector. -/
theorem shearLarge : (12 : ℝ) ≤ ‖shear‖ := by
  have h := shear.le_opNorm ((0 : ℂ), 1)
  norm_num [shearApply, Prod.norm_def] at h
  exact h

/-- A closed family with this projection and no higher expansion coefficients. -/
def badData : ExpansionData ((ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) where
  H := fun _ => 0
  P := fun _ => shear
  Eeig := fun _ => 0
  g := 1
  B := fun n _ => if n = 0 then shear else 0

/-- The old Gevrey condition is satisfied by the genuinely constant zero Hamiltonian. -/
theorem badGevrey : badData.IsGevrey 2 1 1 := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · simp [badData]
  · intro k hk s _
    change ‖iteratedDeriv k (fun _ : ℝ =>
      (0 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))) s‖ ≤
        (1 : ℝ) * 1 ^ k * (k : ℝ) ^ ((2 : ℝ) * (k : ℝ))
    rw [iteratedDeriv_const, ite_eq_right (by omega : k ≠ 0)]
    simpa only [norm_zero, one_pow, one_mul] using
      Real.rpow_nonneg (Nat.cast_nonneg k) ((2 : ℝ) * (k : ℝ))

/-- Idempotence is exactly the complete old projection promise. -/
theorem badProjection : badData.IsProjection := by
  intro s
  exact shearIdem

/-- The zero Hamiltonian has the required actual resolvent everywhere on the circle. -/
theorem badResolvent : badData.ResolventBound := by
  refine ⟨by norm_num [badData], ?_⟩
  intro s _ z hz
  have hzNorm : ‖z‖ = (1 / 2 : ℝ) := by simpa [badData] using hz
  have hz0 : z ≠ 0 := by
    intro he
    subst z
    norm_num at hzNorm
  refine ⟨(-z)⁻¹ • 1, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro x
    change 0 - z • ((-z)⁻¹ • x) = x
    rw [zero_sub, ← neg_smul, smul_smul,
      mul_inv_cancel₀ (neg_ne_zero.mpr hz0), one_smul]
  · apply ContinuousLinearMap.ext
    intro x
    change (-z)⁻¹ • (0 - z • x) = x
    rw [zero_sub, ← neg_smul, smul_smul,
      inv_mul_cancel₀ (neg_ne_zero.mpr hz0), one_smul]
  · change ‖(-z)⁻¹ • (1 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))‖ ≤ 2 / 1
    rw [norm_smul, norm_inv, norm_neg, hzNorm, norm_one]
    norm_num

/-- Constant coefficients meet every differential and algebraic hierarchy equation. -/
theorem badHierarchy : badData.SolvesHierarchy := by
  refine ⟨by simp [badData], ?_, ?_⟩
  · intro j s
    by_cases hj : j = 0
    · simpa [badData, hj] using hasDerivAt_const s shear
    · simpa [badData, hj] using
        hasDerivAt_const s (0 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
  · intro j s
    by_cases hj : j = 0
    · subst j
      simpa [badData] using shearIdem.symm
    · change (if j = 0 then shear else 0) = _
      rw [ite_eq_right hj]
      symm
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : m = 0
      · subst m
        simp [badData, hj]
      · simp [badData, hm]

/-- At n=k=0, the literal legacy estimate fails on this fully specified model. -/
theorem badEstimate : ¬ (
    ‖iteratedDeriv 0 (badData.B 0) (0 : ℝ)‖ ≤
      (1 / (10 * (0 : ℝ) + 0.3) ^ 2) *
        badData.g ^ (-(2 * (0 : ℝ) + (0 : ℝ))) *
          (2 * (1 : ℝ) * 1 * ((0 : ℝ) + 3 * (0 : ℝ)) ^ (2 * (2 : ℝ))) ^
            (0 + 3 * (0 : ℕ))) := by
  intro h
  norm_num [badData] at h
  have hlow := shearLarge
  linarith

/-- All four old premises are satisfiable together with failure of their proposed base case. -/
theorem badWitness : badData.IsGevrey 2 1 1 ∧ badData.IsProjection ∧
    badData.ResolventBound ∧ badData.SolvesHierarchy ∧
    ¬ ‖badData.B 0 (0 : ℝ)‖ ≤ (100 / 9 : ℝ) := by
  refine ⟨badGevrey, badProjection, badResolvent, badHierarchy, ?_⟩
  change ¬ ‖shear‖ ≤ (100 / 9 : ℝ)
  have h := shearLarge
  linarith
end Qatlib.Papers.SwitchAdiab12.MainResults.ProjectionProbe
