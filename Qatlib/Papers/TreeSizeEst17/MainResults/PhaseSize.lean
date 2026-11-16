/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.TreeSizeEst17.MainResults.Bounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section


/-! # Scalar phase-to-size accuracy for arXiv:1704.06774v3 Lemma 5.
The conclusion uses the supplied spectral sandwich and phase accuracy. It does
not construct a graph, quantum walk, phase measurement, or runtime bound.
-/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.TreeSizeEst17.MainResults

/-- The scalar spectral sandwich and phase error imply the multiplicative size estimate of Lemma 5. -/
theorem source_lemma_five
    (δ n T θ θhat : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hn : 0 < n) (hT : 0 < T)
    (hθ0 : 0 < θ) (hθπ : θ < Real.pi)
    (hθh0 : 0 < θhat) (hθhπ : θhat < Real.pi / 2)
    (hσlo : (2 * n * δ⁻¹) * T ≤ 1 / Real.sin (θ / 2) ^ 2)
    (hσhi : 1 / Real.sin (θ / 2) ^ 2 ≤ (2 * n * δ⁻¹ + n) * T)
    (hclose : |θhat - θ| ≤ δ ^ (1.5 : ℝ) / (24 * Real.sqrt (3 * n * T))) :
    (1 - δ) * T ≤ 1 / ((Real.sqrt (2 * n * δ⁻¹)) ^ 2 * Real.sin (θhat / 2) ^ 2) ∧
      1 / ((Real.sqrt (2 * n * δ⁻¹)) ^ 2 * Real.sin (θhat / 2) ^ 2) ≤ (1 + δ) * T := by
  let s : ℝ := Real.sin (θ / 2)
  let t : ℝ := Real.sin (θhat / 2)
  let A : ℝ := 2 * n * δ⁻¹
  have hs : 0 < s :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hs2 : 0 < s ^ 2 := pow_pos hs _
  have hA : 0 < A := by dsimp [A]; positivity
  have hthree : 0 < 3 * n * T := by positivity
  have hthreeSqrt : 0 < Real.sqrt (3 * n * T) := Real.sqrt_pos.mpr hthree
  have hnδ : n * δ ≤ n := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hδ1.le hn.le
  have hσupper : 1 / s ^ 2 ≤ (3 * n * T) / δ := by
    calc 1 / s ^ 2 ≤ (A + n) * T := hσhi
      _ ≤ (3 * n * T) / δ := by
        apply (le_div_iff₀ hδ0).mpr
        calc ((A + n) * T) * δ = (2 * n + n * δ) * T := by
              dsimp [A]
              field_simp [hδ0.ne']
          _ ≤ (3 * n) * T := mul_le_mul_of_nonneg_right (by linarith) hT.le
          _ = 3 * n * T := rfl
  have hδsquare : δ ≤ (3 * n * T) * s ^ 2 := by
    have h := (div_le_div_iff₀ hs2 hδ0).mp hσupper
    simpa only [one_mul] using h
  have hsqrtComparison : Real.sqrt δ ≤ Real.sqrt (3 * n * T) * s := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt (3 * n * T) * s)).mp
    rw [Real.sq_sqrt hδ0.le, mul_pow, Real.sq_sqrt hthree.le]
    exact hδsquare
  have hδrpow : δ ^ (1.5 : ℝ) = δ * Real.sqrt δ := by
    rw [show (1.5 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hδ0,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hphaseScalar : δ ^ (1.5 : ℝ) / (24 * Real.sqrt (3 * n * T)) ≤ (δ / 24) * s := by
    rw [hδrpow, div_le_iff₀ (by positivity : (0 : ℝ) < 24 * Real.sqrt (3 * n * T))]
    calc δ * Real.sqrt δ ≤ δ * (Real.sqrt (3 * n * T) * s) :=
          mul_le_mul_of_nonneg_left hsqrtComparison hδ0.le
      _ = ((δ / 24) * s) * (24 * Real.sqrt (3 * n * T)) := by ring
  have hphase : |θ - θhat| ≤ (δ / 24) * Real.sin (θ / 2) := by
    rw [abs_sub_comm]
    exact hclose.trans hphaseScalar
  have hd0 := source_lemma_sixteen θ θhat (δ / 24) hθ0 hθπ hθh0 hθhπ
    (by positivity) (by linarith) hphase
  have hd : |1 / t ^ 2 - 1 / s ^ 2| ≤ (δ / 4) * (1 / s ^ 2) := by
    calc |1 / t ^ 2 - 1 / s ^ 2| ≤ 6 * (δ / 24) / s ^ 2 := hd0
      _ = (δ / 4) * (1 / s ^ 2) := by ring
  have htauLower : (1 - δ / 4) * (1 / s ^ 2) ≤ 1 / t ^ 2 := by
    have h := (abs_le.mp hd).1
    nlinarith
  have htauUpper : 1 / t ^ 2 ≤ (1 + δ / 4) * (1 / s ^ 2) := by
    have h := (abs_le.mp hd).2
    nlinarith
  have hdimension : A + n = A * (1 + δ / 2) := by
    dsimp [A]
    field_simp [hδ0.ne']
  have hδsq : δ ^ 2 ≤ δ := by
    nlinarith [mul_nonneg hδ0.le (sub_nonneg.mpr hδ1.le)]
  have hfactor : (1 + δ / 4) * (1 + δ / 2) ≤ 1 + δ := by nlinarith
  have hlower : (1 - δ) * T * A ≤ 1 / t ^ 2 := by
    calc (1 - δ) * T * A = (1 - δ) * (A * T) := by ring
      _ ≤ (1 - δ / 4) * (A * T) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hA.le hT.le)
      _ ≤ (1 - δ / 4) * (1 / s ^ 2) :=
        mul_le_mul_of_nonneg_left hσlo (by linarith)
      _ ≤ 1 / t ^ 2 := htauLower
  have hupper : 1 / t ^ 2 ≤ (1 + δ) * T * A := by
    calc 1 / t ^ 2 ≤ (1 + δ / 4) * (1 / s ^ 2) := htauUpper
      _ ≤ (1 + δ / 4) * ((A + n) * T) :=
        mul_le_mul_of_nonneg_left hσhi (by linarith)
      _ = ((1 + δ / 4) * (1 + δ / 2)) * (A * T) := by rw [hdimension]; ring
      _ ≤ (1 + δ) * (A * T) :=
        mul_le_mul_of_nonneg_right hfactor (mul_nonneg hA.le hT.le)
      _ = (1 + δ) * T * A := by ring
  have hest : 1 / ((Real.sqrt A) ^ 2 * t ^ 2) = (1 / t ^ 2) / A := by
    rw [Real.sq_sqrt hA.le, div_div]
    congr 1
    ring
  change (1 - δ) * T ≤ 1 / ((Real.sqrt A) ^ 2 * t ^ 2) ∧
    1 / ((Real.sqrt A) ^ 2 * t ^ 2) ≤ (1 + δ) * T
  rw [hest]
  exact ⟨(le_div_iff₀ hA).mpr hlower, (div_le_iff₀ hA).mpr hupper⟩

end Qatlib.Papers.TreeSizeEst17.MainResults
