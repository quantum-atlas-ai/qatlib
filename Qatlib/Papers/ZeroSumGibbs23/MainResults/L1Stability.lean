/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel
public import Mathlib.Tactic

@[expose] public section


/-!
# Stability of normalized finite weights

The normalized L1 estimate holds for arbitrary real vectors. The zero-mass
second vector is treated separately, so no positivity or nonzero denominator
is hidden in the theorem.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.L1Stability
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model

/-- Perturbing every coordinate by at most `η` changes normalized weights by at most `2nη/‖w‖₁`. -/
theorem normalized_dist {n : ℕ} (w z : Fin n → ℝ) {η : ℝ}
    (hη : ∀ j, |w j - z j| ≤ η) (hW : 0 < l1Norm w) :
    l1Norm (fun j => w j / l1Norm w - z j / l1Norm z) ≤
      2 * ((n : ℝ) * η) / l1Norm w := by
  let W := l1Norm w
  let Z := l1Norm z
  let D := l1Norm (fun j => w j - z j)
  have hW' : 0 < W := hW
  have hZ0 : 0 ≤ Z := l1Norm_nonneg z
  have hD : D ≤ (n : ℝ) * η := by
    simpa [D, mul_comm] using l1Norm_le_of_abs_le hη
  by_cases hZ : Z = 0
  · have hz (j : Fin n) : z j = 0 := by
      have hle : |z j| ≤ l1Norm z :=
        Finset.single_le_sum (fun i _ => abs_nonneg (z i)) (Finset.mem_univ j)
      have hab : |z j| = 0 := by dsimp [Z] at hZ; linarith [abs_nonneg (z j)]
      exact abs_eq_zero.mp hab
    have hD' : D = W := by simp [D, W, hz, l1Norm]
    have heq : l1Norm (fun j => w j / l1Norm w - z j / l1Norm z) = 1 := by
      simp only [hz, zero_div, sub_zero]
      change (∑ j, |w j / l1Norm w|) = 1
      simp only [abs_div, abs_of_pos hW]
      rw [← Finset.sum_div]
      exact div_self hW.ne'
    rw [heq]
    apply (le_div_iff₀ hW).mpr
    simp only [one_mul]
    change W ≤ 2 * ((n : ℝ) * η)
    rw [hD'] at hD
    linarith
  · have hZ' : 0 < Z := lt_of_le_of_ne hZ0 (Ne.symm hZ)
    have htri1 : W ≤ D + Z := by
      change (∑ j, |w j|) ≤ (∑ j, |w j - z j|) + ∑ j, |z j|
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun j _ => by simpa using abs_add_le (w j - z j) (z j)
    have htri2 : Z ≤ D + W := by
      change (∑ j, |z j|) ≤ (∑ j, |w j - z j|) + ∑ j, |w j|
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      have h := abs_add_le (z j - w j) (w j)
      simpa [abs_sub_comm] using h
    have hrev : |Z - W| ≤ D := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsplit (j : Fin n) : w j / W - z j / Z =
        (w j - z j) / W + z j * ((Z - W) / (W * Z)) := by
      field_simp
      ring
    have hsum : l1Norm (fun j => w j / W - z j / Z) ≤
        D / W + Z * |Z - W| / (W * Z) := by
      unfold l1Norm
      calc
        (∑ j, |w j / W - z j / Z|) ≤
            ∑ j, (|w j - z j| / W + |z j| * |Z - W| / (W * Z)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [hsplit]
          have h := abs_add_le ((w j - z j) / W) (z j * ((Z - W) / (W * Z)))
          simpa only [abs_div, abs_mul, abs_of_pos hW', abs_of_pos hZ', mul_div_assoc] using h
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div, ← Finset.sum_mul]
          rfl
    change l1Norm (fun j => w j / W - z j / Z) ≤ 2 * ((n : ℝ) * η) / W
    calc
      _ ≤ D / W + Z * |Z - W| / (W * Z) := hsum
      _ = (D + |Z - W|) / W := by field_simp
      _ ≤ 2 * ((n : ℝ) * η) / W :=
        div_le_div_of_nonneg_right (by linarith) hW'.le

end Qatlib.Papers.ZeroSumGibbs23.MainResults.L1Stability
