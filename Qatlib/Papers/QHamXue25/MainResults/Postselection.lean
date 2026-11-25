/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-!
# Norms in homotopy postselection

The target block is the sum of the homotopy terms. The other blocks satisfy
the source componentwise norm estimate. Their binomial sum reduces to a
geometric series with ratio `α + ‖U 0‖`. The target norm divided by the joint norm
is the square root of the postselection probability.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.QHamXue25.MainResults

/-- The finite geometric sum is bounded by its convergent infinite series. -/
private theorem geom_sum_upper {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (m : ℕ) :
    (∑ j ∈ Finset.range m, q ^ j) ≤ (1 - q)⁻¹ := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := q)
    (by rwa [Real.norm_of_nonneg hq0])
  rw [← hg.tsum_eq]
  exact hg.summable.sum_le_tsum _ (fun j _ => pow_nonneg hq0 _)

/-- Equation (65)'s initial-term comparison follows from the geometric bounds
on the remaining orders. -/
theorem homotopy_solution_norm_bounds {E : Type*} [NormedAddCommGroup E]
    (U : ℕ → E) (m : ℕ) (α : ℝ) (ha0 : 0 ≤ α) (ha1 : α < 1)
    (hterms : ∀ i, ‖U i‖ ≤ α ^ i * ‖U 0‖) :
    (1 - 2 * α) / (1 - α) * ‖U 0‖ ≤ ‖∑ i ∈ Finset.range (m + 1), U i‖ ∧
      ‖∑ i ∈ Finset.range (m + 1), U i‖ ≤ (1 - α)⁻¹ * ‖U 0‖ := by
  let Y := ∑ i ∈ Finset.range (m + 1), U i
  let R := ∑ i ∈ Finset.range m, U (i + 1)
  have hYR : Y = U 0 + R := by dsimp [Y, R]; rw [Finset.sum_range_succ']; ac_rfl
  have hR : ‖R‖ ≤ α / (1 - α) * ‖U 0‖ := calc
    ‖R‖ ≤ ∑ i ∈ Finset.range m, ‖U (i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range m, α ^ (i + 1) * ‖U 0‖ :=
      Finset.sum_le_sum (fun i _ => hterms (i + 1))
    _ = (∑ i ∈ Finset.range m, α ^ i) * (α * ‖U 0‖) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ]; ring)
    _ ≤ (1 - α)⁻¹ * (α * ‖U 0‖) :=
      mul_le_mul_of_nonneg_right (geom_sum_upper ha0 ha1 m) (mul_nonneg ha0 (norm_nonneg _))
    _ = _ := by ring
  have hU : ‖U 0‖ ≤ ‖Y‖ + ‖R‖ := by
    have hh := norm_sub_le Y R
    rw [show Y - R = U 0 by rw [hYR, add_sub_cancel_right]] at hh
    exact hh
  constructor
  · change _ ≤ ‖Y‖
    have hcoef : (1 - 2 * α) / (1 - α) = 1 - α / (1 - α) := by
      field_simp [ne_of_gt (sub_pos.mpr ha1)]
      ring
    rw [hcoef, sub_mul, one_mul]
    linarith
  · calc
      ‖Y‖ ≤ ∑ i ∈ Finset.range (m + 1), ‖U i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (m + 1), α ^ i * ‖U 0‖ :=
        Finset.sum_le_sum (fun i _ => hterms i)
      _ ≤ _ := by rw [← Finset.sum_mul]; exact
        mul_le_mul_of_nonneg_right (geom_sum_upper ha0 ha1 (m + 1)) (norm_nonneg _)

/-- The source block norm bounds imply Eq. (68) for the square root of the
postselection probability. -/
theorem homotopy_postselection_bound {E : Type*} [NormedAddCommGroup E]
    (U : ℕ → E) (m : ℕ) (α : ℝ) (ha0 : 0 ≤ α) (ha2 : α < 1 / 2)
    (hu0 : 0 < ‖U 0‖) (hconv : α + ‖U 0‖ < 1)
    (hterms : ∀ i, ‖U i‖ ≤ α ^ i * ‖U 0‖)
    (block : ℕ → ℕ → ℝ) (D : ℝ) (hD0 : 0 < D)
    (hblock : ∀ j < m + 1, ∀ i < j + 1,
        block j i ≤ (j.choose i : ℝ) * α ^ (j - i) * ‖U 0‖ ^ (i + 1))
    (hD : D ≤ ‖∑ i ∈ Finset.range (m + 1), U i‖ +
      ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1), block j i) :
    (1 - 2 * α) * (1 - α - ‖U 0‖) / (2 - 2 * α - ‖U 0‖) ≤
      Real.sqrt (‖∑ i ∈ Finset.range (m + 1), U i‖ ^ 2 / D ^ 2) := by
  let u := ‖U 0‖
  let N := ‖∑ i ∈ Finset.range (m + 1), U i‖
  let s := 1 - α
  let t := 1 - α - u
  have hs : 0 < s := by dsimp [s]; linarith
  have ht : 0 < t := by dsimp [t, u]; linarith
  have ha1 : α < 1 := ha2.trans (by norm_num)
  have hnum := homotopy_solution_norm_bounds U m α ha0 ha1 hterms
  have hblocks : (∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1), block j i) ≤
      t⁻¹ * u := by
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * α ^ (j - i) * u ^ (i + 1) :=
        Finset.sum_le_sum fun j hj =>
          Finset.sum_le_sum fun i hi => hblock j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi)
      _ = (∑ j ∈ Finset.range (m + 1), (u + α) ^ j) * u := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [add_pow, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_succ]
        ring
      _ ≤ _ := by
        have h := geom_sum_upper (show 0 ≤ u + α by positivity) (show u + α < 1 by
          dsimp [u]; linarith) (m + 1)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        convert h using 1
        ring
  have hDup : D ≤ (s⁻¹ + t⁻¹) * u := by
    have hh := hD.trans (add_le_add hnum.2 hblocks)
    simpa [s, mul_add, add_mul] using hh
  have hNlo : (1 - 2 * α) / s * u ≤ N := hnum.1
  have hp : 0 ≤ N / D := div_nonneg (norm_nonneg _) hD0.le
  change (1 - 2 * α) * t / (2 - 2 * α - u) ≤ Real.sqrt (N ^ 2 / D ^ 2)
  rw [← div_pow, Real.sqrt_sq hp]
  have hscale : (1 - 2 * α) / s * u / ((s⁻¹ + t⁻¹) * u) =
      (1 - 2 * α) * t / (2 - 2 * α - u) := by
    have hu : u ≠ 0 := hu0.ne'
    have hst : s + t ≠ 0 := (add_pos hs ht).ne'
    rw [show 2 - 2 * α - u = s + t by dsimp [s,t]; ring]
    field_simp [hs.ne', ht.ne', hu, hst]
    ring
  rw [← hscale]
  calc
    _ ≤ N / ((s⁻¹ + t⁻¹) * u) := div_le_div_of_nonneg_right hNlo (by positivity)
    _ ≤ N / D := div_le_div_of_nonneg_left (norm_nonneg _) hD0 hDup

end Qatlib.Papers.QHamXue25.MainResults
