/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2
import Qatlib.Papers.QConvexOpt18.MainResults.FiniteDiff.SourceFiniteDiff

set_option backward.isDefEq.respectTransparency false

/-!
# QConvexOpt18 Lemma 10: how far a subgradient is from the finite-difference gradient

van Apeldoorn--Gilyén--Gribling--de Wolf, fixed arXiv:1809.00643v4
(accepted in Quantum 2019-12-03), Lemma 10.

Lemma 10. If `r2 > 0`, `z ∈ ℝ^n`, and `f : B₁(z, r2) → ℝ` is convex, then
`sup_{g ∈ ∂̲f(z)} ‖g - ∇^(r2) f (z)‖₁ ≤ r2 Δ^(r2) f (z) / 2`.

The proof is the source's argument, coordinate by coordinate. Fix a subgradient `g` and `i`.
Convexity gives `f (z + r2 eᵢ) ≥ f z + r2 gᵢ` and `f (z - r2 eᵢ) ≥ f z - r2 gᵢ`, i.e.
`Aᵢ := (f z - f (z - r2 eᵢ)) / r2 ≤ gᵢ ≤ Bᵢ := (f (z + r2 eᵢ) - f z) / r2`. For any three reals
`A ≤ g ≤ B` one has `|g - (A + B)/2| ≤ (B - A)/2`; here `(Aᵢ + Bᵢ)/2 = ∇ᵢ^(r2) f (z)` and
`Bᵢ - Aᵢ = r2 Δᵢ^(r2) f (z)`. Summing `|gᵢ - ∇ᵢ^(r2) f (z)| ≤ r2 Δᵢ^(r2) f (z) / 2` over `i`
and using `Δ^(r2) f (z) = ∑ᵢ Δᵢ^(r2) f (z)` gives the `ℓ₁` bound.

The hypothesis `ConvexOn` is what makes `∂̲f(z)` the paper's subdifferential; the chain above only
consumes the subgradient inequalities on `B₁(z, r2)`, which is the source's `B₁` (the `ℓ₁` ball, here
recorded through the sup-norm ball of `ℓ₁`-norm points by `norm_le_l1Norm`).

`sum_mul_coordVec` records the coordinate functional `⟨g, eᵢ⟩ = gᵢ`.

Boundary: a pointwise inequality about one subgradient and one finite-difference gradient. It does
not assert that a subgradient exists, and it carries no probability or query model.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QConvexOpt18.MainResults

open scoped BigOperators

/-- The coordinate functional `⟨g, eᵢ⟩ = gᵢ` against the coordinate vector of Definition 8. -/
theorem sum_mul_coordVec {n : ℕ} (g : Fin n → ℝ) (i : Fin n) :
    ∑ j, g j * coordVec i j = g i := by
  simp only [coordVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  simp

/-- The two difference points `z ± r2 eᵢ` lie in the sup-norm ball `B_∞(z, r2) = B₁(z, r2)` of
Definition 8, because `‖r2 eᵢ‖_∞ = r2`. -/
theorem coordVec_smul_mem_closedBall {n : ℕ} (z : Fin n → ℝ) {r2 : ℝ} (hr : 0 ≤ r2)
    (i : Fin n) :
    z + r2 • coordVec i ∈ Metric.closedBall z r2 ∧
      z - r2 • coordVec i ∈ Metric.closedBall z r2 := by
  have hnorm : ‖r2 • coordVec i‖ = r2 := by
    rw [norm_smul, Real.norm_eq_abs, coordVec, Pi.norm_single, abs_of_nonneg hr]
    simp
  constructor
  · rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hnorm]
  · rw [Metric.mem_closedBall, dist_eq_norm]
    have hsub : z - r2 • coordVec i - z = -(r2 • coordVec i) := by abel
    rw [hsub, norm_neg, hnorm]

/-- Lemma 10 of arXiv:1809.00643v4. Every subgradient `g` of a convex `f` at `z` is within
`r2 Δ^(r2) f (z) / 2` of the finite-difference gradient `∇^(r2) f (z)` in the `ℓ₁` norm. -/
theorem source_subgradient_finiteDiff_gap {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z g : Fin n → ℝ)
    (r2 : ℝ) (hr : 0 < r2) (_hconv : ConvexOn ℝ (Metric.closedBall z r2) f)
    (hg : ∀ y ∈ Metric.closedBall z r2, f z + ∑ i, g i * (y i - z i) ≤ f y) :
    ∑ i, |g i - finDiffGradCoord f z r2 i| ≤ r2 * finDiffLaplace f z r2 / 2 := by
  have hcoord : ∀ i, |g i - finDiffGradCoord f z r2 i| ≤
      r2 * finDiffLaplaceCoord f z r2 i / 2 := by
    intro i
    obtain ⟨hmem₂, hmem₁⟩ := coordVec_smul_mem_closedBall (n := n) z hr.le i
    -- the upper one-sided difference dominates `gᵢ`
    have hup : g i ≤ (f (z + r2 • coordVec i) - f z) / r2 := by
      have h := hg (z + r2 • coordVec i) hmem₂
      have hsum : ∑ j, g j * ((z + r2 • coordVec i) j - z j) = r2 * g i := by
        have hterm : ∀ j, (z + r2 • coordVec i) j - z j = r2 * coordVec i j := by
          intro j; simp
        have hfac : ∀ j, g j * (r2 * coordVec i j) = r2 * (g j * coordVec i j) :=
          fun j => by ring
        simp only [hterm, hfac, ← Finset.mul_sum, sum_mul_coordVec]
      rw [hsum] at h
      rw [le_div_iff₀ hr]
      linarith
    -- the lower one-sided difference is dominated by `gᵢ`
    have hlow : (f z - f (z - r2 • coordVec i)) / r2 ≤ g i := by
      have h := hg (z - r2 • coordVec i) hmem₁
      have hsum : ∑ j, g j * ((z - r2 • coordVec i) j - z j) = -(r2 * g i) := by
        have hterm : ∀ j, (z - r2 • coordVec i) j - z j = -(r2 * coordVec i j) := by
          intro j; simp
        have hfac : ∀ j, g j * (-(r2 * coordVec i j)) = -(r2 * (g j * coordVec i j)) :=
          fun j => by ring
        simp only [hterm, hfac, Finset.sum_neg_distrib, ← Finset.mul_sum, sum_mul_coordVec]
      rw [hsum] at h
      rw [div_le_iff₀ hr]
      linarith
    -- `|gᵢ - (Aᵢ + Bᵢ)/2| ≤ (Bᵢ - Aᵢ)/2`
    have hmid : |g i - ((f z - f (z - r2 • coordVec i)) / r2 +
        (f (z + r2 • coordVec i) - f z) / r2) / 2| ≤
        ((f (z + r2 • coordVec i) - f z) / r2 -
          (f z - f (z - r2 • coordVec i)) / r2) / 2 := by
      rw [abs_le]
      constructor <;> linarith
    have hgrad : ((f z - f (z - r2 • coordVec i)) / r2 +
        (f (z + r2 • coordVec i) - f z) / r2) / 2 = finDiffGradCoord f z r2 i := by
      rw [finDiffGradCoord]
      field_simp
      ring
    have hlap : ((f (z + r2 • coordVec i) - f z) / r2 -
        (f z - f (z - r2 • coordVec i)) / r2) / 2 =
        r2 * finDiffLaplaceCoord f z r2 i / 2 := by
      rw [finDiffLaplaceCoord]
      field_simp
      ring
    rw [hgrad, hlap] at hmid
    exact hmid
  calc ∑ i, |g i - finDiffGradCoord f z r2 i|
      ≤ ∑ i, r2 * finDiffLaplaceCoord f z r2 i / 2 :=
        Finset.sum_le_sum fun i _ => hcoord i
    _ = r2 * finDiffLaplace f z r2 / 2 := by
        rw [finDiffLaplace, Finset.mul_sum, Finset.sum_div]

end Qatlib.Papers.QConvexOpt18.MainResults
