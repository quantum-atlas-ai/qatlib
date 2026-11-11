/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Overlap estimates for adiabatic state preparation

`AdiabaticSlowEnough` records a supplied norm-distance bound between a prepared state and its
target. For normalized vectors, this module converts that bound into a lower bound on squared
overlap, providing the quantitative overlap step used in the preparation discussion of
[AspuruGuzikEtAl2005].

The module also records a stretched-hydrogen reference overlap and the positive
inverse-gap-squared scale `adiabaticRampScale`.

## Main statements

* `squared_overlap_lower_bound`: Norm closeness within `δ ∈ [0, 1]` gives squared overlap at
  least `1 - δ^2`.
* `stretched_h2_asp_improves`: A supplied distance bound of one half gives squared overlap
  strictly greater than one half.
* `adiabaticRampScale_pos`: Positive numerator and gap give a positive ramp scale.

## References

* [Aspuru-Guzik et al., 2005][AspuruGuzikEtAl2005]
-/

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace

namespace Qatlib.Papers.MolEnergySim06.MainResults

/-- The norm-distance condition `‖ψ - φ‖ ≤ δ` between the prepared vector and its target. -/
def AdiabaticSlowEnough {E : Type*} [NormedAddCommGroup E] (ψ φ : E) (δ : ℝ) : Prop :=
  ‖ψ - φ‖ ≤ δ

/-- Two normalized vectors at norm distance at most `δ`, with `0 ≤ δ ≤ 1`, have squared
inner-product norm at least `1 - δ^2`; see [AspuruGuzikEtAl2005]. -/
theorem squared_overlap_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    {δ : ℝ} (hclose : ‖ψ - φ‖ ≤ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - δ ^ 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  have hns : ‖ψ - φ‖ ^ 2 = 2 - 2 * RCLike.re ⟪ψ, φ⟫_ℂ := by
    rw [norm_sub_sq (𝕜 := ℂ), hψ, hφ]
    ring
  have hδsq : ‖ψ - φ‖ ^ 2 ≤ δ ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hclose hclose (norm_nonneg _) hδ0
  have hre : 1 - δ ^ 2 / 2 ≤ RCLike.re ⟪ψ, φ⟫_ℂ := by
    linarith
  have hrenorm : RCLike.re ⟪ψ, φ⟫_ℂ ≤ ‖⟪ψ, φ⟫_ℂ‖ :=
    (le_abs_self _).trans (Complex.abs_re_le_norm _)
  have hδ2le : δ ^ 2 ≤ 1 := by
    simpa using pow_le_one₀ hδ0 hδ1 (n := 2)
  have hnn : 0 ≤ 1 - δ ^ 2 / 2 := by linarith
  have hsq : (1 - δ ^ 2 / 2) ^ 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 :=
    pow_le_pow_left₀ hnn (hre.trans hrenorm) 2
  have hexp : (1 - δ ^ 2 / 2) ^ 2 = 1 - δ ^ 2 + (δ ^ 2) ^ 2 / 4 := by ring
  have hnonneg : 0 ≤ (δ ^ 2) ^ 2 / 4 := by positivity
  rw [hexp] at hsq
  linarith

/-- The supplied `AdiabaticSlowEnough` distance bound for normalized vectors gives squared
overlap at least `1 - δ^2` when `δ ∈ [0, 1]`; see [AspuruGuzikEtAl2005]. -/
theorem asp_squared_overlap_ge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    {δ : ℝ} (hslow : AdiabaticSlowEnough ψ φ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - δ ^ 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 :=
  squared_overlap_lower_bound hψ hφ hslow hδ0 hδ1

/-- The rational reference squared overlap one half for the stretched-hydrogen Hartree-Fock
example. -/
def stretchedH2HFSquaredOverlap : ℚ := 1 / 2

/-- For normalized vectors satisfying the distance bound `AdiabaticSlowEnough ψ φ (1 / 2)`, the
squared overlap exceeds one half; see [AspuruGuzikEtAl2005]. -/
theorem stretched_h2_asp_improves {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hslow : AdiabaticSlowEnough ψ φ (1 / 2)) :
    (1 / 2 : ℝ) < ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  have h := squared_overlap_lower_bound hψ hφ hslow (by norm_num) (by norm_num)
  linarith

/-- The stored stretched-hydrogen reference squared overlap is strictly less than three
quarters. -/
theorem stretchedH2HFSquaredOverlap_lt_asp_target :
    stretchedH2HFSquaredOverlap < 3 / 4 := by
  unfold stretchedH2HFSquaredOverlap
  norm_num

/-- The inverse-gap-squared scale `C / g^2` for parameters `C` and `g`. -/
def adiabaticRampScale (C g : ℝ) : ℝ := C / g ^ 2

/-- The scale `adiabaticRampScale C g` is positive when both `C` and `g` are positive; see
[AspuruGuzikEtAl2005]. -/
theorem adiabaticRampScale_pos {C g : ℝ} (hC : 0 < C) (hg : 0 < g) :
    0 < adiabaticRampScale C g := by
  unfold adiabaticRampScale
  positivity

end Qatlib.Papers.MolEnergySim06.MainResults
