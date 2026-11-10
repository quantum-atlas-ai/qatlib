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

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace

namespace Qatlib.Papers.MolEnergySim06.MainResults

def AdiabaticSlowEnough {E : Type*} [NormedAddCommGroup E] (ψ φ : E) (δ : ℝ) : Prop :=
  ‖ψ - φ‖ ≤ δ

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

theorem asp_squared_overlap_ge {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    {δ : ℝ} (hslow : AdiabaticSlowEnough ψ φ δ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    1 - δ ^ 2 ≤ ‖⟪ψ, φ⟫_ℂ‖ ^ 2 :=
  squared_overlap_lower_bound hψ hφ hslow hδ0 hδ1

def stretchedH2HFSquaredOverlap : ℚ := 1 / 2

theorem stretched_h2_asp_improves {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {ψ φ : E} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1)
    (hslow : AdiabaticSlowEnough ψ φ (1 / 2)) :
    (1 / 2 : ℝ) < ‖⟪ψ, φ⟫_ℂ‖ ^ 2 := by
  have h := squared_overlap_lower_bound hψ hφ hslow (by norm_num) (by norm_num)
  linarith

theorem stretchedH2HFSquaredOverlap_lt_asp_target :
    stretchedH2HFSquaredOverlap < 3 / 4 := by
  unfold stretchedH2HFSquaredOverlap
  norm_num

def adiabaticRampScale (C g : ℝ) : ℝ := C / g ^ 2

theorem adiabaticRampScale_pos {C g : ℝ} (hC : 0 < C) (hg : 0 < g) :
    0 < adiabaticRampScale C g := by
  unfold adiabaticRampScale
  positivity

end Qatlib.Papers.MolEnergySim06.MainResults
