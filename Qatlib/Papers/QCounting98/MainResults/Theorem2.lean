/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Theorem2QuadraticSpeedupRestrictedQuan
import Mathlib.Analysis.SpecificLimits.Normed
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open scoped BigOperators

theorem source_theorem2_quadratic_speedup {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (hA : A * A.conjTranspose = 1) (θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi / 2)
    (hsin : Real.sin θ ^ 2 = ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
    (ha0 : 0 < ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i)) :
    max (1 - ∑ i, Complex.normSq (goodPart g (fun i => A i 0) i))
        (∑ i, Complex.normSq (goodPart g (fun i => A i 0) i)) ≤
      ∑ i, Complex.normSq (goodPart g
        (((iterate A g (-1) (-1)) ^ Nat.floor (Real.pi / (4 * θ))).mulVec
          (fun i => A i 0)) i) :=
  zoo_counting_rankone_known_success_amplification n A g hA θ hθ0 hθπ hsin ha0

theorem source_geometric_trials {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑' k : ℕ, ((k : ℝ) + 1) * q ^ k * (1 - q)) = 1 / (1 - q) := by
  have hr : ‖q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]
    exact hq1
  have h1 : HasSum (fun k : ℕ => (k : ℝ) * q ^ k) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hr
  have h2 : HasSum (fun k : ℕ => q ^ k) ((1 - q)⁻¹) :=
    hasSum_geometric_of_norm_lt_one hr
  have hsum : HasSum (fun k : ℕ => ((k : ℝ) + 1) * q ^ k)
      (q / (1 - q) ^ 2 + (1 - q)⁻¹) := by
    have h := h1.add h2
    convert h using 1
    · ext k
      ring
  have hmul := hsum.mul_left (1 - q)
  have hval : (1 - q) * (q / (1 - q) ^ 2 + (1 - q)⁻¹) = 1 / (1 - q) := by
    have hne : (1 - q) ≠ 0 := by linarith
    field_simp
    ring
  rw [hval] at hmul
  have hfun : (fun k : ℕ => (1 - q) * (((k : ℝ) + 1) * q ^ k)) =
      fun k : ℕ => ((k : ℝ) + 1) * q ^ k * (1 - q) := by
    ext k; ring
  rw [hfun] at hmul
  exact hmul.tsum_eq

theorem source_amplification_expected_applications {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (m : ℕ) :
    (∑' k : ℕ, ((k : ℝ) + 1) * a ^ k * (1 - a)) * (2 * (m : ℝ) + 1) =
      (2 * (m : ℝ) + 1) / (1 - a) := by
  rw [source_geometric_trials ha0 ha1]
  ring

end Qatlib.Papers.QCounting98.MainResults
