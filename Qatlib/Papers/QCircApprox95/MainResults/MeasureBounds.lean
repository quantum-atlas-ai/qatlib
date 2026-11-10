/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalCircuits.MetricCover
import Qatlib.Papers.QCircApprox95.MainResults.HaarFrames
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open Qatlib.Concepts.LocalCircuits.MetricCover
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
namespace Qatlib.Papers.QCircApprox95.MainResults

def exp2 (x : ℝ) : ℝ := Real.rpow 2 x

theorem finite_cover_exp2_bound {α : Type*} (μ : OuterMeasure α)
    (S : Set α) (m : ℕ) (C : Fin m → Set α) (A B : ℝ)
    (hcover : S ⊆ ⋃ i, C i)
    (hball : ∀ i, μ (C i) ≤ ENNReal.ofReal (exp2 (-B)))
    (hcount : (m : ℝ) ≤ exp2 A) :
    μ S ≤ ENNReal.ofReal (exp2 (A - B)) := by
  calc
    _ ≤ (m : ℝ≥0∞) * ENNReal.ofReal (exp2 (-B)) :=
      finite_cover_outer_bound μ S m C _ hcover hball
    _ = ENNReal.ofReal ((m : ℝ) * exp2 (-B)) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    _ ≤ ENNReal.ofReal (exp2 A * exp2 (-B)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcount
        (Real.rpow_nonneg (by norm_num) _))
    _ = ENNReal.ofReal (exp2 (A - B)) := by
      congr 1
      simpa only [exp2, sub_eq_add_neg] using!
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) A (-B)).symm

theorem qualitative_unitary_net (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ),
      (↑F : Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) ⊆
        Matrix.unitaryGroup (Fin (2 ^ n)) ℂ ∧
      ∀ U ∈ Matrix.unitaryGroup (Fin (2 ^ n)) ℂ, ∃ V ∈ F, ‖U - V‖ < ε := by
  have hc : IsCompact (Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :
      Set (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) :=
    Qatlib.Papers.Trainability23.HaarAverages.isCompact_unitaryGroup _
  obtain ⟨F, hF, hfin, hcover⟩ := hc.finite_cover_balls hε
  refine ⟨hfin.toFinset, by simpa using hF, ?_⟩
  intro U hU
  obtain ⟨V, hV, hnear⟩ := Set.mem_iUnion₂.mp (hcover hU)
  exact ⟨V, hfin.mem_toFinset.mpr hV, by simpa only [Metric.mem_ball, dist_eq_norm] using hnear⟩

end Qatlib.Papers.QCircApprox95.MainResults
