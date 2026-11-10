/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMedianStats98.MainResults.Model.Basic
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SharpMarkovDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
open Qatlib.Papers.QMedianStats98.MainResults.Model
open Qatlib.Concepts.QueryComplexity.DegreeMethod

theorem lemma_2_1_case_a {d n : ℕ} {Δ C : ℝ} (hΔ : 0 < Δ) (hC0 : 0 ≤ C) (hC2 : C < 2)
    (p : Polynomial ℝ) (hdeg : p.natDegree ≤ d)
    (hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ C)
    {a : ℝ} (ha : a ∈ Set.Icc (-1 : ℝ) 1)
    (hderiv : (n : ℝ) / (6 * Δ) ≤ |p.derivative.eval a|) :
    Real.sqrt ((n : ℝ) / (12 * Δ)) ≤ (d : ℝ) := by
  have hM := sharp_markov_derivative d p C hdeg hC0 hb a ha
  have h1 : (n : ℝ) / (6 * Δ) ≤ (d : ℝ) ^ 2 * C := le_trans hderiv hM
  have h2 : (d : ℝ) ^ 2 * C ≤ (d : ℝ) ^ 2 * 2 := by
    exact mul_le_mul_of_nonneg_left (le_of_lt hC2) (sq_nonneg (d : ℝ))
  have hkey : (n : ℝ) / (12 * Δ) ≤ (d : ℝ) ^ 2 := by
    have heq : (n : ℝ) / (12 * Δ) = ((n : ℝ) / (6 * Δ)) / 2 := by
      field_simp
      ring
    rw [heq]
    linarith
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact (Real.sqrt_le_iff).mpr ⟨hd0, hkey⟩

end Qatlib.Papers.QMedianStats98.MainResults.DegreeLowerBound
