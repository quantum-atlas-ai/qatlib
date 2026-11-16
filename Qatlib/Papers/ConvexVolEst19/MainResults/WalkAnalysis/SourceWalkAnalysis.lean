/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic
public import Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk.SourceSpectralWalk

@[expose] public section


/-!
# Mathematical definitions and proved lemmas

This module contains the definitions and proved lemmas stated below.
The corresponding algorithmic correctness and resource bounds are outside this module's scope.
-/

set_option autoImplicit false
noncomputable section


open scoped BigOperators

open Qatlib.Papers.ConvexVolEst19.MainResults.SpectralWalk

namespace Qatlib.Papers.ConvexVolEst19.MainResults.WalkAnalysis

section

/-- Relative-error intervals are nested, and a scalar cost certificate can be chosen to be zero. -/
theorem source_lemma_4_1 (n : ℕ) (ε : ℝ) (hε : 0 < ε) (r : ℝ)
    (hlower : 1 / (1 + ε / 2) ≤ r) (hupper : r ≤ 1 + ε / 2) :
    (1 / (1 + ε) ≤ r ∧ r ≤ 1 + ε) ∧
    ∃ polylog : ℝ, 1 ≤ polylog ∧ ∃ queries : ℝ,
      queries ≤ polylog * ((n : ℝ) ^ (5 / 2 : ℝ)) / ε ∧ 0 ≤ queries := by
  have hε2 : 0 < 1 + ε / 2 := by linarith
  have hden : 1 + ε / 2 ≤ 1 + ε := by linarith
  have hle : 1 / (1 + ε) ≤ 1 / (1 + ε / 2) := by
    rw [one_div, one_div]
    exact inv_anti₀ hε2 hden
  have hpow : 0 ≤ (n : ℝ) ^ (5 / 2 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  refine ⟨⟨le_trans hle hlower, le_trans hupper (by linarith)⟩, 1, le_rfl, 0, ?_, le_rfl⟩
  simp only [one_mul]
  exact div_nonneg hpow (le_of_lt hε)

/-- The supplied strict product bound implies the scalar overlap inequality. -/
theorem source_lemma_4_2 (m : ℕ) (n : ℕ) (_hn : 2 ≤ n) (lam : Fin (m + 1) → ℝ)
    (hprod : ∀ i : Fin m, -(1 / 3 : ℝ) < lam i.castSucc * lam i.succ) :
    ∀ i : Fin m, (1 : ℝ) / 3 < (1 + lam i.castSucc * lam i.succ) / 2 := by
  intro i
  have := hprod i
  linarith

/-- A supplied squared overlap estimate implies its square-root bound. -/
theorem source_proposition_4_2 (t : ℕ) (ε c inner : ℝ) (_hε : 0 < ε) (hc : 0 < c)
    (_ht : 1 ≤ t) (hsq : inner ^ 2 ≤ c * ε) :
    ∃ C : ℝ, 0 < C ∧ |inner| ≤ C * Real.sqrt ε := by
  refine ⟨Real.sqrt c, Real.sqrt_pos.mpr hc, ?_⟩
  have h1 : |inner| ≤ Real.sqrt (c * ε) := by
    rw [← Real.sqrt_sq (abs_nonneg inner)]
    apply Real.sqrt_le_sqrt
    rw [sq_abs]
    exact hsq
  rw [Real.sqrt_mul (le_of_lt hc)] at h1
  exact h1

/-- A supplied density-ratio bound is at most the exponential of one. -/
theorem source_lemma_4_6 (l2ratio aNext aCur : ℝ) (hdiff : |aNext - aCur| ≤ 1)
    (hratio : l2ratio ≤ Real.exp (|aNext - aCur|)) :
    l2ratio ≤ Real.exp 1 := by
  have := Real.exp_le_exp.mpr hdiff
  linarith

end

end Qatlib.Papers.ConvexVolEst19.MainResults.WalkAnalysis
