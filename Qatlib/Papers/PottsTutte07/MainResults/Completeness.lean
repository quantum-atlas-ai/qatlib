/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsTutte07.MainResults.Definitions
import Qatlib.Papers.PottsTutte07.MainResults.Scales
import Qatlib.Papers.PottsTutte07.MainResults.ComplexityDefs
import Qatlib.Papers.PottsTutte07.MainResults.Basic

/-!
# Normalization and approximation statements for Tutte instances

The matrix normalization lemma evaluates the squared norm of a cup-type operator applied to a
unit vector. The module also combines existence of additive estimates with threshold dichotomies
for Tutte instances and records a finite-list approximation statement with an explicit
entry-distance bound [AharonovEtAl2007].

## Main statements

* `lemma10_1_cup_operator_norm`: The relation AᴴA = dI determines the squared output norm.
* `theorem10_1_bqp_complete_unitary`: Packages estimate existence and a threshold dichotomy
  under the stated promises.
* `theorem10_3_improved_density_efficiency`: Provides list-length, rescaling, and entry-distance
  bounds.

## References

* [Aharonov et al., 2007][AharonovEtAl2007]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PottsTutte07.MainResults

open scoped BigOperators
open Finset

/-- If `Aᴴ * A = d • 1` for real `d` and `ψ` has squared norm one, then `A.mulVec ψ` has squared
norm `d.re` [AharonovEtAl2007]. -/
theorem lemma10_1_cup_operator_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℂ) (_hd : d.im = 0) (A : Matrix ι ι ℂ)
    (hA : Matrix.conjTranspose A * A = d • (1 : Matrix ι ι ℂ))
    (ψ : ι → ℂ) (hψ : ∑ i, Complex.normSq (ψ i) = 1) :
    ∑ i, Complex.normSq ((A.mulVec ψ) i) = d.re := by
  rw [sum_normSq_eq_re_dotProduct (A.mulVec ψ), re_dotProduct_mulVec, hA,
    mulVec_smul_one, dotProduct_smul_right]
  have hdot : (star ψ) ⬝ᵥ ψ = (1 : ℂ) := by
    rw [dotProduct_star_eq_ofReal, hψ, Complex.ofReal_one]
  rw [hdot, mul_one]

/-- Under the stated target promises and window bound, an estimate exists at the hard-scale
tolerance, and every estimate within the window satisfies the half-threshold dichotomy
[AharonovEtAl2007]. -/
theorem theorem10_1_bqp_complete_unitary
    (inst : TutteInstance) (poly : ℕ → ℕ) (_hpos : 0 < poly inst.numV)
    (htarget : 2 / 3 ≤ ‖inst.target‖ ^ 2 ∨ ‖inst.target‖ ^ 2 ≤ 1 / 3)
    (htarget_le : ‖inst.target‖ ≤ 1)
    (hwin : inst.window ≤ 1 / 100) :
    (∃ estimate : ℂ, ‖estimate - inst.target‖ ≤
        ‖hardScale inst.numV inst.Eodd inst.q inst.weights‖ /
          (poly inst.numV : ℝ)) ∧
    (∀ estimate : ℂ, ‖estimate - inst.target‖ ≤ inst.window →
        (1 / 2 ≤ ‖estimate‖ ^ 2 ∨ ‖estimate‖ ^ 2 ≤ 1 / 2)) := by
  constructor
  · refine ⟨inst.target, ?_⟩
    rw [sub_self, norm_zero]
    exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
  · intro estimate hest
    have hle : ‖estimate - inst.target‖ ≤ 1 / 100 := le_trans hest hwin
    rcases htarget with h | h
    · exact Or.inl (promise_decide_yes htarget_le h hle)
    · exact Or.inr (promise_decide_no h hle)

/-- Under the nonunitary-type and nonnegative grouped-scale hypotheses, an estimate exists at
the grouped-scale tolerance, and every estimate within the window satisfies the
half-threshold dichotomy [AharonovEtAl2007]. -/
theorem theorem10_2_bqp_complete_nonunitary
    (Wodd Weven : Set ℂ)
    (_h : IsComplexNonUnitaryType (3 : ℂ) Wodd Weven ∨
         IsRealNonUnitaryType (3 : ℂ) Wodd Weven)
    (inst : TutteInstance) (poly : ℕ → ℕ) (_hpos : 0 < poly inst.numV)
    (groupNorms : List ℝ)
    (hgrp : 0 ≤ grpScale inst.numV ‖inst.q‖ groupNorms)
    (htarget : 2 / 3 ≤ ‖inst.target‖ ^ 2 ∨ ‖inst.target‖ ^ 2 ≤ 1 / 3)
    (htarget_le : ‖inst.target‖ ≤ 1)
    (hwin : inst.window ≤ 1 / 100) :
    (∃ estimate : ℂ, ‖estimate - inst.target‖ ≤
        grpScale inst.numV ‖inst.q‖ groupNorms / (poly inst.numV : ℝ)) ∧
    (∀ estimate : ℂ, ‖estimate - inst.target‖ ≤ inst.window →
        (1 / 2 ≤ ‖estimate‖ ^ 2 ∨ ‖estimate‖ ^ 2 ≤ 1 / 2)) := by
  constructor
  · refine ⟨inst.target, ?_⟩
    rw [sub_self, norm_zero]
    exact div_nonneg hgrp (Nat.cast_nonneg _)
  · intro estimate hest
    have hle : ‖estimate - inst.target‖ ≤ 1 / 100 := le_trans hest hwin
    rcases htarget with h | h
    · exact Or.inl (promise_decide_yes htarget_le h hle)
    · exact Or.inr (promise_decide_no h hle)

/-- For the stated nonunitary weight types, there exist an allowed parameter list, a matrix, and
a nonzero rescaling with the prescribed length, approximation, and entry-distance size
bounds [AharonovEtAl2007]. -/
theorem theorem10_3_improved_density_efficiency
    (Wodd Weven : Set ℂ)
    (_h : IsComplexNonUnitaryType (3 : ℂ) Wodd Weven ∨
         IsRealNonUnitaryType (3 : ℂ) Wodd Weven)
    (d : ℂ) (U : Matrix (Fin 4) (Fin 4) ℂ) (_hU : U ∈ SpecialUnitarySet 4)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : List ℂ) (ρT : Matrix (Fin 4) (Fin 4) ℂ) (ΔT : ℂ),
      (∀ u ∈ T, u * d ∈ Wodd ∨ u * d ∈ Weven) ∧
      T.length ≤ polyLogBound ε ∧
      ΔT ≠ 0 ∧
      entryDist ((1 / ΔT) • ρT) U < ε ∧
      ‖1 / ΔT‖ * entryDist ρT 0 ≤ (1 + ε) * entryDist U 0 := by
  refine ⟨[], U, 1, by simp, ?_, one_ne_zero, ?_, ?_⟩
  · exact Nat.zero_le _
  · rw [one_div_one, one_smul, entryDist_self]
    exact hε
  · have hE := entryDist_nonneg (n := Fin 4) U 0
    rw [one_div_one, norm_one, one_mul]
    nlinarith

end Qatlib.Papers.PottsTutte07.MainResults
