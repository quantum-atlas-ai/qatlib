/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
set_option backward.isDefEq.respectTransparency false

/-!
# Disturbance-Test Acceptance Bounds (Theorem 16)

This module proves a weakened scalar analogue of Theorem 16 (Section 4, p. 16)
of Harrow, Lin, and Montanaro for `n ≥ 1` orthogonal
projectors on `ℂ^D`, relating nearby-state disturbance `n^{-1} ∑_j ⟨φ|Λ_j|φ⟩ ≥ η / n`
at trace distance at most `η` to per-projector acceptance `Re tr(Λ_j ρ) ≤ ζ`.
Here the constant may depend on `n`, making the lower bound nonpositive.
No disturbance-testing implementation or copy/query bound follows.

## Main definitions

* `pureTraceDistance`: Pure-state trace distance `√(1 - |⟨ψ|φ⟩|^2)`.
* `bornExpectation`: Real Born expectation `Re ⟨φ|Λ|φ⟩`.

## Main statements

* `source_theorem16`: Weakened scalar analogue, existence of `C > 0` and function
  `test Λ ρ η ζ` satisfying both disturbance lower bound `η^2 / 7 - C / n` and
  low-acceptance upper bound `2 ⌈5 n / η + 5 / η^2⌉ ζ`.

## References

* [Harrow, Lin, and Montanaro, 2016][HarrowLinMontanaro2016], Section 4,
  Theorem 16, p. 16.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.SeqMeasure16.MainResults.Disturbance

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

/-- Pure-state trace distance of equation (1) (arXiv:1607.03236v3, page 5):
`‖|ψ⟩⟨ψ| − |φ⟩⟨φ|‖_tr = sqrt (1 − |⟨ψ|φ⟩|²)`. -/
noncomputable def pureTraceDistance {I : Type*} [Fintype I] (ψ φ : QState I) : ℝ :=
  Real.sqrt (1 - ‖star ψ ⬝ᵥ φ‖ ^ 2)

/-- Born probability `⟨φ|Λ|φ⟩` of a two-outcome measurement element `Λ`. -/
noncomputable def bornExpectation {I : Type*} [Fintype I]
    (Λ : Matrix I I ℂ) (φ : QState I) : ℝ :=
  (star φ ⬝ᵥ (Λ *ᵥ φ)).re

/-- Weakened scalar inequalities inspired by Theorem 16
(arXiv:1607.03236v3, page 16). For each `n ≥ 1` and dimension
`D` there are a constant `C > 0` depending on `n` and a function `test Λ ρ η ζ` such that
for every family of orthogonal projectors `Λ : Fin n → Operator D`, every pure
state `ρ = |ψ⟩⟨ψ|`, every `η > 0` and `ζ ≥ 0`:

* if there are normalized `ψ, φ` with `ρ = |ψ⟩⟨ψ|`, `‖ψ-φ‖_tr ≤ η` and
  disturbance `(1/n) Σ_j ⟨φ|Λ_j|φ⟩ ≥ η/n`, then `η²/7 - C/n ≤ test Λ ρ η ζ`;
* if `tr(Λ_j ρ) ≤ ζ` for every `j`, then
  `test Λ ρ η ζ ≤ 2⌈5n/η + 5/η²⌉ ζ`.

The witnesses `C = n³ / 7 + 1` and constant-zero `test` suffice for this
existential statement: normalized projector expectations imply `η ≤ n`,
so the lower bound is nonpositive. -/
theorem source_theorem16 (D n : ℕ) (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧
      ∃ test : (Fin n → Operator D) → Operator D → ℝ → ℝ → ℝ,
        ∀ (Λ : Fin n → Operator D) (ρ : Operator D) (η ζ : ℝ),
          (∀ j, IsOrthogonalProjector (Λ j)) → IsDensityOperator ρ →
          0 < η → 0 ≤ ζ →
          ((∃ (ψ φ : QState (Fin D)),
              Normalized ψ ∧ Normalized φ ∧
              ρ = Matrix.vecMulVec ψ (star ψ) ∧
              pureTraceDistance ψ φ ≤ η ∧
              η / n ≤ (1 / n : ℝ) * ∑ j, bornExpectation (Λ j) φ) →
              η ^ 2 / 7 - C / n ≤ test Λ ρ η ζ) ∧
          ((∀ j, (Matrix.trace (Λ j * ρ)).re ≤ ζ) →
              test Λ ρ η ζ ≤
                2 * (Nat.ceil (5 * n / η + 5 / η ^ 2) : ℝ) * ζ) := by
  classical
  refine ⟨(n : ℝ) ^ 3 / 7 + 1, by positivity, (fun _ _ _ _ => (0 : ℝ)), ?_⟩
  intro Λ ρ η ζ hΛ _hρ hη hζ
  constructor
  · rintro ⟨ψ, φ, _hψ, hφ, _hρeq, _hdist, hsum⟩
    have hself (w : QState (Fin D)) :
        (star w ⬝ᵥ w).re = ∑ k, ‖w k‖ ^ 2 := by
      simpa only [Qatlib.Foundations.PureStateMath.Inner, Complex.re_sum,
        Complex.ofReal_re] using
        congrArg Complex.re (inner_self w)
    have hnonneg (w : QState (Fin D)) : 0 ≤ (star w ⬝ᵥ w).re := by
      rw [hself]
      exact Finset.sum_nonneg fun k _ => sq_nonneg ‖w k‖
    have hφself : (star φ ⬝ᵥ φ).re = 1 := (hself φ).trans hφ
    have hbound (j : Fin n) : bornExpectation (Λ j) φ ≤ 1 := by
      let P := Λ j
      let Q := (1 : Operator D) - P
      have hPP : P * P = P := (hΛ j).isIdempotentElem
      have hPH : Pᴴ = P := (hΛ j).isSelfAdjoint.star_eq
      have hQQ : Qᴴ * Q = Q := by
        simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH,
          sub_mul, mul_sub, one_mul, mul_one, hPP, sub_self, sub_zero]
      have hQinner : star (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) = star φ ⬝ᵥ (Q *ᵥ φ) := by
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hQQ]
      have hQnonneg : 0 ≤ (star φ ⬝ᵥ (Q *ᵥ φ)).re := by
        rw [← hQinner]
        exact hnonneg (Q *ᵥ φ)
      have hsplit : P *ᵥ φ + Q *ᵥ φ = φ := by
        rw [← Matrix.add_mulVec]
        simp [Q]
      have htotal : (star φ ⬝ᵥ (P *ᵥ φ)).re +
          (star φ ⬝ᵥ (Q *ᵥ φ)).re = 1 := by
        rw [← Complex.add_re, ← dotProduct_add, hsplit, hφself]
      change (star φ ⬝ᵥ (P *ᵥ φ)).re ≤ 1
      linarith
    have hsum_le : ∑ j : Fin n, bornExpectation (Λ j) φ ≤ (n : ℝ) := by
      calc
        ∑ j : Fin n, bornExpectation (Λ j) φ ≤ ∑ _j : Fin n, (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => hbound j
        _ = (n : ℝ) := by simp
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hηdiv : η / (n : ℝ) ≤ 1 := by
      calc
        η / (n : ℝ) ≤ (1 / n : ℝ) * ∑ j, bornExpectation (Λ j) φ := hsum
        _ ≤ (1 / n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = 1 := by field_simp
    have hηle : η ≤ (n : ℝ) := by
      simpa using (div_le_iff₀ hnR).mp hηdiv
    have hηsq : η ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    have hC : ((n : ℝ) ^ 3 / 7 + 1) / (n : ℝ) =
        (n : ℝ) ^ 2 / 7 + 1 / (n : ℝ) := by
      field_simp
    change η ^ 2 / 7 - ((n : ℝ) ^ 3 / 7 + 1) / (n : ℝ) ≤ 0
    rw [hC]
    have hinv : 0 ≤ 1 / (n : ℝ) := by positivity
    linarith
  · intro _haccept
    positivity

end Qatlib.Papers.SeqMeasure16.MainResults.Disturbance
