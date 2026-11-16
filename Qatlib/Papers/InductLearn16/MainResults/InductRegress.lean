/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.InductLearn16.MainResults.QuantumChannelApproximation
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder
open Matrix

namespace Qatlib.Papers.InductLearn16.MainResults

open Qatlib.Papers.InductLearn16.MainResults

/-- The legacy bad-set conclusion fails for one outcome, unit effect, and zero error.
The legacy theorem imposes no moment condition or definition of the bad event. -/
theorem badSet_counter :
    ¬ ((∑ _g ∈ (Finset.univ : Finset (Fin 1)),
          (1 : Matrix (Fin 1) (Fin 1) ℂ).trace.re) ≤
      (1 : ℝ) ^ 2 / (1 : ℝ) ^ 2 *
        (2 * (0 : ℝ) * (1 + 1 / (1 : ℝ)) + (0 : ℝ) ^ 2)) := by
  norm_num [Matrix.trace]

/-- Zero satisfies the legacy inverse-square-root equation on a normalized state.
Consequently the legacy hypotheses do not imply the maximally mixed marginal. -/
theorem twirl_counter :
    let φ : Matrix (Fin 1 × Fin 1) (Fin 1 × Fin 1) ℂ := 1
    let τ : Matrix (Fin 1) (Fin 1) ℂ := 1
    let τinv : Matrix (Fin 1) (Fin 1) ℂ := 0
    let τsqrt : Matrix (Fin 1) (Fin 1) ℂ := 1
    φ.PosSemidef ∧ τ = Matrix.traceRight φ ∧ τ.PosSemidef ∧
      τinv * τ * τinv = τinv ∧ τinv.IsHermitian ∧
      τsqrt * τsqrt = τ ∧ τsqrt.IsHermitian ∧
      Matrix.traceRight
        (((Fintype.card (Fin 1) : ℂ)⁻¹) •
          (Matrix.kronecker τinv (1 : Matrix (Fin 1) (Fin 1) ℂ) * φ *
            Matrix.kronecker τinv (1 : Matrix (Fin 1) (Fin 1) ℂ))) ≠
        maxMixedOf (Fin 1) := by
  dsimp
  refine ⟨Matrix.PosSemidef.one, ?_, Matrix.PosSemidef.one, by simp,
    Matrix.isHermitian_zero, by simp, Matrix.isHermitian_one, ?_⟩
  · ext i j
    simp [Matrix.traceRight, Matrix.one_apply]
  · intro h
    have hi := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) h
    norm_num [Matrix.traceRight, Matrix.kronecker, maxMixedOf] at hi

end Qatlib.Papers.InductLearn16.MainResults
