/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QcaDynamics.ParityWeights
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false
noncomputable section

open Complex Qatlib.Concepts.QcaDynamics.ParityWeights

namespace Qatlib.Papers.QCellAutomata96.MainResults

set_option maxHeartbeats 1000000 in

theorem eq24_satisfies_constraints (θ ρ : ℝ) :
    Eq19 (eq24wm θ ρ) (eq24w0 θ ρ) (eq24wp θ ρ) ∧
    ParityInvariant (eq24wm θ ρ) (eq24w0 θ ρ) (eq24wp θ ρ) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · ext i j
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        Matrix.star_apply]
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [eq24wm, eq24w0, eq24wp, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
          Complex.sin_ofReal_im, Complex.cos_ofReal_im] <;>
        ring_nf <;> (try simp only [Real.sin_sq]) <;> ring
    · ext i j
      simp only [Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply,
        Matrix.star_apply]
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [eq24wm, eq24w0, eq24wp, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
          Complex.sin_ofReal_im, Complex.cos_ofReal_im] <;> ring_nf
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, Matrix.star_apply]
      fin_cases i <;> fin_cases j <;>
        apply Complex.ext <;>
        simp [eq24wm, eq24wp]
  · constructor
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [eq24wm, eq24wp, P2, Matrix.of_apply]
    · ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      fin_cases i <;> fin_cases j <;>
        simp [eq24w0, P2, Matrix.of_apply]

def IsEq24Form (wm w0 wp : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  ∃ (θ ρ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) (φ : ℂ),
    U ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ ‖φ‖ = 1 ∧
      wm = φ • (U * eq24wm θ ρ * star U) ∧
      w0 = φ • (U * eq24w0 θ ρ * star U) ∧
      wp = φ • (U * eq24wp θ ρ * star U)

end Qatlib.Papers.QCellAutomata96.MainResults
