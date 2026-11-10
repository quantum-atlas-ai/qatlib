/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.PauliRepresentation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators
open Qatlib.Concepts.PauliClifford.PauliBasis
open Qatlib.Papers.KoopmanSim26.SpectralRep
open Qatlib.Papers.KoopmanSim26.SpectralRep.PauliBridge

namespace Qatlib.Papers.KoopmanSim26.SpectralRep.CanonicalPauli

theorem source_coefficient_eq_public {n : ℕ} (f : Cube n → ℝ) (s : Cube n) :
    (walshCoeff f s:ℂ)=pauliCoefficient (Matrix.diagonal (fun x : Cube n => (f x:ℂ))) (zWord s) := by
  rw [walshCoeff_eq_pauli_trace, pauliCoefficient, Matrix.trace_mul_comm]
  congr 1
  simp only [one_div, inv_pow]

theorem target_exp_actual_pauli {n : ℕ} (α : Cube n → ℝ) :
    NormedSpace.exp (Complex.I • (∑ s : Cube n, (α s:ℂ) • pauliWord (zWord s))) =
      diagonalUnitary (walshPhase α) := by
  rw [← walsh_generator_pauli_sum, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rfl

end Qatlib.Papers.KoopmanSim26.SpectralRep.CanonicalPauli
