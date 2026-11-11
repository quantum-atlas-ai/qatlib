/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.KoopmanSim26.SpectralRep.PauliRepresentation
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Canonical Pauli interpretation of Walsh phases

This module connects the real Walsh coefficients and diagonal phase functions used in the
spectral ansatz to the public Pauli basis. The result `source_coefficient_eq_public` identifies
a diagonal observable's Walsh coefficient with its canonical Pauli coefficient at the
corresponding identity/Z word.

The identity `target_exp_actual_pauli` realizes a Walsh phase unitary as the exponential of an
actual Pauli-Z expansion. These bridges give the phase representation underlying the
product-rotation approximation framework in [ZhangEtAl2026].

## Main statements

* `source_coefficient_eq_public` equates Walsh and canonical Pauli coefficients for diagonal
  real data.
* `target_exp_actual_pauli` exponentiates the Pauli-Z expansion to the associated diagonal phase
  unitary.

## References

- [Zhang et al., 2026][ZhangEtAl2026]
-/

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

/-- The complex cast of a real function's Walsh coefficient equals the canonical Pauli
coefficient of its diagonal matrix at the corresponding identity/Z word. This identifies the
coefficient convention for the diagonal ansatz in [ZhangEtAl2026]. -/
theorem source_coefficient_eq_public {n : ℕ} (f : Cube n → ℝ) (s : Cube n) :
    (walshCoeff f s:ℂ)=pauliCoefficient (Matrix.diagonal (fun x : Cube n => (f x:ℂ))) (zWord s) := by
  rw [walshCoeff_eq_pauli_trace, pauliCoefficient, Matrix.trace_mul_comm]
  congr 1
  simp only [one_div, inv_pow]

/-- Exponentiating `i` times the Pauli-Z sum with real coefficients `alpha` gives the diagonal
unitary whose phase function is `walshPhase alpha`. -/
theorem target_exp_actual_pauli {n : ℕ} (α : Cube n → ℝ) :
    NormedSpace.exp (Complex.I • (∑ s : Cube n, (α s:ℂ) • pauliWord (zWord s))) =
      diagonalUnitary (walshPhase α) := by
  rw [← walsh_generator_pauli_sum, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  apply congrArg Matrix.diagonal
  funext x
  rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
  rfl

end Qatlib.Papers.KoopmanSim26.SpectralRep.CanonicalPauli
