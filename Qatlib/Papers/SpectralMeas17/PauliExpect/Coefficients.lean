/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpectralMeas17.PauliExpect.Native

/-!
# Coefficient normalization for Pauli Hamiltonians

This module converts real Pauli coefficients into their absolute-sum scale, square-root
preparation amplitudes, and coefficient signs. It identifies the rescaled Pauli Hamiltonian with
the signed-term representation used in [PoulinEtAl2018].

## Main statements

* `coefficientAmplitude_normalized`: preparation amplitudes have squared sum one when the scale
  is positive.
* `normalizedHamiltonian_eq`: equality of the coefficient and signed-term Hamiltonians.

## References

* [Poulin et al., 2018][PoulinEtAl2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Papers.SpectralMeas17.PauliExpect
set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Foundations.MatrixGeometry.LcuFrame
variable {J : Type*} [Fintype J] [DecidableEq J] {n : ℕ}

/-- The sum of the absolute values of the real Pauli coefficients. -/
def coefficientScale (α : J → ℝ) : ℝ := ∑ j, |α j|

/-- The square root of a coefficient's absolute value divided by the total absolute coefficient
scale. -/
def coefficientAmplitude (α : J → ℝ) (j : J) : ℝ :=
  Real.sqrt (|α j| / coefficientScale α)

/-- The Boolean indicator that the specified real coefficient is negative. -/
def coefficientNegative (α : J → ℝ) (j : J) : Bool := decide (α j<0)

/-- The sum of the Pauli word operators weighted by their real coefficients divided by the total
absolute coefficient scale. -/
def normalizedHamiltonian (α : J → ℝ) (words : J → PauliWord n) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  ∑ j, ((α j / coefficientScale α : ℝ) : ℂ) • pauliWordOp n (words j)

omit [DecidableEq J] in

/-- When the total absolute coefficient scale is positive, the squared coefficient preparation
amplitudes sum to one. -/
theorem coefficientAmplitude_normalized (α : J → ℝ) (hα : 0<coefficientScale α) :
    ∑ j, coefficientAmplitude α j^2=1 := by
  simp_rw [coefficientAmplitude,Real.sq_sqrt (div_nonneg (abs_nonneg _) hα.le)]
  rw [← Finset.sum_div]
  exact div_self hα.ne'

omit [DecidableEq J] in

/-- For positive coefficient scale, the normalized Pauli Hamiltonian equals the signed-term
Hamiltonian formed using `coefficientAmplitude` and `coefficientNegative`. -/
theorem normalizedHamiltonian_eq (α : J → ℝ) (words : J → PauliWord n)
    (hα : 0<coefficientScale α) :
    normalizedHamiltonian α words =
      hamiltonian (coefficientAmplitude α) (coefficientNegative α) words := by
  unfold normalizedHamiltonian hamiltonian ham
  apply Finset.sum_congr rfl
  intro j _
  have hsq : coefficientAmplitude α j^2 = |α j|/coefficientScale α :=
    Real.sq_sqrt (div_nonneg (abs_nonneg _) hα.le)
  have hsqC : (coefficientAmplitude α j : ℂ)^2 = ((|α j|/coefficientScale α : ℝ) : ℂ) := by
    exact_mod_cast hsq
  rw [hsqC]
  by_cases hn : α j<0
  · simp [coefficientNegative,signedTerm,hn,abs_of_neg hn,neg_div]
  · simp [coefficientNegative,signedTerm,hn,abs_of_nonneg (le_of_not_gt hn)]

end
end Qatlib.Papers.SpectralMeas17.PauliExpect
