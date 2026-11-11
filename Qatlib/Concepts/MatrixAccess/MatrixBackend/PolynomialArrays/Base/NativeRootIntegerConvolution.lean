/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Base.NativeRootIntegerPolynomial

set_option backward.isDefEq.respectTransparency false

/-! Ascending POWER-coefficient convolution, matching the final nested-update
coefficient formula. This is not the Chebyshev phase-array multiplication. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
open Polynomial
open Qatlib.Concepts.OrderedOracle.TiSdpBridge
open scoped BigOperators

/-- Each integer output cell of the double-loop convolution, before trimming. -/
def rootIntegerConvolution {d e : ℕ} (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) :
    Fin (d+e+1) → ℤ :=
  fun k => ∑ i,∑ j,if i.val+j.val=k.val then a i*b j else 0

/-- The finite construction in `NativeRootIntegerConvolution` satisfies `rootIntegerPolynomial_convolution` under the displayed hypotheses. -/
theorem rootIntegerPolynomial_convolution {d e : ℕ}
    (a : Fin (d+1) → ℤ) (b : Fin (e+1) → ℤ) :
    rootIntegerPolynomial (rootIntegerConvolution a b)=
      rootIntegerPolynomial a*rootIntegerPolynomial b := by
  apply Polynomial.ext
  intro k
  rw [rootIntegerPolynomial_coeff]
  simp only [rootIntegerPolynomial,laurentCoefficientPolynomial,Finset.sum_mul,
    Finset.mul_sum,Polynomial.monomial_mul_monomial,Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  by_cases hk : k<d+e+1
  · simp only [dite_eq_left hk,rootIntegerConvolution,Int.cast_sum,Int.cast_ite,Int.cast_mul,Int.cast_zero]
    exact Finset.sum_comm
  · rw [dite_eq_right hk]
    symm
    apply Finset.sum_eq_zero
    intro i _
    apply Finset.sum_eq_zero
    intro j _
    have hij : j.val+i.val≠k := by
      have hi := i.isLt
      have hj := j.isLt
      omega
    simp [hij]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays
