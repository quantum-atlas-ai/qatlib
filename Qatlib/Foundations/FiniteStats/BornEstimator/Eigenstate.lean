/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.States.Mixed.MState

/-!
# Eigenvectors as pure quantum states

This module packages a column of a Hermitian matrix's eigenvector unitary as the normalized ket
`eigenKet`. It proves the eigenvector equation and identifies the expectation of the matrix in
the corresponding pure state with its eigenvalue.

These spectral witnesses support the state optimization arguments associated with [XuEtAl2026].

## Main statements

* `eigenKet`: The normalized ket given by the `i`th column of the eigenvector unitary of `A`.
* `eigenstate_exp`: The expectation of `A` in the pure state defined by `eigenKet A i` equals
  the corresponding eigenvalue.

## References

* [Xu et al., 2026][XuEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The normalized ket given by the `i`th column of the eigenvector unitary of `A`. -/
def eigenKet (A : HermitianMat d ℂ) (i : d) : Ket d :=
  ⟨fun x => A.H.eigenvectorUnitary x i,Matrix.unitaryGroup_row_norm _ i⟩

/-- The ket `eigenKet A i` is an eigenvector of `A` with eigenvalue `A.H.eigenvalues i`. -/
theorem eigenKet_mulVec (A : HermitianMat d ℂ) (i : d) :
    A.mat *ᵥ (eigenKet A i : d → ℂ) = (A.H.eigenvalues i : ℂ) • (eigenKet A i : d → ℂ) := by
  simpa only [eigenKet,Matrix.IsHermitian.eigenvectorUnitary_apply] using!
      A.H.mulVec_eigenvectorBasis i

/-- The expectation of `A` in the pure state defined by `eigenKet A i` equals the corresponding
eigenvalue. -/
theorem eigenstate_exp (A : HermitianMat d ℂ) (i : d) :
    (MState.pure (eigenKet A i)).exp_val A=A.H.eigenvalues i := by
  let v : d → ℂ := eigenKet A i
  have hn : v ⬝ᵥ star v=(1:ℂ) := by
    change (∑ x,v x*star (v x))=1
    have h := congrArg (fun r : ℝ => (r:ℂ)) (eigenKet A i).normalized
    simpa only [Complex.ofReal_sum,Complex.ofReal_one,Complex.normSq_eq_conj_mul_self,
      RCLike.star_def,mul_comm] using h
  rw [MState.exp_val,real_inner_comm,HermitianMat.inner_eq_re_trace]
  change Complex.re (Matrix.trace (A.mat*Matrix.vecMulVec v (star v)))=A.H.eigenvalues i
  rw [Matrix.mul_vecMulVec,eigenKet_mulVec,Matrix.trace_vecMulVec,smul_dotProduct,hn]
  simp

end Qatlib.Foundations.FiniteStats.BornEstimator
