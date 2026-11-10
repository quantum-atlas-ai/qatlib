/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.States.Mixed.MState
set_option warningAsError false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Foundations.FiniteStats.BornEstimator
open scoped Classical BigOperators RealInnerProductSpace
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

def eigenKet (A : HermitianMat d ℂ) (i : d) : Ket d :=
  ⟨fun x => A.H.eigenvectorUnitary x i,Matrix.unitaryGroup_row_norm _ i⟩

theorem eigenKet_mulVec (A : HermitianMat d ℂ) (i : d) :
    A.mat *ᵥ (eigenKet A i : d → ℂ) = (A.H.eigenvalues i : ℂ) • (eigenKet A i : d → ℂ) := by
  simpa only [eigenKet,Matrix.IsHermitian.eigenvectorUnitary_apply] using!
      A.H.mulVec_eigenvectorBasis i

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
