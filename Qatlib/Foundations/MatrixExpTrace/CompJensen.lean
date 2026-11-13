/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.LogExp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Jensen bounds for compressed matrix exponentials

`density_exp_jensen` compares the exponential of a Hermitian expectation with the expectation of
the matrix exponential in a positive semidefinite trace-one matrix. Coordinate projection
identities then yield `isometry_exp_trace_le`, a trace inequality for compression by a
rectangular isometry.

The module also identifies `HermitianMat.exp` with the normed-algebra matrix exponential. These
are finite-dimensional exponential convexity estimates in the setting of [HiaiPetz2014].

## Main statements

* `density_exp_jensen`: the scalar exponential Jensen bound for a density matrix.
* `coordinate_sandwich_trace`: a rank-one coordinate sandwich extracts a compressed diagonal
  entry.
* `isometry_exp_trace_le`: the exponential of a compression has trace at most the compressed
  exponential's trace.

## References

* [Hiai and Petz, 2014][HiaiPetz2014]
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Matrix
open scoped Classical BigOperators ComplexOrder MatrixOrder Matrix Matrix.Norms.L2Operator
namespace Qatlib.Foundations.MatrixExpTrace.CompJensen

/-- For Hermitian `X` and a positive semidefinite trace-one matrix `sigma`, the exponential of
the real part of `trace (sigma * X)` is at most the real part of `trace (sigma * exp X)`. -/
theorem density_exp_jensen (D : ℕ) (X sigma : Matrix (Fin D) (Fin D) ℂ)
    (hX : X.IsHermitian) (hsigma : sigma.PosSemidef) (htrace : Matrix.trace sigma=1) :
    Real.exp (Matrix.trace (sigma*X)).re ≤
      (Matrix.trace (sigma*NormedSpace.exp X)).re := by
  let U := hX.eigenvectorUnitary
  let R : Matrix (Fin D) (Fin D) ℂ := U.valᴴ * sigma * U.val
  let p : Fin D → ℝ := fun i => (R i i).re
  have hR : R.PosSemidef := hsigma.conjTranspose_mul_mul_same U.val
  have hpn (i : Fin D) : 0 ≤ p i := (Complex.nonneg_iff.mp (hR.diag_nonneg (i := i))).1
  have htr : Matrix.trace R = 1 := by
    dsimp [R]
    rw [Matrix.trace_mul_cycle,
      show U.val*U.valᴴ=1 from Matrix.mem_unitaryGroup_iff.mp U.property,
      Matrix.one_mul,htrace]
  have hpsum : ∑i,p i=1 := by
    change ∑i,(R i i).re=1
    simpa [Matrix.trace,← Complex.re_sum] using congrArg Complex.re htr
  have hex : (Matrix.trace (sigma*X)).re=∑i,p i*hX.eigenvalues i := by
    conv_lhs => rw [hX.spectral_theorem]
    change (Matrix.trace (sigma*(U.val*Matrix.diagonal (fun i=>(hX.eigenvalues i : ℂ))*U.valᴴ))).re=_
    rw [← Matrix.mul_assoc,Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
    change (Matrix.trace (R*Matrix.diagonal (fun i=>(hX.eigenvalues i : ℂ)))).re=_
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,p]
  have htex : (Matrix.trace (sigma*NormedSpace.exp X)).re=∑i,p i*Real.exp (hX.eigenvalues i) := by
    have he : NormedSpace.exp X=cfc Real.exp X := by
      letI : ContinuousFunctionalCalculus ℝ (Matrix (Fin D) (Fin D) ℂ) IsSelfAdjoint :=
        Matrix.IsHermitian.instContinuousFunctionalCalculus
      exact (CFC.real_exp_eq_normedSpace_exp (a := X) (show IsSelfAdjoint X from hX)).symm
    rw [he]
    rw [hX.cfc_eq,Matrix.IsHermitian.cfc,Unitary.conjStarAlgAut_apply]
    change (Matrix.trace (sigma*(U.val*Matrix.diagonal (fun i=>(Real.exp (hX.eigenvalues i) : ℂ))*U.valᴴ))).re=_
    rw [← Matrix.mul_assoc,Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc]
    change (Matrix.trace (R*Matrix.diagonal (fun i=>(Real.exp (hX.eigenvalues i) : ℂ)))).re=_
    simp only [Matrix.trace,Matrix.diag_apply,Matrix.mul_diagonal,Complex.re_sum,
      Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,p]
  rw [hex,htex]
  simpa only [smul_eq_mul] using convexOn_exp.map_sum_le (t := Finset.univ) (w := p)
    (p := hX.eigenvalues) (fun i _=>hpn i) hpsum (fun _ _=>Set.mem_univ _)

/-- The underlying matrix of the Hermitian-matrix exponential equals the normed-algebra
exponential of the underlying matrix. -/
theorem hermitian_exp_mat {E : ℕ} (H : HermitianMat (Fin E) ℂ) :
    H.exp.mat=NormedSpace.exp H.mat := by
  rw [HermitianMat.exp,HermitianMat.mat_cfc]
  letI : ContinuousFunctionalCalculus ℝ (Matrix (Fin E) (Fin E) ℂ) IsSelfAdjoint :=
    Matrix.IsHermitian.instContinuousFunctionalCalculus
  exact CFC.real_exp_eq_normedSpace_exp H.H

/-- The diagonal projection onto the coordinate indexed by `i`. -/
def coordinateProjection {E : ℕ} (i : Fin E) : Matrix (Fin E) (Fin E) ℂ :=
  Matrix.diagonal (fun j=>if j=i then 1 else 0)

/-- A coordinate projection matrix is positive semidefinite. -/
theorem coordinateProjection_psd {E : ℕ} (i : Fin E) :
    (coordinateProjection i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  change (0 : ℂ) ≤ if j=i then 1 else 0
  split_ifs <;> simp

/-- The trace pairing of `K * coordinateProjection i * Kᴴ` with `X` equals the `i`th diagonal
entry of `Kᴴ * X * K`. -/
theorem coordinate_sandwich_trace {D E : ℕ} (K : Matrix (Fin D) (Fin E) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) (i : Fin E) :
    Matrix.trace ((K*coordinateProjection i*Kᴴ)*X)=(Kᴴ*X*K) i i := by
  calc
    _ = Matrix.trace ((K*coordinateProjection i)*(Kᴴ*X)) := by rw [Matrix.mul_assoc]
    _ = Matrix.trace ((Kᴴ*X)*(K*coordinateProjection i)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace ((Kᴴ*X*K)*coordinateProjection i) := by simp only [Matrix.mul_assoc]
    _ = _ := by simp [coordinateProjection,Matrix.trace,Matrix.mul_diagonal]

/-- For Hermitian `X` and `Vᴴ * V = 1`, the real trace of `exp (Vᴴ * X * V)` is at most the real
trace of `Vᴴ * exp X * V`. -/
theorem isometry_exp_trace_le {D E : ℕ} (X : Matrix (Fin D) (Fin D) ℂ)
    (hX : X.IsHermitian) (V : Matrix (Fin D) (Fin E) ℂ) (hV : Vᴴ*V=1) :
    (Matrix.trace (NormedSpace.exp (Vᴴ*X*V))).re ≤
      (Matrix.trace (Vᴴ*NormedSpace.exp X*V)).re := by
  let B := Vᴴ*X*V
  have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul V hX
  let U := hB.eigenvectorUnitary
  let K := V*U.val
  have hU : U.valᴴ*U.val=1 := Matrix.mem_unitaryGroup_iff'.mp U.property
  have hUr : U.val*U.valᴴ=1 := Matrix.mem_unitaryGroup_iff.mp U.property
  have hK : Kᴴ*K=1 := by
    dsimp [K]
    rw [Matrix.conjTranspose_mul]
    calc
      _ = U.valᴴ*(Vᴴ*V)*U.val := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hV,Matrix.mul_one,hU]
  have hKB : Kᴴ*X*K=Matrix.diagonal (fun i=>(hB.eigenvalues i : ℂ)) := by
    dsimp [K]
    rw [Matrix.conjTranspose_mul]
    calc
      _ = U.valᴴ*B*U.val := by simp only [B,Matrix.mul_assoc]
      _ = _ := by
        conv_lhs => rw [hB.spectral_theorem]
        change U.valᴴ*(U.val*Matrix.diagonal (fun i=>(hB.eigenvalues i : ℂ))*U.valᴴ)*U.val=_
        simp only [← Matrix.mul_assoc,hU,Matrix.one_mul]
        rw [Matrix.mul_assoc,hU,Matrix.mul_one]
  have hi (i : Fin E) : Real.exp (hB.eigenvalues i) ≤ ((Kᴴ*NormedSpace.exp X*K) i i).re := by
    let sigma := K*coordinateProjection i*Kᴴ
    have hp : sigma.PosSemidef := (coordinateProjection_psd i).mul_mul_conjTranspose_same K
    have ht : Matrix.trace sigma=1 := by
      have hh := coordinate_sandwich_trace K (1 : Matrix (Fin D) (Fin D) ℂ) i
      simpa only [Matrix.mul_one,Matrix.one_mul,hK,Matrix.one_apply_eq] using hh
    have hj := density_exp_jensen D X sigma hX hp ht
    change Real.exp (Matrix.trace ((K*coordinateProjection i*Kᴴ)*X)).re ≤
      (Matrix.trace ((K*coordinateProjection i*Kᴴ)*NormedSpace.exp X)).re at hj
    simp_rw [coordinate_sandwich_trace] at hj
    simpa only [hKB,Matrix.diagonal_apply_eq,Complex.ofReal_re] using hj
  have he : (Matrix.trace (NormedSpace.exp B)).re=∑i,Real.exp (hB.eigenvalues i) := by
    let H : HermitianMat (Fin E) ℂ := ⟨B,hB⟩
    change (Matrix.trace (NormedSpace.exp H.mat)).re=_
    rw [← hermitian_exp_mat H]
    exact H.trace_cfc_eq Real.exp
  have htr : Matrix.trace (Kᴴ*NormedSpace.exp X*K)=Matrix.trace (Vᴴ*NormedSpace.exp X*V) := by
    dsimp [K]
    rw [Matrix.conjTranspose_mul]
    calc
      _ = Matrix.trace (U.valᴴ*(Vᴴ*NormedSpace.exp X*V)*U.val) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.trace_mul_cycle,hUr,Matrix.one_mul]
  change (Matrix.trace (NormedSpace.exp B)).re≤_
  rw [he]
  calc
    _ ≤ ∑i : Fin E,((Kᴴ*NormedSpace.exp X*K) i i).re := Finset.sum_le_sum (fun i _=>hi i)
    _ = (Matrix.trace (Kᴴ*NormedSpace.exp X*K)).re := by simp only [Matrix.trace,Complex.re_sum,Matrix.diag_apply]
    _ = _ := congrArg Complex.re htr

end Qatlib.Foundations.MatrixExpTrace.CompJensen
