/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Qatlib.Concepts.MatrixExpTrace.GibbsNorm
import Qatlib.Foundations.MatrixExpTrace.CompJensen

/-!
# Finite Gibbs probabilities and compression bounds

This module defines finite Gibbs partition functions, trace-ratio probabilities, observable
averages, and compressed Hamiltonians `clampHamiltonian`. It proves positivity, regularity of
compression, and a lower bound on a projector probability by the compressed partition ratio,
supplying the finite matrix ingredients for [AminEtAl2018].

The weighted negative-log inequality converts positive probability lower bounds into an upper
bound on a loss with nonnegative data weights.

## Main statements

* `clamped_trace_probability_lower_bound`: the compressed partition ratio bounds the projector
  probability from below.
* `negative_log_likelihood_upper_bound`: probability lower bounds give a loss upper bound.
* `golden_thompson_trace`: the finite Hermitian trace-exponential inequality.

## References

* [Amin et al., 2018][AminEtAl2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator
namespace Qatlib.Papers.QBoltzmann16.MainResults

/-- The complex matrix type for operators on a `D`-dimensional space indexed by `Fin D`. -/
abbrev Operator (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

/-- The real part of the trace of `exp (-H)`, used as the finite Gibbs partition function. -/
def gibbsPartition (D : ℕ) (H : Operator D) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-H))).re

/-- The real trace of `Lambda * exp (-H)` divided by the Gibbs partition function. -/
def marginalizedProbability (D : ℕ) (H Lambda : Operator D) : ℝ :=
  (Matrix.trace (Lambda*NormedSpace.exp (-H))).re/gibbsPartition D H

/-- The trace-ratio probability `marginalizedProbability`, named for use with an input-dependent
Hamiltonian. -/
def conditionalProbability (D : ℕ) (H Lambda : Operator D) : ℝ :=
  marginalizedProbability D H Lambda

/-- The real trace of `exp (-H) * A` divided by the Gibbs partition function. -/
def boltzmannAverage (D : ℕ) (H A : Operator D) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-H)*A)).re/gibbsPartition D H

/-- The compression `Vᴴ * H * V` of an operator along the matrix `V`. -/
def clampHamiltonian {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) (H : Operator D) : Operator E :=
  Vᴴ*H*V

/-- Compression by a fixed matrix `V` as a complex-linear map on operators. -/
def clampLinear {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) : Operator D →ₗ[ℂ] Operator E where
  toFun := clampHamiltonian V
  map_add' A B := by simp [clampHamiltonian,Matrix.mul_add,Matrix.add_mul]
  map_smul' c A := by simp [clampHamiltonian,Matrix.mul_smul,Matrix.smul_mul]

/-- Compression by a fixed matrix `V` as a continuous real-linear map on operators. -/
def clampCLM {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) : Operator D →L[ℝ] Operator E :=
  ((clampLinear V).restrictScalars ℝ).toContinuousLinearMap

/-- Compressing a differentiable operator family by a fixed matrix differentiates to the
compression of its derivative. -/
theorem clamp_hasDerivAt {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (H : ℝ→Operator D) (Hprime : Operator D) (theta : ℝ) (hH : HasDerivAt H Hprime theta) :
    HasDerivAt (fun t=>clampHamiltonian V (H t)) (clampHamiltonian V Hprime) theta := by
  exact (clampCLM V).hasFDerivAt.comp_hasDerivAt theta hH

/-- Compression by a fixed matrix preserves continuity at the specified parameter. -/
theorem clamp_continuousAt {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (Hprime : ℝ→Operator D) (theta : ℝ) (hc : ContinuousAt Hprime theta) :
    ContinuousAt (fun t=>clampHamiltonian V (Hprime t)) theta :=
  (clampCLM V).continuous.continuousAt.comp hc

/-- Compression of a Hermitian matrix by any matrix is Hermitian. -/
theorem clamp_hermitian {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (H : Operator D) (hH : H.IsHermitian) : (clampHamiltonian V H).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul V hH

/-- For finite Hermitian matrices `A` and `B`, the real trace of `exp (A + B)` is at most the
real trace of `exp A * exp B`. -/
theorem golden_thompson_trace (D : ℕ) (A B : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (A+B))).re ≤
      (Matrix.trace (NormedSpace.exp A*NormedSpace.exp B)).re :=
  Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential D A B hA hB

/-- A Hermitian Hamiltonian in positive dimension has a strictly positive Gibbs partition
function. -/
theorem gibbsPartition_pos (D : ℕ) (H : Operator D) (hD : 0<D) (hH : H.IsHermitian) :
    0<gibbsPartition D H := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  exact Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos (-H) hH.neg

/-- For positive full and compressed dimensions and Hermitian `H`, the compressed Gibbs
partition ratio is strictly positive. -/
theorem clamped_ratio_pos {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) (H : Operator D)
    (hD : 0<D) (hE : 0<E) (hH : H.IsHermitian) :
    0<gibbsPartition E (clampHamiltonian V H)/gibbsPartition D H :=
  div_pos (gibbsPartition_pos E _ hE (clamp_hermitian V H hH)) (gibbsPartition_pos D H hD hH)

/-- For Hermitian `H` in positive dimension and an isometric embedding `V`, the compressed
partition ratio is at most the Gibbs probability associated with `V * Vᴴ`. -/
theorem clamped_trace_probability_lower_bound {D E : ℕ} (H : Operator D)
    (V : Matrix (Fin D) (Fin E) ℂ) (hD : 0<D) (hH : H.IsHermitian) (hV : Vᴴ*V=1) :
    gibbsPartition E (clampHamiltonian V H)/gibbsPartition D H ≤
      marginalizedProbability D H (V*Vᴴ) := by
  have hj := Qatlib.Foundations.MatrixExpTrace.CompJensen.isometry_exp_trace_le (-H) hH.neg V hV
  have htr : Matrix.trace (Vᴴ*NormedSpace.exp (-H)*V)=Matrix.trace ((V*Vᴴ)*NormedSpace.exp (-H)) := by
    rw [Matrix.trace_mul_cycle]
  have hneg : Vᴴ*(-H)*V=-(clampHamiltonian V H) := by simp [clampHamiltonian]
  rw [hneg,htr] at hj
  exact div_le_div_of_nonneg_right hj (gibbsPartition_pos D H hD hH).le

/-- For nonnegative data weights, positive pointwise lower bounds on model values give an upper
bound on the weighted negative-log loss. -/
theorem negative_log_likelihood_upper_bound {I : Type*} [Fintype I]
    (data model lower : I→ℝ) (hd : ∀i,0≤data i) (hl : ∀i,0<lower i)
    (hm : ∀i,lower i ≤ model i) :
    -(∑i,data i*Real.log (model i))≤-(∑i,data i*Real.log (lower i)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (Real.log_le_log (hl i) (hm i)) (hd i))
  linarith
end Qatlib.Papers.QBoltzmann16.MainResults
