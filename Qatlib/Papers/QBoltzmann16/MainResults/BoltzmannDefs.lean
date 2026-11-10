/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixWeights.WeightsCore
import Qatlib.Concepts.MatrixExpTrace.GibbsNorm
import Qatlib.Foundations.MatrixExpTrace.CompJensen
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder Matrix Matrix.Norms.L2Operator
namespace Qatlib.Papers.QBoltzmann16.MainResults

abbrev Operator (D : ℕ) := Matrix (Fin D) (Fin D) ℂ

def gibbsPartition (D : ℕ) (H : Operator D) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-H))).re

def marginalizedProbability (D : ℕ) (H Lambda : Operator D) : ℝ :=
  (Matrix.trace (Lambda*NormedSpace.exp (-H))).re/gibbsPartition D H

def conditionalProbability (D : ℕ) (H Lambda : Operator D) : ℝ :=
  marginalizedProbability D H Lambda

def boltzmannAverage (D : ℕ) (H A : Operator D) : ℝ :=
  (Matrix.trace (NormedSpace.exp (-H)*A)).re/gibbsPartition D H

def clampHamiltonian {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) (H : Operator D) : Operator E :=
  Vᴴ*H*V

def clampLinear {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) : Operator D →ₗ[ℂ] Operator E where
  toFun := clampHamiltonian V
  map_add' A B := by simp [clampHamiltonian,Matrix.mul_add,Matrix.add_mul]
  map_smul' c A := by simp [clampHamiltonian,Matrix.mul_smul,Matrix.smul_mul]

def clampCLM {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) : Operator D →L[ℝ] Operator E :=
  ((clampLinear V).restrictScalars ℝ).toContinuousLinearMap

theorem clamp_hasDerivAt {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (H : ℝ→Operator D) (Hprime : Operator D) (theta : ℝ) (hH : HasDerivAt H Hprime theta) :
    HasDerivAt (fun t=>clampHamiltonian V (H t)) (clampHamiltonian V Hprime) theta := by
  exact (clampCLM V).hasFDerivAt.comp_hasDerivAt theta hH

theorem clamp_continuousAt {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (Hprime : ℝ→Operator D) (theta : ℝ) (hc : ContinuousAt Hprime theta) :
    ContinuousAt (fun t=>clampHamiltonian V (Hprime t)) theta :=
  (clampCLM V).continuous.continuousAt.comp hc

theorem clamp_hermitian {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ)
    (H : Operator D) (hH : H.IsHermitian) : (clampHamiltonian V H).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul V hH

theorem golden_thompson_trace (D : ℕ) (A B : Operator D)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp (A+B))).re ≤
      (Matrix.trace (NormedSpace.exp A*NormedSpace.exp B)).re :=
  Qatlib.Concepts.MatrixWeights.WeightsCore.matrix_mw_golden_thompson_trace_potential D A B hA hB

theorem gibbsPartition_pos (D : ℕ) (H : Operator D) (hD : 0<D) (hH : H.IsHermitian) :
    0<gibbsPartition D H := by
  letI : Nonempty (Fin D) := ⟨⟨0,hD⟩⟩
  exact Qatlib.Concepts.MatrixExpTrace.GibbsNorm.exp_trace_re_pos (-H) hH.neg

theorem clamped_ratio_pos {D E : ℕ} (V : Matrix (Fin D) (Fin E) ℂ) (H : Operator D)
    (hD : 0<D) (hE : 0<E) (hH : H.IsHermitian) :
    0<gibbsPartition E (clampHamiltonian V H)/gibbsPartition D H :=
  div_pos (gibbsPartition_pos E _ hE (clamp_hermitian V H hH)) (gibbsPartition_pos D H hD hH)

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

theorem negative_log_likelihood_upper_bound {I : Type*} [Fintype I]
    (data model lower : I→ℝ) (hd : ∀i,0≤data i) (hl : ∀i,0<lower i)
    (hm : ∀i,lower i ≤ model i) :
    -(∑i,data i*Real.log (model i))≤-(∑i,data i*Real.log (lower i)) := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (Real.log_le_log (hl i) (hm i)) (hd i))
  linarith
end Qatlib.Papers.QBoltzmann16.MainResults
