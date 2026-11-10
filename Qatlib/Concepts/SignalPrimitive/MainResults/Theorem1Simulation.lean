/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.LCUConsumers.Theorem1Simulation
import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
set_option warningAsError false


open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SignalPrimitive.LCUConsumers
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Concepts.SignalPrimitive.MainResults
open Matrix Polynomial Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

private theorem realize_polynomial {W I : Type} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (V : Matrix W W ℂ)
    (F : Matrix W I ℂ) (hA : A.IsHermitian) (hV : ProjectedUnitaryEncoding A V F F)
    (p : Polynomial ℝ) (d : ℕ) (hdeg : p.degree ≤ (d : WithBot ℕ))
    (hpar : HasRealParity d p) (hbound : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ cs : List (AdjointStep (Bool × W)),
      compress (averageFrame F) (evaluate (parallelOracle V) cs) (averageFrame F) =
        aeval A (p.map Complex.ofRealHom) ∧
      adjointQueryCount cs = d ∧ adjointGateCount cs = d + 1 := by
  obtain ⟨base, zs, hb, hz, hn, hpoly, _⟩ := exists_phases_of_bounded hdeg hpar hbound
  have hreal : realPartPolynomial (responseP base zs) = p.map Complex.ofRealHom := by
    unfold realPartPolynomial
    change (2 : ℂ)⁻¹ • (responseP base zs +
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs)) = _
    rw [hpoly, Polynomial.C_mul', smul_smul]
    norm_num
  let cs := hermitianResponseWord F d base zs
  refine ⟨cs, ?_, (hermitianResponseWord_counts F d base zs hn).1,
    (hermitianResponseWord_counts F d base zs hn).2⟩
  have hencoding : ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
      (evaluate (parallelOracle V) cs) (averageFrame F) (averageFrame F) := by
    dsimp [cs, hermitianResponseWord]
    split_ifs with ho
    · rw [evaluate_compileRealPartQSVT]
      have h := realPartQSVT_odd_projectedEncoding hV hb zs hz (by simpa only [hn] using ho)
      rw [hreal, hermitian_dilation_polynomial_odd A hA p d hpar ho] at h
      exact h
    · have he : d % 2 = 0 := by omega
      rw [evaluate_swapQueries, parallelOracle_adjoint, evaluate_compileRealPartQSVT]
      have h := realPartQSVT_even_right_projectedEncoding hV hb zs hz (by simpa only [hn] using he)
      rw [hreal, hermitian_dilation_polynomial_even A hA p d hpar he] at h
      exact h
  exact hencoding.encoded

private theorem taylor_parts (τ : ℝ) (n : ℕ) :
    exponentialTaylorPolynomial τ n =
      (cosineTaylorPolynomial τ n).map Complex.ofRealHom -
        Complex.I • (sineTaylorPolynomial τ n).map Complex.ofRealHom := by
  unfold exponentialTaylorPolynomial cosineTaylorPolynomial sineTaylorPolynomial
  simp only [Polynomial.map_sum, Polynomial.map_monomial, Finset.smul_sum,
    ← Finset.sum_sub_distrib, Polynomial.smul_monomial, ← Polynomial.monomial_sub]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  apply Complex.ext <;> simp

private theorem taylor_operator_error {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (τ : ℝ) (n : ℕ)
    (hspec : ∀ i, hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1)
    (hcut : 2 * |τ| ≤ (n : ℝ) + 1) :
    ‖aeval A (exponentialTaylorPolynomial τ n) -
      NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A)‖ ≤ exponentialTaylorError τ n := by
  letI : CStarAlgebra (Matrix I I ℂ) := {}
  letI : NormedAlgebra ℚ (Matrix I I ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  let eigVals : I → ℂ := fun i => (hA.eigenvalues i : ℂ)
  let D := Matrix.diagonal eigVals
  let Φ := Unitary.conjStarAlgAut ℂ (Matrix I I ℂ) hA.eigenvectorUnitary
  have hdiag : A = Φ D := hA.spectral_theorem
  let p := exponentialTaylorPolynomial τ n
  have heval : (aeval eigVals) p = fun i => p.eval (eigVals i) := by
    funext i
    rw [Polynomial.aeval_pi_apply₂]
    simp [Polynomial.aeval_def]
  have hpd : aeval D p = Matrix.diagonal (fun i => p.eval (eigVals i)) := by
    have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℂ) eigVals p
    rw [heval] at h
    exact h
  have hp : aeval A p = Φ (Matrix.diagonal (fun i => p.eval (eigVals i))) := by
    rw [hdiag, Polynomial.aeval_algHom_apply, hpd]
  have hde : NormedSpace.exp ((-Complex.I * (τ : ℂ)) • D) =
      Matrix.diagonal (fun i => Complex.exp (-Complex.I * (τ : ℂ) * eigVals i)) := by
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]
    congr 1
    funext i
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    rfl
  have hexp : NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A) =
      Φ (Matrix.diagonal (fun i => Complex.exp (-Complex.I * (τ : ℂ) * eigVals i))) := by
    rw [hdiag, ← map_smul]
    rw [← NormedSpace.map_exp Φ (StarAlgEquiv.isometry Φ).continuous, hde]
  change ‖aeval A p - NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A)‖ ≤ _
  rw [hp, hexp, ← map_sub, StarAlgEquiv.norm_map, Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (exponentialTaylorError_nonneg τ n)).2
  intro i
  exact exponentialTaylorPolynomial_error_le τ n hcut (hspec i)

private theorem restore_quarter {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (p : Polynomial ℝ) :
    (4 : ℂ) • aeval A ((C (1/4 : ℝ) * p).map Complex.ofRealHom) =
      aeval A (p.map Complex.ofRealHom) := by
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.aeval_mul,
    Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, smul_smul]
  norm_num

theorem theorem1Simulation : Theorem1Simulation := by
  intro J I _ _ _ _ H V j₀ α t ε n hH hα _hHnorm _hε hε1 hV hcut htail
  let A := ((α⁻¹ : ℝ) : ℂ) • H
  let τ := t * α
  have hA : A.IsHermitian := by
    dsimp [A]
    exact hH.smul (R := ℝ) (IsSelfAdjoint.all _)
  have htail1 : exponentialTaylorError τ n < 1 := htail.trans_lt hε1
  let qc := C (1/4 : ℝ) * cosineTaylorPolynomial τ n
  let qs := C (1/4 : ℝ) * sineTaylorPolynomial τ n
  have hcdeg : qc.degree ≤ (2*n : ℕ) := by
    apply Polynomial.degree_le_natDegree.trans
    exact_mod_cast (Polynomial.natDegree_C_mul_le _ _).trans
      ((cosineTaylorPolynomial_natDegree_le τ n).trans (by omega : n-1 ≤ 2*n))
  have hsdeg : qs.degree ≤ (2*n+1 : ℕ) := by
    apply Polynomial.degree_le_natDegree.trans
    exact_mod_cast (Polynomial.natDegree_C_mul_le _ _).trans
      ((sineTaylorPolynomial_natDegree_le τ n).trans (by omega : n-1 ≤ 2*n+1))
  have hcpar : HasRealParity (2*n) qc := by
    simp [HasRealParity, qc, Polynomial.mul_comp, cosineTaylorPolynomial_comp_neg_X, pow_mul]
  have hspar : HasRealParity (2*n+1) qs := by
    simp [HasRealParity, qs, Polynomial.mul_comp, sineTaylorPolynomial_comp_neg_X, pow_add, pow_mul]
  obtain ⟨wc, hwc, hqc, hgc⟩ := realize_polynomial A V (encodingFiber j₀) hA hV qc (2*n)
    hcdeg hcpar (fun x hx => (scaledCosineTaylorPolynomial_abs_lt_half τ n hcut htail1 hx).le.trans (by norm_num))
  obtain ⟨ws, hws, hqs, hgs⟩ := realize_polynomial A V (encodingFiber j₀) hA hV qs (2*n+1)
    hsdeg hspar (fun x hx => (scaledSineTaylorPolynomial_abs_lt_half τ n hcut htail1 hx).le.trans (by norm_num))
  refine ⟨wc, ws, hqc, hgc, hqs, hgs, ?_⟩
  have hscalar : ∀ i : I, hA.eigenvalues i ∈ Set.Icc (-1 : ℝ) 1 := by
    intro i
    simpa only [Matrix.IsHermitian.eigenvalues, orderedHermitianValues] using
      hermitian_encoding_spectrum_interval A hA V (encodingFiber j₀) hV
        ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)
  have herr := taylor_operator_error A hA τ n hscalar hcut
  have hscale : (-Complex.I * (τ : ℂ)) • A = (-Complex.I * (t : ℂ)) • H := by
    have hc : (α : ℂ) ≠ 0 := by exact_mod_cast hα.ne'
    ext i j
    simp only [A, τ, Matrix.smul_apply, smul_eq_mul]
    push_cast
    field_simp [hc]
  rw [hwc, hws, restore_quarter, restore_quarter]
  rw [← map_smul, ← map_sub, ← taylor_parts, ← hscale]
  exact herr.trans htail

end Qatlib.Concepts.SignalPrimitive.MainResults
