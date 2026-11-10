/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.QSVTBridge
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CBMD

open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def normalizedApproximation (P : Polynomial ℂ) (η : ℝ) : Polynomial ℂ :=
  ((1 + η)⁻¹ : ℝ) • P

theorem normalizedApproximation_bounded (P : Polynomial ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + η) :
    ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      ‖(normalizedApproximation P η).eval (x : ℂ)‖ ≤ 1 := by
  intro x hx
  have hr : 0 < 1 + η := by positivity
  simp only [normalizedApproximation, Polynomial.eval_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hr)]
  calc
    (1 + η)⁻¹ * ‖P.eval (x : ℂ)‖ ≤ (1 + η)⁻¹ * (1 + η) :=
      mul_le_mul_of_nonneg_left (hP x hx) (inv_nonneg.mpr hr.le)
    _ = 1 := inv_mul_cancel₀ hr.ne'

theorem normalized_scalar_error (z w : ℂ) (η : ℝ) (hη : 0 ≤ η)
    (hw : ‖w‖ ≤ 1) (herr : ‖z - w‖ ≤ η) :
    ‖((1 + η)⁻¹ : ℝ) • z - w‖ ≤ 2 * η / (1 + η) := by
  have hr : 0 < 1 + η := by positivity
  have hid : ((1 + η)⁻¹ : ℝ) • z - w =
      ((1 + η)⁻¹ : ℝ) • ((z - w) - η • w) := by
    have hsum : (1 + η)⁻¹ + (1 + η)⁻¹ * η = 1 := by
      calc
        (1 + η)⁻¹ + (1 + η)⁻¹ * η = (1 + η)⁻¹ * (1 + η) := by ring
        _ = 1 := inv_mul_cancel₀ hr.ne'
    simp only [smul_sub, smul_smul]
    rw [sub_sub, ← add_smul, hsum, one_smul]
  rw [hid, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  have hn : ‖(z - w) - η • w‖ ≤ 2 * η := by
    calc
      ‖(z - w) - η • w‖ ≤ ‖z - w‖ + ‖η • w‖ := norm_sub_le _ _
      _ = ‖z - w‖ + η * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
      _ ≤ η + η * 1 := add_le_add herr (mul_le_mul_of_nonneg_left hw hη)
      _ = 2 * η := by ring
  calc
    (1 + η)⁻¹ * ‖(z - w) - η • w‖ ≤ (1 + η)⁻¹ * (2 * η) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr hr.le)
    _ = 2 * η / (1 + η) := by ring

theorem hermitian_complex_polynomial_evaluation
    (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (P : Polynomial ℂ) :
    hermitianFunction A hA (fun x => P.eval (x : ℂ)) = aeval A P := by
  rw [aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A _
    (orderedHermitianBasis_action hA)]
  rfl

theorem hermitian_complex_polynomial_error
    (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (P : Polynomial ℂ)
    (g : ℝ → ℂ) (ε : ℝ) (hε : 0 ≤ ε)
    (herr : ∀ i, ‖g (orderedHermitianValues hA i) -
      P.eval (orderedHermitianValues hA i : ℂ)‖ ≤ ε) :
    ‖hermitianFunction A hA g - aeval A P‖ ≤ ε := by
  rw [← hermitian_complex_polynomial_evaluation I A hA P]
  exact spectralDiagonal_error_le (orderedHermitianBasis hA) _ _ hε herr

theorem normalized_approximation_qsvt_uniform_phases
    (P : Polynomial ℂ) (g : ℝ → ℂ) (s : Set ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + η)
    (hg : ∀ x ∈ s, ‖g x‖ ≤ 1)
    (happrox : ∀ x ∈ s, ‖P.eval (x : ℂ) - g x‖ ≤ η) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P η) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (hA : A.IsHermitian),
      ProjectedUnitaryEncoding A U F F →
      (∀ i, orderedHermitianValues hA i ∈ s) →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P η) j)
          (base j) (zs j)) ≤ 2 * P.natDegree + 1) ∧
      BlockEncoding (hermitianFunction A hA g)
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P η) j)
            (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 (2 * η) := by
  obtain ⟨base, zs, hphases, hactual⟩ := complex_polynomial_qsvt_uniform_phases
    (normalizedApproximation P η) (normalizedApproximation_bounded P η hη hP)
  refine ⟨base, zs, hphases, ?_⟩
  intro H I _ _ _ _ A U F hA hAU hspectrum
  obtain ⟨hcounts, hblock⟩ := hactual H I A U F hA hAU
  refine ⟨?_, ?_⟩
  · intro j
    have hdeg : (normalizedApproximation P η).natDegree ≤ P.natDegree :=
      Polynomial.natDegree_smul_le ((1 + η)⁻¹ : ℝ) P
    exact (hcounts j).2.2.trans (by omega)
  · have hε : 0 ≤ 2 * η / (1 + η) := by positivity
    have herr : ‖hermitianFunction A hA g - aeval A (normalizedApproximation P η)‖ ≤
        2 * η / (1 + η) := by
      apply hermitian_complex_polynomial_error I A hA (normalizedApproximation P η) g _ hε
      intro i
      have hi := hspectrum i
      have h := normalized_scalar_error
        (P.eval (orderedHermitianValues hA i : ℂ)) (g (orderedHermitianValues hA i)) η
        hη (hg _ hi) (happrox _ hi)
      rw [norm_sub_rev]
      simpa only [normalizedApproximation, Polynomial.eval_smul] using h
    have h := hblock.perturb hε herr
    simp only [zero_add] at h
    apply h.mono
    exact div_le_self (by positivity) (by linarith)

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
