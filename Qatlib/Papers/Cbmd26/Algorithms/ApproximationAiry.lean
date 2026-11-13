/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationSharpQSVT
import Qatlib.Foundations.CbmdAnalysis.Core.AiryMixture

/-!
# Polynomial and QSVT approximation of the Airy propagator

`airy_bounded_polynomial_exists` approximates the scaled Airy propagator on `[g, 1]` while
controlling the polynomial on `[-1, 1]`. `airy_spectral_qsvt_exists` supplies uniform QSVT
phases, and `airy_hermitian_function_eq_series` identifies the spectral functional calculus with
the matrix series, yielding `airy_qsvt_exists` with explicit degree and query bounds.

This approximation supports the Airy dynamics studied in [WangEtAl2026].

## Main statements

* `airy_bounded_polynomial_exists` gives bounded polynomial approximation of the scalar
  propagator.
* `airy_hermitian_function_eq_series` identifies spectral and matrix-series propagators.
* `airy_qsvt_exists` supplies the corresponding uniform QSVT implementation.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Complex Polynomial Metric Set Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The scalar Airy propagator is real when both its spectral parameter and time are real. -/
theorem airy_scalar_real (x t : ℝ) :
    ((_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (x : ℂ) (t : ℂ)).re : ℂ) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (x : ℂ) (t : ℂ) := by
  apply Complex.conj_eq_iff_re.mp
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator, smul_eq_mul, Complex.conj_tsum,
    map_mul, map_pow, map_neg, Complex.conj_ofReal]

/-- For nonnegative `b` and `t`, the scaled scalar Airy propagator on the radius-two circle has
norm at most `exp (airyTimeScale t * sqrt (2 * b))`. -/
theorem airy_scalar_circle_bound (b t : ℝ) (hb : 0 ≤ b) (ht : 0 ≤ t)
    (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 2) :
    ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) * z) (t : ℂ)‖ ≤
      Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)) := by
  have hn : ‖z‖ = 2 := by simpa using! mem_sphere_iff_norm.mp hz
  simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb,
    hn, mul_comm b 2] using! _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator_norm_le_exp ((b : ℂ) * z) t ht

/-- For real `b` and `t`, the scalar Airy propagator composed with multiplication by `b` is
complex differentiable on the radius-two closed disk. -/
private theorem airy_scaled_analytic (b t : ℝ) :
    DifferentiableOn ℂ
      (fun z : ℂ => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) * z) (t : ℂ))
      (closedBall 0 2) := by
  intro z _
  have h :=
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
  simpa only [zero_add, smul_eq_mul, mul_comm, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator]
    using! h.differentiableWithinAt

/-- For nonnegative `b` and `t` and positive `g` and `ε`, there is a complex polynomial
approximating the scaled Airy propagator within `ε` on `[g, 1]` and bounded by `1 + ε` on
`[-1, 1]`. Its degree satisfies the stated dyadic budget using the circle-growth bound. -/
theorem airy_bounded_polynomial_exists (b t g ε : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hg : 0 < g) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.natDegree ≤ dyadicOrder
          (ε / (4 * Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)))) *
        (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1,
        ‖P.eval (x : ℂ) - _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b * x : ℝ) : ℂ) (t : ℂ)‖ ≤ ε) := by
  simp only [Complex.ofReal_mul]
  apply bounded_real_holomorphic_complex_polynomial_exists
    (fun z => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) * z) (t : ℂ)) g
    (Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b))) ε hg
    (Real.one_le_exp (mul_nonneg (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale_nonneg ht)
      (Real.sqrt_nonneg _))) hε
  · exact airy_scaled_analytic b t
  · exact airy_scalar_circle_bound b t hb ht
  · intro x hx
    simpa only [← Complex.ofReal_mul] using!
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator_scalar_nonneg_norm_le_one (b * x) t (mul_nonneg hb hx.1) ht
  · intro x _
    simpa only [← Complex.ofReal_mul] using! airy_scalar_real (b * x) t

/-- For nonnegative `b` and `t` and positive `g` and `ε`, there are a polynomial and four
uniform QSVT phase lists with the stated explicit degree and per-branch query bounds. For
every projected unitary encoding of a Hermitian matrix with spectrum in `[g, 1]`, their LCU
block-encodes the spectral Airy propagator with normalization `4` and error `ε`. -/
theorem airy_spectral_qsvt_exists (b t g ε : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hg : 0 < g) (hε : 0 < ε) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      P.natDegree ≤ dyadicOrder ((ε / 2) /
          (4 * Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)))) *
        (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (hA : A.IsHermitian),
      ProjectedUnitaryEncoding A U F F →
      (∀ i, orderedHermitianValues hA i ∈ Icc g 1) →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
          (base j) (zs j)) ≤
        2 * (dyadicOrder ((ε / 2) /
          (4 * Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)))) *
          (1 + 4 * ⌈512 / g⌉₊)) + 1) ∧
      BlockEncoding (hermitianFunction A hA
          (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b * x : ℝ) : ℂ) (t : ℂ)))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
            (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 ε := by
  simp only [Complex.ofReal_mul]
  apply sharp_holomorphic_qsvt_exists
    (fun z => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) * z) (t : ℂ)) g
    (Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b))) ε hg
    (Real.one_le_exp (mul_nonneg (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale_nonneg ht)
      (Real.sqrt_nonneg _))) hε
  · exact airy_scaled_analytic b t
  · exact airy_scalar_circle_bound b t hb ht
  · intro x hx
    simpa only [← Complex.ofReal_mul] using!
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator_scalar_nonneg_norm_le_one (b * x) t (mul_nonneg hb hx.1) ht
  · intro x _
    simpa only [← Complex.ofReal_mul] using! airy_scalar_real (b * x) t

/-- Each term of the Airy matrix series for a Hermitian matrix equals the spectral diagonal
matrix obtained by applying the corresponding scalar term to its eigenvalues. -/
private theorem airy_term_spectral (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (b t : ℂ) (n : ℕ) :
    (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) • (-(t ^ 3) • (b • A)) ^ n =
      spectralDiagonal (orderedHermitianBasis hA) (fun i =>
        (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) *
          (-(t ^ 3) * (b * (orderedHermitianValues hA i : ℂ))) ^ n) := by
  have h := aeval_eq_spectralDiagonal_of_action (orderedHermitianBasis hA) A _
    (orderedHermitianBasis_action hA)
    (C (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) * (C (-(t ^ 3) * b) * X) ^ n)
  simpa only [map_mul, map_pow, aeval_C, aeval_X, eval_mul, eval_pow, eval_C,
    eval_X, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_smul, mul_assoc] using! h

/-- For a finite Hermitian matrix and arbitrary complex scale and time, the spectral Airy
functional calculus equals the Airy propagator defined by the matrix series. -/
theorem airy_hermitian_function_eq_series (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (b t : ℂ) :
    hermitianFunction A hA (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (b * (x : ℂ)) t) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (b • A) t := by
  let L : (Fin (Fintype.card I) → ℂ) →ₗ[ℂ] Matrix I I ℂ :=
    { toFun := spectralDiagonal (orderedHermitianBasis hA)
      map_add' := fun f g => by
        simp only [spectralDiagonal]
        have hd : Matrix.diagonal (f + g) = Matrix.diagonal f + Matrix.diagonal g := by
          exact (Matrix.diagonal_add f g).symm
        rw [hd, Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c f => by simp [spectralDiagonal, Matrix.diagonal_smul,
        Matrix.mul_smul, Matrix.smul_mul] }
  have hs : Summable (fun n : ℕ => fun i : Fin (Fintype.card I) =>
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) *
        (-(t ^ 3) * (b * (orderedHermitianValues hA i : ℂ))) ^ n) := by
    apply Pi.summable.mpr
    intro i
    exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_series_summable
        (b * (orderedHermitianValues hA i : ℂ)) t
  have h := L.toContinuousLinearMap.map_tsum hs
  change spectralDiagonal (orderedHermitianBasis hA) (∑' n : ℕ, fun i =>
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) *
        (-(t ^ 3) * (b * (orderedHermitianValues hA i : ℂ))) ^ n) = _ at h
  have hfun : (∑' n : ℕ, fun i : Fin (Fintype.card I) =>
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) *
        (-(t ^ 3) * (b * (orderedHermitianValues hA i : ℂ))) ^ n) =
      fun i => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (b * (orderedHermitianValues hA i : ℂ)) t := by
    funext i
    exact Pi.tsum_apply hs
  rw [hfun] at h
  change hermitianFunction A hA (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator (b * (x : ℂ)) t) =
    ∑' n : ℕ, spectralDiagonal (orderedHermitianBasis hA) (fun i =>
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airySeriesCoefficient n : ℂ) *
        (-(t ^ 3) * (b * (orderedHermitianValues hA i : ℂ))) ^ n) at h
  rw [h, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator]
  apply tsum_congr
  intro n
  exact (airy_term_spectral I A hA b t n).symm

/-- For nonnegative `b` and `t` and positive `g` and `ε`, there are a polynomial and four
uniform QSVT phase lists with the stated degree and per-branch query bounds. For every
projected unitary encoding of a Hermitian matrix with spectrum in `[g, 1]`, their LCU
block-encodes `airyPropagator ((b : ℂ) • A) (t : ℂ)` with normalization `4` and error `ε`. -/
theorem airy_qsvt_exists (b t g ε : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hg : 0 < g) (hε : 0 < ε) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      P.natDegree ≤ dyadicOrder ((ε / 2) /
          (4 * Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)))) *
        (1 + 4 * ⌈512 / g⌉₊) ∧
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (hA : A.IsHermitian),
      ProjectedUnitaryEncoding A U F F →
      (∀ i, orderedHermitianValues hA i ∈ Icc g 1) →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
          (base j) (zs j)) ≤
        2 * (dyadicOrder ((ε / 2) /
          (4 * Real.exp (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t * Real.sqrt (2 * b)))) *
          (1 + 4 * ⌈512 / g⌉₊)) + 1) ∧
      BlockEncoding (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) • A) (t : ℂ))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε / 2)) j)
            (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 ε := by
  obtain ⟨P, base, zs, hd, hphase, hactual⟩ :=
    airy_spectral_qsvt_exists b t g ε hb ht hg hε
  refine ⟨P, base, zs, hd, hphase, ?_⟩
  intro H I _ _ _ _ A U F hA hAU hs
  obtain ⟨hc, hblock⟩ := hactual H I A U F hA hAU hs
  refine ⟨hc, ?_⟩
  have heq : hermitianFunction A hA
      (fun x => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b * x : ℝ) : ℂ) (t : ℂ)) =
      _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator ((b : ℂ) • A) (t : ℂ) := by
    simpa only [Complex.ofReal_mul] using!
      airy_hermitian_function_eq_series I A hA (b : ℂ) (t : ℂ)
  rw [heq] at hblock
  exact hblock

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
