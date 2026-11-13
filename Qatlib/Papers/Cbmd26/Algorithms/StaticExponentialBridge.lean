/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationEntire
import Qatlib.Papers.Cbmd26.Algorithms.ApproximateQSVTBridge
import Qatlib.Papers.Cbmd26.Algorithms.PropagatorSpectralBridge
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Polynomial QSVT approximations of static exponentials

Cauchy-series truncation on the disk of radius two gives uniform polynomial approximations on
the real interval `[-1, 1]`. Applied to the oscillatory exponential, this yields shared QSVT
phases and a block encoding of Hermitian time evolution for the static samples in
[WangEtAl2026].

## Main statements

* `complexCauchyTruncation_error`: bounds the truncation error by a geometric tail.
* `static_exponential_qsvt_exists`: gives phases, branch query bounds, and an exponential block
  encoding with normalization four.

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
open Matrix Polynomial Complex Metric Set
open scoped BigOperators Matrix.Norms.L2Operator

/-- The polynomial formed from the first `N` Cauchy coefficients of `f` at zero with contour
radius two. -/
def complexCauchyTruncation (f : ℂ → ℂ) (N : ℕ) : Polynomial ℂ :=
  ∑ n ∈ Finset.range N, C (cauchyCoefficient f 0 2 n) * X ^ n

/-- The natural degree of the `N`-term Cauchy truncation is at most `N`. -/
theorem complexCauchyTruncation_degree (f : ℂ → ℂ) (N : ℕ) :
    (complexCauchyTruncation f N).natDegree ≤ N := by
  apply natDegree_sum_le_of_forall_le
  intro n hn
  exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.le_of_lt (Finset.mem_range.mp hn))

/-- For `f` differentiable on the closed disk of radius two and bounded there on the boundary by
`M`, the Cauchy truncation error at any real `|x| ≤ 1` is at most `2 * M * (1 / 2) ^ N`. -/
theorem complexCauchyTruncation_error (f : ℂ → ℂ) (M : ℝ)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (N : ℕ) (x : ℝ) (hx : |x| ≤ 1) :
    ‖(complexCauchyTruncation f N).eval (x : ℂ) - f (x : ℂ)‖ ≤
      2 * M * (1 / 2 : ℝ) ^ N := by
  have hs := cauchyCoefficient_hasSum f 0 2 (by norm_num) hf (x : ℂ)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx.trans_lt (by norm_num : (1 : ℝ) < 2))
  simp only [zero_add] at hs
  have ht (n : ℕ) : ‖cauchyCoefficient f 0 2 n * (x : ℂ) ^ n‖ ≤ M * (1/2 : ℝ)^n := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs]
    have hp : |x| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _) hx
    calc
      _ ≤ ‖cauchyCoefficient f 0 2 n‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ ≤ M * (1/2 : ℝ)^n := by
        simpa using cauchyCoefficient_norm_le f 0 2 M (by norm_num) hb n
  have he := norm_sub_le_of_geometric_bound_of_hasSum (by norm_num : (1/2 : ℝ) < 1) ht hs N
  simpa only [complexCauchyTruncation, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    using he.trans_eq (by norm_num; ring)

/-- A function differentiable on the closed disk of radius two, bounded by positive `M` on its
boundary and by one on `[-1, 1]`, has a polynomial approximation with error `ε > 0`, modulus
at most `1 + ε`, and degree at most `dyadicOrder (ε / (2 * M))` on that interval. -/
theorem full_interval_holomorphic_polynomial_exists (f : ℂ → ℂ) (M ε : ℝ)
    (hM : 0 < M) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall 0 2))
    (hb : ∀ z ∈ sphere (0 : ℂ) 2, ‖f z‖ ≤ M)
    (hr : ∀ x ∈ Icc (-1 : ℝ) 1, ‖f (x : ℂ)‖ ≤ 1) :
    ∃ P : Polynomial ℂ, P.natDegree ≤ dyadicOrder (ε / (2 * M)) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ) - f (x : ℂ)‖ ≤ ε) := by
  let N := dyadicOrder (ε / (2 * M))
  let P := complexCauchyTruncation f N
  have herr (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
      ‖P.eval (x : ℂ) - f (x : ℂ)‖ ≤ ε := by
    calc
      _ ≤ 2 * M * (1/2 : ℝ)^N := complexCauchyTruncation_error f M hf hb N x (abs_le.mpr hx)
      _ ≤ 2 * M * (ε / (2 * M)) :=
        mul_le_mul_of_nonneg_left (dyadicOrder_error (by positivity)) (by positivity)
      _ = ε := by field_simp
  refine ⟨P, complexCauchyTruncation_degree f N, ?_, herr⟩
  intro x hx
  calc
    _ ≤ ‖P.eval (x : ℂ) - f (x : ℂ)‖ + ‖f (x : ℂ)‖ := norm_le_norm_sub_add _ _
    _ ≤ ε + 1 := add_le_add (herr x hx) (hr x hx)
    _ = 1 + ε := add_comm _ _

/-- The scalar oscillatory exponential `exp (-i * τ * z)` for real frequency `τ`. -/
def oscillatoryExponential (τ : ℝ) (z : ℂ) : ℂ := Complex.exp (-Complex.I * (τ : ℂ) * z)

/-- The oscillatory exponential is differentiable on the closed disk of radius two, bounded on
its boundary by `exp (2 * |τ|)`, and has unit modulus at real arguments. -/
theorem oscillatoryExponential_properties (τ : ℝ) :
    DifferentiableOn ℂ (oscillatoryExponential τ) (closedBall 0 2) ∧
    (∀ z ∈ sphere (0 : ℂ) 2, ‖oscillatoryExponential τ z‖ ≤ Real.exp (2 * |τ|)) ∧
    (∀ x : ℝ, ‖oscillatoryExponential τ (x : ℂ)‖ = 1) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold oscillatoryExponential
    fun_prop
  · intro z hz
    apply (Complex.norm_exp_le_exp_norm _).trans
    apply Real.exp_le_exp.mpr
    have hz' : ‖z‖ = 2 := by simpa only [sub_zero] using mem_sphere_iff_norm.mp hz
    simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs, hz']
    linarith
  · intro x
    simp [oscillatoryExponential, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

/-- Applying the oscillatory exponential through the Hermitian functional calculus equals the
matrix exponential `exp ((-i * τ) • A)`. -/
theorem oscillatory_hermitian_function_eq_exp (I : Type) [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (τ : ℝ) :
    hermitianFunction A hA (fun x => oscillatoryExponential τ (x : ℂ)) =
      NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A) := by
  have he (z : ℂ) : (∑' n : ℕ, ((n.factorial : ℂ)⁻¹) * z ^ n) = Complex.exp z := by
    simpa only [smul_eq_mul, Complex.exp_eq_exp_ℂ] using
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) z).tsum_eq
  have h := hermitian_scalar_series I A hA (fun n => ((n.factorial : ℂ)⁻¹))
    (-Complex.I * (τ : ℂ)) (fun i => by
      simpa only [smul_eq_mul] using NormedSpace.expSeries_summable' (𝕂 := ℂ)
        ((-Complex.I * (τ : ℂ)) * (orderedHermitianValues hA i : ℂ)))
  simp_rw [he] at h
  rw [← congrFun (NormedSpace.exp_eq_tsum ℂ) ((-Complex.I * (τ : ℂ)) • A)] at h
  exact h

/-- For `ε > 0`, there exist polynomial and unit-modulus phase data with explicit degree and
branch query bounds, uniformly over Hermitian projected encodings. The resulting four-branch
LCU block-encodes the oscillatory matrix exponential with normalization four and error `ε`. -/
theorem static_exponential_qsvt_exists (τ ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      P.natDegree ≤ dyadicOrder ((ε / 2) / (2 * Real.exp (2 * |τ|))) ∧
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2)) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (_hA : A.IsHermitian), ProjectedUnitaryEncoding A U F F →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2)) j)
          (base j) (zs j)) ≤
        2 * dyadicOrder ((ε / 2) / (2 * Real.exp (2 * |τ|))) + 1) ∧
      BlockEncoding (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2)) j)
            (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 ε := by
  obtain ⟨hf, hb, hr⟩ := oscillatoryExponential_properties τ
  obtain ⟨P, hd, hP, he⟩ := full_interval_holomorphic_polynomial_exists
    (oscillatoryExponential τ) (Real.exp (2 * |τ|)) (ε/2)
    (Real.exp_pos _) (by positivity) hf hb (fun x _ => (hr x).le)
  obtain ⟨base, zs, hp, ha⟩ := normalized_approximation_qsvt_uniform_phases
    P (fun x => oscillatoryExponential τ (x : ℂ)) (Icc (-1 : ℝ) 1) (ε/2)
    (by positivity) hP (fun x _ => (hr x).le) he
  refine ⟨P, base, zs, hd, hp, ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  obtain ⟨hc, hblock⟩ := ha H I A U F hA hAU
    (hermitian_encoding_spectrum_interval A hA U F hAU)
  rw [oscillatory_hermitian_function_eq_exp I A hA τ] at hblock
  refine ⟨fun j => (hc j).trans (by omega), ?_⟩
  convert hblock using 1
  ring

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
