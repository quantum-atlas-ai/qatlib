/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximationAiry
import Qatlib.Papers.Cbmd26.Algorithms.ApproximationPropagators
import Qatlib.Papers.Cbmd26.Algorithms.PropagatorSpectralBridge

/-!
# Uniform polynomial approximation of second-order propagators

`SecondOrderFamily` collects the wave, Bessel, and normalized Airy propagators. This module
gives their scalar bounds, analyticity, Hermitian functional-calculus identities, and a common
polynomial degree budget for the second-order algorithms of [WangEtAl2026].

## Main statements

* `secondOrder_scalar_circle_bound`: bounds growth on the complex circle of radius two.
* `secondOrder_uniform_polynomial_exists`: gives polynomials bounded on `[-1, 1]` and accurate
  on `[g, 1]`, with a degree bound uniform over the permitted scale range.

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
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Complex Polynomial Metric Set Matrix
open scoped Matrix.Norms.L2Operator

/-- The three second-order propagator families: wave, Bessel, and Airy. -/
inductive SecondOrderFamily where
  | wave | bessel | airy
  deriving DecidableEq

/-- The wave, Bessel, or normalized Airy propagator at real time `t`, evaluated in a complete
complex normed algebra. -/
def secondOrderPropagator {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]
    (kind : SecondOrderFamily) (A : E) (t : ℝ) : E :=
  match kind with
  | .wave => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator A (t : ℂ)
  | .bessel => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator A (t : ℂ)
  | .airy => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator A (t : ℂ)

/-- The family-dependent growth time scale, equal to `t` for wave and Bessel and to
`airyTimeScale t` for Airy. -/
def secondOrderTimeScale (kind : SecondOrderFamily) (t : ℝ) : ℝ :=
  match kind with
  | .wave => t
  | .bessel => t
  | .airy => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale t

/-- The second-order time scale is nonnegative at nonnegative times. -/
theorem secondOrderTimeScale_nonneg (kind : SecondOrderFamily) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ secondOrderTimeScale kind t := by
  cases kind
  · exact ht
  · exact ht
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyTimeScale_nonneg ht

/-- The scalar second-order propagator is real-valued for real matrix parameter and time. -/
theorem secondOrder_scalar_real (kind : SecondOrderFamily) (x t : ℝ) :
    ((secondOrderPropagator kind (x : ℂ) t).re : ℂ) = secondOrderPropagator kind (x : ℂ) t := by
  cases kind
  · exact wave_scalar_real x t
  · exact bessel_scalar_real x t
  · exact airy_scalar_real x t

/-- For nonnegative scalar parameter and time, each second-order propagator has norm at most
one. -/
theorem secondOrder_scalar_pos_bound (kind : SecondOrderFamily) (x t : ℝ)
    (hx : 0 ≤ x) (ht : 0 ≤ t) : ‖secondOrderPropagator kind (x : ℂ) t‖ ≤ 1 := by
  cases kind
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator_scalar_nonneg_norm_le_one x t hx
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator_scalar_nonneg_norm_le_one x t hx
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator_scalar_nonneg_norm_le_one x t hx ht

/-- The scaled scalar second-order propagator is complex differentiable on the closed disk of
radius two. -/
theorem secondOrder_scalar_scaled_analytic (kind : SecondOrderFamily) (b t : ℝ) :
    DifferentiableOn ℂ (fun z : ℂ => secondOrderPropagator kind ((b : ℂ) * z) t) (closedBall 0 2) := by
  intro z _
  cases kind
  · have h := (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
    simpa only [zero_add, smul_eq_mul, mul_comm, secondOrderPropagator, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator]
      using! h.differentiableWithinAt
  · have h := (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.bessel_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
    simpa only [zero_add, smul_eq_mul, mul_comm, secondOrderPropagator, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator]
      using! h.differentiableWithinAt
  · have h := (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_series_affine_analytic (0 : ℂ) (b : ℂ) (t : ℂ) z).differentiableAt
    simpa only [zero_add, smul_eq_mul, mul_comm, secondOrderPropagator, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator]
      using! h.differentiableWithinAt

/-- For nonnegative scale and time, the scaled scalar propagator on the circle of radius two has
norm at most `exp (secondOrderTimeScale kind t * sqrt (2 * b))`. -/
theorem secondOrder_scalar_circle_bound (kind : SecondOrderFamily) (b t : ℝ)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 2) :
    ‖secondOrderPropagator kind ((b : ℂ) * z) t‖ ≤
      Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * b)) := by
  cases kind
  · simpa only [abs_of_nonneg ht] using! wave_scalar_circle_bound b t hb z hz
  · simpa only [abs_of_nonneg ht] using! bessel_scalar_circle_bound b t hb z hz
  · exact airy_scalar_circle_bound b t hb ht z hz

/-- The Hermitian functional calculus of the scalar scaled propagator equals the second-order
propagator of the scaled matrix. -/
theorem secondOrder_hermitian_function_eq_series (kind : SecondOrderFamily)
    (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ) (hA : A.IsHermitian) (b t : ℝ) :
    hermitianFunction A hA (fun x => secondOrderPropagator kind ((b * x : ℝ) : ℂ) t) =
      secondOrderPropagator kind ((b : ℂ) • A) t := by
  simp only [Complex.ofReal_mul]
  cases kind
  · exact wave_hermitian_function_eq_series I A hA (b : ℂ) (t : ℂ)
  · exact bessel_hermitian_function_eq_series I A hA (b : ℂ) (t : ℂ)
  · exact airy_hermitian_function_eq_series I A hA (b : ℂ) (t : ℂ)

/-- The common second-order polynomial degree budget obtained from the dyadic analytic
approximation order and a factor depending on the positive spectral threshold `g`. -/
def secondOrderDegreeBudget (kind : SecondOrderFamily) (t bmax g ε : ℝ) : ℕ :=
  dyadicOrder (ε / (4 * Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * bmax)))) *
    (1 + 4 * ⌈512 / g⌉₊)

/-- For nonnegative time and `0 ≤ b ≤ bmax`, positive `g`, and positive `ε`, a polynomial of
degree at most `secondOrderDegreeBudget kind t bmax g ε` is bounded by `1 + ε` on `[-1, 1]`
and approximates the scaled propagator within `ε` on `[g, 1]`. -/
theorem secondOrder_uniform_polynomial_exists (kind : SecondOrderFamily) (t b bmax g ε : ℝ)
    (ht : 0 ≤ t) (hb : 0 ≤ b) (hbmax : b ≤ bmax) (hg : 0 < g) (hε : 0 < ε) :
    ∃ P : Polynomial ℂ,
      P.natDegree ≤ secondOrderDegreeBudget kind t bmax g ε ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + ε) ∧
      (∀ x ∈ Icc g 1,
        ‖P.eval (x : ℂ) - secondOrderPropagator kind ((b * x : ℝ) : ℂ) t‖ ≤ ε) := by
  simp only [Complex.ofReal_mul]
  apply bounded_real_holomorphic_complex_polynomial_exists
    (fun z => secondOrderPropagator kind ((b : ℂ) * z) t) g
    (Real.exp (secondOrderTimeScale kind t * Real.sqrt (2 * bmax))) ε hg
    (Real.one_le_exp (mul_nonneg (secondOrderTimeScale_nonneg kind ht) (Real.sqrt_nonneg _))) hε
  · exact secondOrder_scalar_scaled_analytic kind b t
  · intro z hz
    apply (secondOrder_scalar_circle_bound kind b t hb ht z hz).trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hbmax (by norm_num)))
      (secondOrderTimeScale_nonneg kind ht)
  · intro x hx
    simpa only [← Complex.ofReal_mul] using!
      secondOrder_scalar_pos_bound kind (b * x) t (mul_nonneg hb hx.1) ht
  · intro x _
    simpa only [← Complex.ofReal_mul] using! secondOrder_scalar_real kind (b * x) t

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
