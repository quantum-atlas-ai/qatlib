/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.PiecewiseRepresentation
import Qatlib.Papers.Cbmd26.Algorithms.StaticKernelFamily

/-!
# Finite kernel sums for time-dependent evolution

Defines the real-frequency unitary samples `dynamicKernelSample` and their finite sum
`dynamicKernelLCU` for a piecewise continuous time-dependent evolution. Hermitian component
bounds give complex-parameter growth control, approximation of the dissipative target, and
contraction of that target. These results support the contour-based algorithms of
[WangEtAl2026].

## Main statements

* `dynamicKernel_target_error`: bounds finite-kernel approximation error.
* `dynamicKernel_sample_unitary`: establishes unitarity of each real-frequency sample.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace CBMD
open Matrix MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {I : Type} [Fintype I] [DecidableEq I]

/-- For Hermitian `L` and `H`, the norm of `L` is at most the norm of `L + iH`. -/
theorem hermitian_part_norm_le_original (L H : Matrix I I ℂ)
    (hL : L.IsHermitian) (hH : H.IsHermitian) : ‖L‖ ≤ ‖L + Complex.I • H‖ := by
  have he : (1/2 : ℝ) • ((L + Complex.I • H) + (L + Complex.I • H)ᴴ) = L := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, hL.eq, hH.eq]
    simp only [Complex.star_def, Complex.conj_I, neg_smul]
    module
  calc
    ‖L‖ = ‖(1/2 : ℝ) • ((L + Complex.I • H) + (L + Complex.I • H)ᴴ)‖ := congrArg norm he.symm
    _ = (1/2 : ℝ) * ‖(L + Complex.I • H) + (L + Complex.I • H)ᴴ‖ := by rw [norm_smul]; norm_num
    _ ≤ (1/2 : ℝ) * (‖L + Complex.I • H‖ + ‖(L + Complex.I • H)ᴴ‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = _ := by rw [Matrix.l2_opNorm_conjTranspose]; ring

variable {H L : ℝ → Matrix I I ℂ} {T : ℝ}

/-- Evaluates the piecewise continuous evolution at a chosen real kernel frequency and terminal
time. -/
def dynamicKernelSample (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (α δ : ℝ) (j : StaticKernelIndex α T δ) : Matrix I I ℂ :=
  P.evolution (staticKernelFrequency α T δ j : ℂ) T

/-- Forms the finite weighted sum of the dynamic kernel samples. -/
def dynamicKernelLCU (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (α δ : ℝ) : Matrix I I ℂ :=
  ∑ j, staticKernelWeight α T δ j • dynamicKernelSample P α δ j

/-- A pointwise norm bound `α` on `L` over `[0, T]` bounds its norm integral by `T * α` for
nonnegative `T`. -/
theorem dynamicKernel_norm_integral_bound
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (ht : 0 ≤ T) {α : ℝ} (hbound : ∀ u ∈ Icc 0 T, ‖L u‖ ≤ α) :
    (∫ u in 0..T, ‖L u‖) ≤ T * α := by
  have hb := intervalIntegral.integral_mono_on ht P.original_l_norm_intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => α) volume 0 T) hbound
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using! hb

/-- Under the stated Hermitian, positivity, and original-matrix norm bounds, the evolution norm
is at most `exp (max (Im z) 0 * T * α)`. -/
theorem dynamicKernel_growth
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (ht : 0 ≤ T) (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) {α : ℝ}
    (hbound : ∀ u ∈ Icc 0 T, ‖L u + Complex.I • H u‖ ≤ α) (z : ℂ) :
    ‖P.evolution z T‖ ≤ Real.exp (max z.im 0 * (T * α)) := by
  have hi := dynamicKernel_norm_integral_bound P ht
    (fun u hu => (hermitian_part_norm_le_original (L u) (H u) (hL u hu).isHermitian (hH u hu)).trans
      (hbound u hu))
  exact (P.evolution_norm_le hH hL z).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi (le_max_right _ _)))

/-- The indexed dynamic kernel LCU equals the integer-indexed LCU sum with the chosen order,
spacing, and cutoff. -/
theorem dynamicKernelLCU_eq_integerLCU
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T) (α δ : ℝ) :
    dynamicKernelLCU P α δ = _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerLCUSum (staticKernelOrder δ)
      (staticKernelSpacing α T δ) (staticKernelCutoff α T δ) (fun z => P.evolution z T) := by
  unfold dynamicKernelLCU dynamicKernelSample staticKernelWeight staticKernelFrequency
  rw [← Finset.sum_subtype (Finset.Icc (-(staticKernelCutoff α T δ : ℤ))
    (staticKernelCutoff α T δ)) (fun _ => Iff.rfl)
    (fun k : ℤ => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerWeight (staticKernelOrder δ)
      (staticKernelSpacing α T δ) ((k : ℝ) / staticKernelSpacing α T δ) •
      P.evolution (((k : ℝ) / staticKernelSpacing α T δ : ℝ) : ℂ) T)]
  rfl

/-- The finite dynamic kernel LCU approximates the dissipative evolution within operator error
`δ` under the stated regularity, positivity, and norm bounds [WangEtAl2026]. -/
theorem dynamicKernel_target_error
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (ht : 0 ≤ T) (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) {α δ : ℝ}
    (hbound : ∀ u ∈ Icc 0 T, ‖L u + Complex.I • H u‖ ≤ α)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ‖P.evolution (-Complex.I) T - dynamicKernelLCU P α δ‖ ≤ δ := by
  rw [dynamicKernelLCU_eq_integerLCU]
  exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.integerLCU_target_error_le (T * α) hδ hδ1
    (fun z => P.evolution z T) P.evolution_differentiable_parameter
    (dynamicKernel_growth P ht hH hL hbound)

/-- Each real-frequency dynamic kernel sample is unitary under the stated Hermitian and positive
semidefinite component assumptions. -/
theorem dynamicKernel_sample_unitary
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) (α δ : ℝ) (j : StaticKernelIndex α T δ) :
    dynamicKernelSample P α δ j ∈ Matrix.unitaryGroup I ℂ :=
  P.evolution_real_unitary hH hL _

/-- The dissipative target evolution has operator norm at most one under the stated component
assumptions. -/
theorem dynamicKernel_target_contraction
    (P : _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.FinitePiecewiseContinuousOn (fun u => (H u,L u)) 0 T)
    (hH : ∀ u ∈ Icc 0 T, (H u).IsHermitian)
    (hL : ∀ u ∈ Icc 0 T, (L u).PosSemidef) :
    ‖P.evolution (-Complex.I) T‖ ≤ 1 := by
  simpa using! P.evolution_norm_le hH hL (-Complex.I)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
