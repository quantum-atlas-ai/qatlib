/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QFVMChen22.TimeStep.StencilSpectrum
public import Qatlib.Concepts.WalkSearch.MultiBandFilter.MultiBandPhaseFilter
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Absolute spectral thresholds from walk phases

[ChenXueChenEtAl2022], Appendix C.3, uses the gapped phase discrimination
of [ChildsKothariSomma2017], Section 5. For the two conjugate branches of a
stencil walk, the cosine of either phase angle is the same eigenvalue.
This module gives a separated threshold test on the finite counter grid
and an error bound for the counted phase-estimation reflection. Stage
control, the bin-specific inverse, and its clock cost require separate
circuits.

[Published paper](https://doi.org/10.1007/s11128-022-03478-w)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QFVMChen22.TimeStep

open Matrix
open Qatlib.Foundations.PureStateMath (Inner Normalized QState normalized_iff_inner_self)
open Qatlib.Concepts.PolynomialCalc.QubitizedPower (walk)
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT (walkBranch)
open Qatlib.Concepts.QsvtCore.PhaseExistence (sparseAlpha)
open Qatlib.Foundations.QramData.SquaredNormTree (Address)
open Qatlib.Papers.QFVMChen22.QramStorage (Geometry)
open Qatlib.Foundations.PureStateMath.BornBridge (toEuclidean_fromVec)
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout (phaseDistance)
open Qatlib.Concepts.WalkSearch.MultiBandFilter (bandClassificationGap bandEmbed bandReflected
  multiband_actual_coherent_reflection_error)
open scoped BigOperators Classical

/-- Decoding the cosine of a phase is Lipschitz for circular distance, including
when the nearest representative crosses the phase counter's zero label. -/
private theorem cos_phase_distance_le (x y : ℝ) :
    |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)| ≤
      (2 * Real.pi) * phaseDistance x y := by
  let k : ℤ := ⌊x - y + 1 / 2⌋
  have hPeriodic := Real.cos_add_int_mul_two_pi (2 * Real.pi * y) k
  have hDiff : 2 * Real.pi * (x - y - (k : ℝ)) =
      2 * Real.pi * x - (2 * Real.pi * y + (k : ℝ) * (2 * Real.pi)) := by ring
  calc
    _ = |Real.cos (2 * Real.pi * x) -
        Real.cos (2 * Real.pi * y + (k : ℝ) * (2 * Real.pi))| := by
      rw [hPeriodic, abs_sub_comm]
    _ ≤ |2 * Real.pi * x - (2 * Real.pi * y + (k : ℝ) * (2 * Real.pi))| := Real.abs_cos_sub_cos_le _ _
    _ = _ := by
      change _ = (2 * Real.pi) * |x - y - (k : ℝ)|
      rw [← hDiff, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

/-- Counted labels whose cosine decodes an eigenvalue magnitude at or above the threshold. -/
def magnitudeThresholdLabels (M : ℕ) (threshold : ℝ) : Finset (Fin M) :=
  Finset.univ.filter fun y => threshold ≤ |Real.cos (2 * Real.pi * ((y.val : ℝ) / M))|

/-- A separated absolute-eigenvalue threshold can be classified directly from the
phase counter of either conjugate branch of the walk. -/
theorem magnitude_threshold_classification_gap {J : Type} [Fintype J] [DecidableEq J]
    (M : ℕ) (phase eigenvalue : J → ℝ) (threshold η : ℝ)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold)) :
    bandClassificationGap M (magnitudeThresholdLabels M threshold) phase (Finset.univ.filter fun j => threshold ≤ |eigenvalue j|) η := by
  intro j y hy
  let estimated := |Real.cos (2 * Real.pi * ((y.val : ℝ) / M))|
  have hError : abs (estimated - |eigenvalue j|) ≤ 2 * Real.pi * η := by
    rw [← hCos j]
    exact (abs_abs_sub_abs_le_abs_sub _ _).trans
      ((cos_phase_distance_le _ _).trans (mul_le_mul_of_nonneg_left hy (by positivity)))
  simp only [magnitudeThresholdLabels, Finset.mem_filter, Finset.mem_univ, true_and]
  change threshold ≤ estimated ↔ threshold ≤ |eigenvalue j|
  have hBound := abs_le.mp hError
  have hGap := hMargin j
  by_cases hj : threshold ≤ |eigenvalue j|
  · rw [abs_of_nonneg (sub_nonneg.mpr hj)] at hGap
    exact iff_of_true (by linarith [hBound.1]) hj
  · rw [abs_of_neg (sub_neg.mpr (lt_of_not_ge hj))] at hGap
    exact iff_of_false (by linarith [hBound.2]) hj

/-- The signed qubitized eigenphase in turns. -/
def stencilEigenphase (eigenvalue : ℝ) (neg : Bool) : ℝ :=
  (if neg then -Real.arccos eigenvalue else Real.arccos eigenvalue) / (2 * Real.pi)

/-- Converting a qubitized phase from turns back to radians recovers its signed angle. -/
private theorem stencil_eigenphase_angle (eigenvalue : ℝ) (neg : Bool) :
    2 * Real.pi * stencilEigenphase eigenvalue neg =
      if neg then -Real.arccos eigenvalue else Real.arccos eigenvalue := by
  unfold stencilEigenphase
  exact mul_div_cancel₀ _ (by positivity)

/-- The cosine decoder recovers the same stencil eigenvalue for either sign of the phase. -/
theorem stencil_phase_cos (eigenvalue : ℝ) (hLo : -1 ≤ eigenvalue) (hHi : eigenvalue ≤ 1) (neg : Bool) :
    Real.cos (2 * Real.pi * stencilEigenphase eigenvalue neg) = eigenvalue := by
  rw [stencil_eigenphase_angle]
  cases neg <;> simp [Real.cos_arccos hLo hHi]

/-- Applying the actual counted phase reflection to a separated magnitude threshold approximates
the sign on the eigenspaces above that threshold. -/
theorem counted_magnitude_reflection_error {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (M : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ) (phase eigenvalue : J → ℝ)
    (threshold η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2)
    (hCos : ∀ j, Real.cos (2 * Real.pi * phase j) = eigenvalue j)
    (hMargin : ∀ j, 2 * Real.pi * η < abs (|eigenvalue j| - threshold))
    (hOrthogonal : ∀ j l, Inner (v j) (v l) = if j = l then 1 else 0)
    (hNorm : (∑ j, ‖c j‖ ^ 2) = 1)
    (hSpectrum : ∀ j, U *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (phase j : ℂ)) • v j) :
    let labels := magnitudeThresholdLabels M threshold
    ‖toEuclidean_fromVec (bandReflected U M (by omega) labels (∑ j, c j • v j) -
      bandEmbed M (by omega) (∑ j, (if threshold ≤ |eigenvalue j| then c j else -c j) • v j))‖ ≤
        1 / (Real.sqrt M * η) := by
  intro labels
  let target := Finset.univ.filter fun j => threshold ≤ |eigenvalue j|
  have hGap : bandClassificationGap M labels phase target η :=
    magnitude_threshold_classification_gap M phase eigenvalue threshold η hCos hMargin
  simpa only [target, Finset.mem_filter, Finset.mem_univ, true_and] using
    multiband_actual_coherent_reflection_error I J U M hM labels v c phase target η
      hU hη hHalf hGap hOrthogonal hNorm hSpectrum

variable {depth columnSlots : ℕ}

/-- A separated threshold on an interior stencil eigenvalue implements the corresponding
sign on either normalized branch, up to the counted phase-reflection error. -/
theorem stencil_branch_magnitude_reflection_error (geometry : Geometry depth)
    (coefficients : Address depth → Fin geometry.stencilSize → ℝ) (entryScale : ℝ)
    (rowScratch : Fin geometry.stencilSize) (columnScratch : Fin columnSlots)
    (hScale : 0 < entryScale)
    (hEntry : ∀ row column, |stencilMatrix geometry coefficients row column| ≤ entryScale)
    (hColumns : ∀ column, (geometry.affected column).dedup.length ≤ columnSlots)
    (j : Address depth ⊕ Address depth) (neg : Bool) (M : ℕ) (hM : 2 ≤ M)
    (threshold η : ℝ) (hη : 0 < η) (hHalf : η ≤ 1 / 2) :
    let G := stencilWalkFrame depth rowScratch columnScratch
    let U := stencilWalkInvolution geometry coefficients entryScale rowScratch columnScratch
    let h := stencil_signal_hermitian geometry coefficients (entryScale * sparseAlpha geometry.stencilSize columnSlots)
    let S : Matrix (Address depth ⊕ Address depth) (Address depth ⊕ Address depth) ℂ := h.eigenvectorUnitary
    let eigenvalue := h.eigenvalues j
    let v := walkBranch U (G *ᵥ (fun i => S i j)) eigenvalue neg
    |eigenvalue| < 1 → 2 * Real.pi * η < abs (|eigenvalue| - threshold) →
      ‖toEuclidean_fromVec (bandReflected (walk G U) M (by omega) (magnitudeThresholdLabels M threshold) v -
        bandEmbed M (by omega) (if threshold ≤ |eigenvalue| then v else -v))‖ ≤
          1 / (Real.sqrt M * η) := by
  intro G U h S eigenvalue v hInterior hMargin
  have hResolution :=
    stencil_walk_spectral_resolution geometry coefficients entryScale rowScratch columnScratch hScale hEntry hColumns
  obtain ⟨hNorm, hSpectrum⟩ := hResolution.2.1 j hInterior neg
  have hSpectrum' : walk G U *ᵥ v =
      Complex.exp (2 * Real.pi * Complex.I * (stencilEigenphase eigenvalue neg : ℂ)) • v := by
    have hPhase : 2 * (Real.pi : ℂ) * Complex.I * (stencilEigenphase eigenvalue neg : ℂ) =
        Complex.I * ((if neg then -Real.arccos eigenvalue else Real.arccos eigenvalue : ℝ) : ℂ) := calc
      _ = Complex.I * ((2 * Real.pi * stencilEigenphase eigenvalue neg : ℝ) : ℂ) := by push_cast; ring
      _ = _ := by rw [stencil_eigenphase_angle]
    rw [hPhase]
    exact hSpectrum
  have hRange := abs_lt.mp hInterior
  have hCos := stencil_phase_cos eigenvalue hRange.1.le hRange.2.le neg
  have hInner : Inner v v = 1 := (normalized_iff_inner_self v).mp hNorm
  simpa [ite_smul] using counted_magnitude_reflection_error (J := Unit) (walk G U) hResolution.1 M hM
    (fun _ => v) (fun _ => (1 : ℂ)) (fun _ => stencilEigenphase eigenvalue neg) (fun _ => eigenvalue)
    threshold η hη hHalf (fun _ => hCos) (fun _ => hMargin)
    (fun a b => by cases a; cases b; simp [hInner]) (by simp) (fun _ => hSpectrum')

end Qatlib.Papers.QFVMChen22.TimeStep
