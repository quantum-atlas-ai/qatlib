/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.CoherentAA.VariableTimeAmplificationDefs
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.VariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.StructuralEstimateCompilationVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.CascadePrefixTransportVari
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.RecordDrivenVariableTimeAlgorithmVari
import Qatlib.Papers.VarTimeAmpAmp10.Estimate.EstimateSandwichVari
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.AverageStopTailBoundVari
import Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound.InitialStatePrepLowerBoundLows
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# Fourier window symmetries and square completion

This module proves periodicity and parity identities for finite Fourier cosine and sine sums.
These analytic helpers extend a window bound to all real angles and construct complementary
periodic functions, in support of the variable-time development associated with [Ambainis2012].

## Main statements

* `clause78_window_global`: extension of a principal-window bound to all angles.
* `clause78_square_completion`: even and odd periodic functions completing the squared sum to
  one.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ProbabilityCore.Concentration

set_option autoImplicit false

open Matrix Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.Estimate
open Qatlib.Papers.VarTimeAmpAmp10.StopModel
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open scoped Classical BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
set_option warningAsError false
noncomputable section

/-- The finite Fourier cosine sum is invariant under adding `2 * π` to its angle. -/
lemma clause78_fourierCos_periodic (n : ℕ) (ac : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierCos n ac (θ + 2 * Real.pi) = fourierCos n ac θ := by
  simp only [fourierCos]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have : (k.val : ℝ) * (θ + 2 * Real.pi)
      = (k.val : ℝ) * θ + ((k.val : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [this, Real.cos_add_int_mul_two_pi]
end
noncomputable section

/-- The finite Fourier sine sum is invariant under adding `2 * π` to its angle. -/
lemma clause78_fourierSin_periodic (n : ℕ) (as : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierSin n as (θ + 2 * Real.pi) = fourierSin n as θ := by
  simp only [fourierSin]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have : (k.val : ℝ) * (θ + 2 * Real.pi)
      = (k.val : ℝ) * θ + ((k.val : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [this, Real.sin_add_int_mul_two_pi]
end
noncomputable section

/-- The finite Fourier cosine sum is an even function of its angle. -/
lemma clause78_fourierCos_neg (n : ℕ) (ac : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierCos n ac (-θ) = fourierCos n ac θ := by
  simp only [fourierCos]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [mul_neg, Real.cos_neg]
end
noncomputable section

/-- The finite Fourier sine sum is an odd function of its angle. -/
lemma clause78_fourierSin_neg (n : ℕ) (as : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierSin n as (-θ) = - fourierSin n as θ := by
  simp only [fourierSin]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_neg, Real.sin_neg]
  ring
end
noncomputable section

/-- Replacing an angle by `2 * π - θ` leaves the finite Fourier cosine sum unchanged. -/
lemma clause78_fourierCos_two_pi_sub (n : ℕ) (ac : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierCos n ac (2 * Real.pi - θ) = fourierCos n ac θ := by
  simp only [fourierCos]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h1 : (k.val : ℝ) * (2 * Real.pi - θ)
      = -((k.val : ℝ) * θ - ((k.val : ℤ) : ℝ) * (2 * Real.pi)) := by
    push_cast
    ring
  rw [h1, Real.cos_neg, Real.cos_sub_int_mul_two_pi]
end
noncomputable section

/-- Replacing an angle by `2 * π - θ` negates the finite Fourier sine sum. -/
lemma clause78_fourierSin_two_pi_sub (n : ℕ) (as : Fin (n + 1) → ℝ) (θ : ℝ) :
    fourierSin n as (2 * Real.pi - θ) = - fourierSin n as θ := by
  simp only [fourierSin]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (k.val : ℝ) * (2 * Real.pi - θ)
      = -((k.val : ℝ) * θ - ((k.val : ℤ) : ℝ) * (2 * Real.pi)) := by
    push_cast
    ring
  rw [h1, Real.sin_neg, Real.sin_sub_int_mul_two_pi]
  ring
end
noncomputable section

/-- Subtracting any integer multiple of `2 * π` leaves the finite Fourier cosine sum unchanged. -/
lemma clause78_fourierCos_sub_int (n : ℕ) (ac : Fin (n + 1) → ℝ) (θ : ℝ) (m : ℤ) :
    fourierCos n ac (θ - m * (2 * Real.pi)) = fourierCos n ac θ := by
  simp only [fourierCos]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h1 : (k.val : ℝ) * (θ - m * (2 * Real.pi))
      = (k.val : ℝ) * θ - (((k.val : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h1, Real.cos_sub_int_mul_two_pi]
end
noncomputable section

/-- Subtracting any integer multiple of `2 * π` leaves the finite Fourier sine sum unchanged. -/
lemma clause78_fourierSin_sub_int (n : ℕ) (as : Fin (n + 1) → ℝ) (θ : ℝ) (m : ℤ) :
    fourierSin n as (θ - m * (2 * Real.pi)) = fourierSin n as θ := by
  simp only [fourierSin]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  have h1 : (k.val : ℝ) * (θ - m * (2 * Real.pi))
      = (k.val : ℝ) * θ - (((k.val : ℤ) * m : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h1, Real.sin_sub_int_mul_two_pi]
end
noncomputable section

/-- A bound by one on the sum of squared Fourier cosine and sine sums for `|θ| ≤ π` extends to
every real angle. -/
lemma clause78_window_global (n : ℕ) (ac as : Fin (n + 1) → ℝ)
    (hwin : ∀ θ : ℝ, abs θ ≤ Real.pi →
      (fourierCos n ac θ) ^ 2 + (fourierSin n as θ) ^ 2 ≤ 1) :
    ∀ θ : ℝ, (fourierCos n ac θ) ^ 2 + (fourierSin n as θ) ^ 2 ≤ 1 := by
  intro θ
  have h2pos : 0 < 2 * Real.pi := by positivity

  set q : ℤ := Int.floor (θ / (2 * Real.pi))
  have hq : (q : ℝ) ≤ θ / (2 * Real.pi) := Int.floor_le _
  have hq' : θ / (2 * Real.pi) < (q : ℝ) + 1 := Int.lt_floor_add_one _
  have hq2 : (q : ℝ) * (2 * Real.pi) ≤ θ := (le_div_iff₀ h2pos).mp hq
  have hq3 : θ < ((q : ℝ) + 1) * (2 * Real.pi) := (div_lt_iff₀ h2pos).mp hq'
  set θ₀ : ℝ := θ - q * (2 * Real.pi) with hθ₀
  have hθ₀0 : 0 ≤ θ₀ := by
    rw [hθ₀]
    nlinarith
  have hθ₀lt : θ₀ < 2 * Real.pi := by
    rw [hθ₀]
    nlinarith

  have hper : (fourierCos n ac θ) ^ 2 + (fourierSin n as θ) ^ 2
      = (fourierCos n ac θ₀) ^ 2 + (fourierSin n as θ₀) ^ 2 := by
    rw [hθ₀, clause78_fourierCos_sub_int n ac θ q, clause78_fourierSin_sub_int n as θ q]
  rw [hper]
  by_cases hle : θ₀ ≤ Real.pi
  · exact hwin θ₀ (by simpa [abs_of_nonneg hθ₀0] using! hle)
  · have hsub : 2 * Real.pi - θ₀ ≤ Real.pi := by
      have : Real.pi < θ₀ := lt_of_not_ge hle
      linarith
    have hsub0 : 0 ≤ 2 * Real.pi - θ₀ := by linarith
    have hcalc : (fourierCos n ac θ₀) ^ 2 + (fourierSin n as θ₀) ^ 2
        = (fourierCos n ac (2 * Real.pi - θ₀)) ^ 2
          + (fourierSin n as (2 * Real.pi - θ₀)) ^ 2 := by
      rw [hθ₀, clause78_fourierCos_two_pi_sub, clause78_fourierSin_two_pi_sub, neg_sq]
    rw [hcalc]
    exact hwin (2 * Real.pi - θ₀) (by simpa [abs_of_nonneg hsub0] using! hsub)
end
noncomputable section

/-- A principal-window bound yields an even periodic function `b` and an odd periodic function
`d` whose squared values complete the two Fourier squares to one. -/
lemma clause78_square_completion (n : ℕ) (ac as : Fin (n + 1) → ℝ)
    (hwin : ∀ θ : ℝ, abs θ ≤ Real.pi →
      (fourierCos n ac θ) ^ 2 + (fourierSin n as θ) ^ 2 ≤ 1) :
    ∃ (b d : ℝ → ℝ),
      (∀ θ : ℝ, b (θ + 2 * Real.pi) = b θ) ∧
      (∀ θ : ℝ, b (-θ) = b θ) ∧
      (∀ θ : ℝ, d (θ + 2 * Real.pi) = d θ) ∧
      (∀ θ : ℝ, d (-θ) = -d θ) ∧
      (∀ θ : ℝ,
        (fourierCos n ac θ) ^ 2 + (b θ) ^ 2 +
          (fourierSin n as θ) ^ 2 + (d θ) ^ 2 = 1) := by
  refine ⟨(fun θ => Real.sqrt (1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2)),
    (fun _ => 0), ?_, ?_, ?_, ?_, ?_⟩
  · intro θ
    show Real.sqrt (1 - (fourierCos n ac (θ + 2 * Real.pi)) ^ 2
        - (fourierSin n as (θ + 2 * Real.pi)) ^ 2)
      = Real.sqrt (1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2)
    rw [clause78_fourierCos_periodic, clause78_fourierSin_periodic]
  · intro θ
    show Real.sqrt (1 - (fourierCos n ac (-θ)) ^ 2 - (fourierSin n as (-θ)) ^ 2)
      = Real.sqrt (1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2)
    rw [clause78_fourierCos_neg, clause78_fourierSin_neg, neg_sq]
  · intro θ
    rfl
  · intro θ
    simp
  · intro θ
    have hle := clause78_window_global n ac as hwin θ
    have hnonneg : 0 ≤ 1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2 := by linarith
    have hsq : (Real.sqrt (1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2)) ^ 2
        = 1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2 :=
      Real.sq_sqrt hnonneg
    show (fourierCos n ac θ) ^ 2 +
        (Real.sqrt (1 - (fourierCos n ac θ) ^ 2 - (fourierSin n as θ) ^ 2)) ^ 2 +
        (fourierSin n as θ) ^ 2 + (0:ℝ) ^ 2 = 1
    linarith [hsq]
end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
