/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HermitianMap26.Construction.Variance
import Qatlib.Papers.HermitianMap26.Construction.MainResult
import Qatlib.Concepts.KrausCompile.Sequential
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.KrausCompile.BornMoments
open Qatlib.Concepts.KrausCompile.Sequential
open scoped BigOperators ComplexOrder

namespace Qatlib.Papers.HermitianMap26.Construction

namespace SignedKraus
variable {d r : ℕ} (D : SignedKraus d r)

theorem shotWeight_cast (i : Fin (r+1)) :
    (D.shotWeight i : ℂ) = D.postProcessingWeight D.normalization i := by
  have him : (D.postProcessingWeight D.normalization i).im = 0 := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp [Complex.mul_im, D.sign_im_zero]
  apply Complex.ext
  · rfl
  · simpa only [Complex.ofReal_im] using him.symm

def asStage (hd : 0 < d) : Stage d where
  n := r+1
  K := D.compiledFamily
  complete := D.compiledFamily_complete hd
  w := D.shotWeight

theorem asStage_completion_zero (hd : 0 < d) : (D.asStage hd).w (Fin.last r) = 0 := by
  simp [asStage, shotWeight]

theorem asStage_weightedLinear (hd : 0 < d) (ρ : Op d) :
    weightedLinear (D.asStage hd) ρ = D.action ρ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_trace_mul_eq_zero
  intro O
  rw [Matrix.sub_mul, Matrix.trace_sub]
  apply sub_eq_zero.mpr
  calc
    _ = ∑ i, D.postProcessingWeight D.normalization i *
        (D.compiledFamily i * ρ * (D.compiledFamily i)ᴴ * O).trace := by
      simp only [weightedLinear, asStage, LinearMap.sum_apply, LinearMap.smul_apply,
        conjBranch_apply, Finset.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul, D.shotWeight_cast]
    _ = (D.action ρ * O).trace := (D.trace_completed_postprocessing hd ρ O).symm
end SignedKraus

structure StageInput (d : ℕ) where
  r : ℕ
  data : SignedKraus d r

def physicalStages {d : ℕ} (inputs : List (StageInput d)) (hd : 0 < d) : List (Stage d) :=
  inputs.map (fun s => s.data.asStage hd)

def targetSequence {d : ℕ} : List (StageInput d) → Op d → Op d
  | [], ρ => ρ
  | s :: ss, ρ => targetSequence ss (s.data.action ρ)

theorem physicalStages_target {d : ℕ} (inputs : List (StageInput d)) (hd : 0 < d) (ρ : Op d) :
    composedWeighted (physicalStages inputs hd) ρ = targetSequence inputs ρ := by
  induction inputs generalizing ρ with
  | nil => rfl
  | cons s ss ih =>
    change composedWeighted (physicalStages ss hd) (weightedLinear (s.data.asStage hd) ρ) = _
    rw [s.data.asStage_weightedLinear hd, ih]
    rfl

theorem successive_postprocessing {d : ℕ} (inputs : List (StageInput d)) (hd : 0 < d)
    (ρ : Op d) (hρ : IsDensityOperator ρ) (V : Op d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (eig : Fin d → ℝ) :
    (∑ x : Hist (physicalStages inputs hd) × Fin d,
      (finalJointLaw (physicalStages inputs hd) (spectralReadout V hV) hρ x).toReal *
        finalValue (physicalStages inputs hd) eig x) =
          (targetSequence inputs ρ * observable V eig).trace.re := by
  rw [final_observable_expectation, physicalStages_target]

end Qatlib.Papers.HermitianMap26.Construction
