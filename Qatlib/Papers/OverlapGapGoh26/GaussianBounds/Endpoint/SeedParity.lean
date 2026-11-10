/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OverlapGapGoh26.GaussianModel.RawInput
set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical BigOperators
open Qatlib.Foundations.MatrixAlgebra.TensorDiff
open Qatlib.Foundations.MatrixGeometry.AxisRotations.Rotation
open Qatlib.Papers.OverlapGapGoh26.SpinDynamics.Feedback
open Qatlib.Papers.OverlapGapGoh26.UniformGrid.RawEnergyNorm
namespace Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint

def reflectSpin (v : Fin 3→ℝ) : Fin 3→ℝ := ![v 0,-v 1,-v 2]

theorem rotation_reflect (s h : ℝ) (v : Fin 3→ℝ) :
    rotationStep s (-h)*ᵥreflectSpin v=reflectSpin (rotationStep s h*ᵥv) := by
  ext j
  fin_cases j <;>
    simp [rotationStep,driverAngle,problemAngle,reflectSpin,Matrix.mulVec,Matrix.mul_apply,dotProduct,
      Fin.sum_univ_three,mul_neg,Real.cos_neg,Real.sin_neg] <;> ring

theorem interaction_neg {r N : ℕ} (hr : Odd r)
    (J : Fin N→(Fin r→Fin N)→ℝ) (z : Fin N→ℝ) (i : Fin N) :
    interaction J (fun j=>-z j) i= -interaction J z i := by
  simp [interaction,Finset.prod_neg,hr.neg_one_pow]

theorem feedback_seed_parity {r N : ℕ} (hr : Odd r)
    (J : Fin N→(Fin r→Fin N)→ℝ) (seed : Fin N→ℝ) (s : ℕ→ℝ) (t : ℕ) :
    feedbackState id J (fun i=>-seed i) s t=
      fun i=>reflectSpin (feedbackState id J seed s t i) := by
  induction t with
  | zero =>
    funext i j
    fin_cases j <;> norm_num [feedbackState,initialSpin,reflectSpin]
  | succ t ih =>
    have hz : (fun j=>feedbackState id J (fun i=>-seed i) s t j 2)=
        fun j=>-feedbackState id J seed s t j 2 := by
      funext j
      rw [ih]
      rfl
    have hh (i:Fin N) :
        feedbackField id J (fun i=>-seed i) s t (feedbackState id J (fun i=>-seed i) s t) i=
        -feedbackField id J seed s t (feedbackState id J seed s t) i := by
      simp only [feedbackField,id_eq,hz,interaction_neg hr]
      ring
    funext i
    change rotationStep (s (t+1)) _*ᵥfeedbackState id J (fun i=>-seed i) s t i=_
    rw [hh,ih]
    exact rotation_reflect _ _ _

theorem rawSpin_seed_odd {r N : ℕ} (hr : Odd r) (s : ℕ→ℝ) (T : ℕ)
    (G : EuclideanSpace ℝ (Fin (r+1)→Fin N)) (seed : Fin N→ℝ) :
    rawSpin s T G (fun i=>-seed i)= -rawSpin s T G seed := by
  ext i
  change feedbackState id _ (fun i=>-seed i) s T i 2= -feedbackState id _ seed s T i 2
  rw [feedback_seed_parity hr]
  rfl
end Qatlib.Papers.OverlapGapGoh26.GaussianBounds.Endpoint
