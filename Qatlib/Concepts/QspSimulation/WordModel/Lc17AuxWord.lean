/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeStat
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.PhaseExistence

open Qatlib.Foundations.PureStateMath

set_option autoImplicit false

namespace Qatlib.Concepts.QspSimulation.WordModel

open Matrix

theorem lcAxisRotation_zero_angle (φ : ℝ) : lcAxisRotation φ 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lcAxisRotation]

theorem lcWord_zero_angle (phis : List ℝ) : lcWord phis 0 = 1 := by
  unfold lcWord
  have hf : ∀ (xs : List ℝ) (a : Matrix (Fin 2) (Fin 2) ℂ),
      (xs.map (fun φ => lcAxisRotation φ 0)).foldl (· * ·) a = a := by
    intro xs
    induction xs with
    | nil => intro a; rfl
    | cons φ xs ih =>
      intro a
      simpa only [List.map_cons, List.foldl_cons, lcAxisRotation_zero_angle,
        mul_one] using! ih a
  exact hf phis.reverse 1

theorem lcSignalStep_eq_adjoint {θ : ℝ} (hθ : 0 ≤ θ) (hπ : θ ≤ 2 * Real.pi) :
    lcSignalStep θ = (SignalMatrix (Real.cos (θ/2))).conjTranspose := by
  have hs : Real.sin (θ/2) = Real.sqrt (1 - Real.cos (θ/2) ^ 2) :=
    Real.sin_eq_sqrt_one_sub_cos_sq (by linarith) (by linarith)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lcSignalStep, lcAxisRotation, SignalMatrix, Matrix.conjTranspose_apply,
      hs, -Complex.ofReal_cos] <;> ring

theorem lcHad_mul_self : lcHad * lcHad = 1 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hc : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by exact_mod_cast hs
  have hnc : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lcHad, Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> first | linear_combination hc | linear_combination -hc

theorem lcPlusAmp_zero_angle (phis : List ℝ) : lcPlusAmp phis 0 = 1 := by
  simp [lcPlusAmp, lcWord_zero_angle, lcHad_mul_self]

theorem lcHalfDiffs_length (a : ℝ) (rest : List ℝ) :
    (lcHalfDiffs (a :: rest)).length = rest.length := by
  induction rest generalizing a with
  | nil => rfl
  | cons b rest ih => simp [lcHalfDiffs, ih]

theorem lcCorrectedQ_length_budget (τ ε : ℝ) : τ + 1 ≤ (lcCorrectedQ τ ε : ℝ) := by
  have hm : (⌈3 * τ⌉₊ : ℝ) + 1 ≤ (lcCorrectedQ τ ε : ℝ) := by
    exact_mod_cast le_max_left _ _
  by_cases hτ : 0 ≤ τ
  · have hc : τ ≤ (⌈3 * τ⌉₊ : ℝ) :=
      le_trans (by linarith : τ ≤ 3 * τ) (Nat.le_ceil (3 * τ))
    linarith
  · have hc : (0:ℝ) ≤ (⌈3 * τ⌉₊ : ℝ) := Nat.cast_nonneg _
    linarith

end Qatlib.Concepts.QspSimulation.WordModel
