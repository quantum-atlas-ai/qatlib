/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeStat
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWordBridge
open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.WordModel

open Matrix

section Bridge

theorem lcSignalStep_unitary (θ : ℝ) :
    lcSignalStep θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  have hcos : (Real.cos (θ/2)) ^ 2 + (Real.sin (θ/2)) ^ 2 = 1 :=
    by linear_combination Real.sin_sq_add_cos_sq (θ/2)
  have hsin : (Real.sin (θ/2)) ^ 2 = 1 - (Real.cos (θ/2)) ^ 2 := by linear_combination hcos
  have hentry : ∀ i j : Fin 2, lcSignalStep θ i j =
      if i = j then ((Real.cos (θ/2) : ℂ)) else -(Complex.I * ((Real.sin (θ/2) : ℂ))) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [lcSignalStep, lcAxisRotation]
  have hc2 : (((Real.cos (θ/2) : ℂ)))^2 + (((Real.sin (θ/2) : ℂ)))^2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add]
    exact_mod_cast hcos
  have e00 : lcSignalStep θ 0 0 = ((Real.cos (θ/2) : ℂ)) := by
    simp [lcSignalStep, lcAxisRotation]
  have e01 : lcSignalStep θ 0 1 = -(Complex.I * ((Real.sin (θ/2) : ℂ))) := by
    simp [lcSignalStep, lcAxisRotation]
  have e10 : lcSignalStep θ 1 0 = -(Complex.I * ((Real.sin (θ/2) : ℂ))) := by
    simp [lcSignalStep, lcAxisRotation]
  have e11 : lcSignalStep θ 1 1 = ((Real.cos (θ/2) : ℂ)) := by
    simp [lcSignalStep, lcAxisRotation]
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  ext a b
  fin_cases a <;> fin_cases b <;>
    (norm_num;
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, RCLike.star_def,
        map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, neg_neg,
        Fin.sum_univ_two, Matrix.one_apply, e00, e01, e10, e11, if_true, if_false,
        sub_zero, mul_zero, add_zero, zero_add, mul_one, one_mul])
  · linear_combination hc2 - ((Real.sin (θ/2) : ℂ))^2 * Complex.I_mul_I
  · ring
  · ring
  · linear_combination hc2 - ((Real.sin (θ/2) : ℂ))^2 * Complex.I_mul_I

theorem lcAxisRotation_unitary (φ θ : ℝ) :
    lcAxisRotation φ θ ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [lcAxisRotation_factor]
  exact Submonoid.mul_mem _
    (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_unitary _)
    (Submonoid.mul_mem _ (lcSignalStep_unitary θ) (Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.phaseRotation_unitary _))

end Bridge

theorem equation1WordBridge : Equation1WordBridge := by
  intro phis θ
  refine ⟨?_, fun h1 h2 => lcSignalStep_eq_adjoint h1 h2, lcWord_zero_angle phis, ?_⟩
  · intro hne hθ1 hθ2
    obtain ⟨φ, rest, rfl⟩ : ∃ φ rest, phis = φ :: rest := by
      cases phis with
      | nil => exact absurd rfl hne
      | cons φ rest => exact ⟨φ, rest, rfl⟩
    have hrevne : (φ :: rest).reverse ≠ [] := by simp
    obtain ⟨x, xs, hx⟩ : ∃ x xs, (φ :: rest).reverse = x :: xs := by
      cases h : (φ :: rest).reverse with
      | nil => rw [h] at hrevne; exact absurd rfl hrevne
      | cons w ws => exact ⟨w, ws, rfl⟩
    have hlastEq : (x :: xs).getLast (by simp) = φ := by
      have h1 : ((φ :: rest).reverse).getLast? = some φ := List.getLast?_reverse
      rw [hx] at h1
      have h2 : (x :: xs).getLast? = some ((x :: xs).getLast (by simp)) :=
          List.getLast?_eq_some_getLast _
      rw [h2] at h1
      simpa using! h1
    have hheadAll : ∀ hp : (φ :: rest) ≠ [], x = (φ :: rest).getLast hp := by
      intro hp
      have h1 : ((φ :: rest).reverse).head? = some ((φ :: rest).getLast hp) := by
        rw [List.head?_reverse, List.getLast?_eq_some_getLast]
      rw [hx, List.head?_cons] at h1
      simpa using! h1
    have htel := lcFold_telescope (lcSignalStep θ) xs x φ hlastEq
    have hmap : ((φ :: rest).reverse.map (fun w =>
          Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (-(w/2)) * (lcSignalStep θ *
            Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs.PhaseRotation (w/2)))).prod
        = ((φ :: rest).reverse.map (fun w => lcAxisRotation w θ)).prod := by
      rw [List.map_congr_left (fun w _ => (lcAxisRotation_factor w θ).symm)]
    have hprod : ((φ :: rest).reverse.map (fun w => lcAxisRotation w θ)).prod
        = lcWord (φ :: rest) θ := by
      show ((φ :: rest).reverse.map (fun w => lcAxisRotation w θ)).prod
          = ((φ :: rest).reverse.map (fun w => lcAxisRotation w θ)).foldl (· * ·) 1
      exact List.prod_eq_foldl
    have hQ := lcWordTilde_eq_lcQspTilde
      (lcSignalStep_eq_adjoint hθ1 hθ2) (lcHalfDiffs (x :: xs))
    refine ⟨lcHalfDiffs (φ :: rest).reverse, -(x/2), φ/2, ?_,
      fun hp => ⟨by linear_combination -((1:ℝ)/2) * hheadAll hp, rfl⟩, rfl, ?_⟩
    · have hlen0 := lcHalfDiffs_length x xs
      rw [hx]
      have hrevlen : ((φ :: rest).reverse).length = (φ :: rest).length :=
        List.length_reverse
      have hsplit : (φ :: rest).length = xs.length + 1 := by
        rw [← hrevlen, hx]; simp
      omega
    · rw [← hprod, ← hmap, hx, htel, hQ]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

  · induction phis with
    | nil => exact Submonoid.one_mem _
    | cons φ rest ih =>
        have e1 : (φ :: rest).reverse = rest.reverse ++ [φ] := by simp
        have e2 : ((rest.reverse ++ [φ]).map (fun w => lcAxisRotation w θ)).prod
            = (rest.reverse.map (fun w => lcAxisRotation w θ)).prod *
              (([φ] : List ℝ).map (fun w => lcAxisRotation w θ)).prod := by
          rw [List.map_append, List.prod_append]
        have e3 : lcWord (φ :: rest) θ
            = ((rest.reverse ++ [φ]).map (fun w => lcAxisRotation w θ)).prod := by
          show ((φ :: rest).reverse.map (fun w => lcAxisRotation w θ)).foldl (· * ·) 1 =
            ((rest.reverse ++ [φ]).map (fun w => lcAxisRotation w θ)).prod
          rw [e1, List.prod_eq_foldl]
        have e4 : lcWord rest θ
            = (rest.reverse.map (fun w => lcAxisRotation w θ)).prod := by
          show (rest.reverse.map (fun w => lcAxisRotation w θ)).foldl (· * ·) 1 =
            (rest.reverse.map (fun w => lcAxisRotation w θ)).prod
          rw [List.prod_eq_foldl]
        have hsplit : lcWord (φ :: rest) θ = lcWord rest θ * lcAxisRotation φ θ := by
          rw [e3, e2, e4, List.map_singleton, List.prod_singleton]
        rw [hsplit]
        exact Submonoid.mul_mem _ ih (lcAxisRotation_unitary φ θ)

end Qatlib.Concepts.QspSimulation.WordModel
