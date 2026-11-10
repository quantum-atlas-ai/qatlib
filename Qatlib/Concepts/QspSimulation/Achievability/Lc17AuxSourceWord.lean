/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.SignalDefs
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix

noncomputable def lcSourceAngles (γ : ℝ) : List ℝ → List ℝ
  | [] => [-2 * γ]
  | q :: qs => (-2 * γ) :: lcSourceAngles (γ + q) qs

theorem lcSourceAngles_length (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).length = qs.length + 1 := by
  induction qs generalizing γ with
  | nil => rfl
  | cons q qs ih => simp [lcSourceAngles, ih]

theorem lcSourceAngles_ne_nil (qs : List ℝ) (γ : ℝ) :
    lcSourceAngles γ qs ≠ [] := by
  cases qs <;> simp [lcSourceAngles]

theorem lcSourceAngles_head (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).head (lcSourceAngles_ne_nil qs γ) = -2 * γ := by
  cases qs <;> rfl

theorem lcSourceAngles_last (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).getLast (lcSourceAngles_ne_nil qs γ) = -2 * (γ + qs.sum) := by
  induction qs generalizing γ with
  | nil => simp [lcSourceAngles]
  | cons q qs ih =>
    simp only [lcSourceAngles]
    rw [List.getLast_cons (lcSourceAngles_ne_nil qs (γ + q)), ih]
    simp only [List.sum_cons]
    ring

theorem lcSourceAngles_diffs (qs : List ℝ) (γ : ℝ) :
    lcHalfDiffs (lcSourceAngles γ qs) = qs := by
  induction qs generalizing γ with
  | nil => rfl
  | cons q qs ih =>
    have hd : lcHalfDiffs ((-2 * γ) :: lcSourceAngles (γ + q) qs) =
        q :: lcHalfDiffs (lcSourceAngles (γ + q) qs) := by
      cases qs <;> simp only [lcSourceAngles, lcHalfDiffs]
      all_goals congr 1; ring
    rw [lcSourceAngles, hd, ih]

theorem lcSourceAngles_word (qs : List ℝ) (γ θ : ℝ)
    (hθ : 0 ≤ θ) (hθπ : θ ≤ 2 * Real.pi) :
    lcWord (lcSourceAngles γ qs).reverse θ =
      PhaseRotation γ * lcQspTilde qs (Real.cos (θ / 2)) *
        (SignalMatrix (Real.cos (θ / 2)))ᴴ * PhaseRotation (-(γ + qs.sum)) := by
  have ht := lcFold_telescope (lcSignalStep θ)
  obtain ⟨a, rest, ha⟩ := List.exists_cons_of_ne_nil (lcSourceAngles_ne_nil qs γ)
  have hhead : a = -2 * γ := by
    have hh := lcSourceAngles_head qs γ
    simpa only [ha, List.head_cons] using! hh
  have hlast : (a :: rest).getLast (List.cons_ne_nil a rest) = -2 * (γ + qs.sum) := by
    simpa only [ha] using! lcSourceAngles_last qs γ
  have htel := ht rest a (-2 * (γ + qs.sum)) hlast
  have hd : lcHalfDiffs (a :: rest) = qs := by
    rw [← ha, lcSourceAngles_diffs]
  rw [hd, lcWordTilde_eq_lcQspTilde (lcSignalStep_eq_adjoint hθ hθπ)] at htel
  unfold lcWord
  rw [List.reverse_reverse, ← List.prod_eq_foldl]
  have hfac : (lcSourceAngles γ qs).map (fun φ => lcAxisRotation φ θ) =
      (lcSourceAngles γ qs).map (fun φ =>
        PhaseRotation (-(φ / 2)) * (lcSignalStep θ * PhaseRotation (φ / 2))) := by
    apply List.map_congr_left
    intro φ _
    exact lcAxisRotation_factor φ θ
  rw [hfac, ha, htel, hhead,
    show -(-2 * γ / 2) = γ by ring,
    show -2 * (γ + qs.sum) / 2 = -(γ + qs.sum) by ring,
    lcSignalStep_eq_adjoint hθ hθπ]
  simp only [Matrix.mul_assoc]

theorem lcSignalMatrix_one : SignalMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [SignalMatrix, Matrix.one_apply]

theorem lcPhaseRotation_zero : PhaseRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseRotation_apply, Matrix.one_apply]

theorem lcQspTilde_one (qs : List ℝ) : lcQspTilde qs 1 = PhaseRotation qs.sum := by
  have ht : lcWordTilde (1 : Matrix (Fin 2) (Fin 2) ℂ) qs = PhaseRotation qs.sum := by
    induction qs with
    | nil => simp [lcWordTilde, lcPhaseRotation_zero]
    | cons q qs ih =>
      rw [lcWordTilde_cons, one_mul, ih, lcPhaseRotation_mul, List.sum_cons]
  rw [← lcWordTilde_eq_lcQspTilde (S := 1) (x := 1)
    (by rw [lcSignalMatrix_one, Matrix.conjTranspose_one]) qs]
  exact ht

theorem lcHad_phase_corner (γ : ℝ) :
    (lcHad * PhaseRotation γ * lcHad) 0 0 = (Real.cos γ : ℂ) := by
  have hs : (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) = 1 / 2 := by
    rw [← Complex.ofReal_mul, ← _root_.mul_inv_rev, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [Matrix.mul_apply, Fin.sum_univ_two, phaseRotation_apply]
  norm_num [lcHad]
  rw [show -((γ : ℂ) * Complex.I) = (-(γ : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast at hs
  linear_combination (2 * Complex.cos (γ : ℂ)) * hs

theorem lcRepoAmp_one (γ₀ γ₁ : ℝ) (qs : List ℝ) :
    lcRepoAmp γ₀ γ₁ qs 1 = (Real.cos (γ₀ + qs.sum + γ₁) : ℂ) := by
  unfold lcRepoAmp
  rw [lcSignalMatrix_one, Matrix.conjTranspose_one, Matrix.mul_one, lcQspTilde_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (PhaseRotation γ₀), lcPhaseRotation_mul,
      ← Matrix.mul_assoc (PhaseRotation (γ₀ + qs.sum)), lcPhaseRotation_mul]
  simpa only [Matrix.mul_assoc] using! lcHad_phase_corner (γ₀ + qs.sum + γ₁)

theorem lcRepoAmp_one_phase (γ₀ γ₁ : ℝ) (qs : List ℝ)
    (h : lcRepoAmp γ₀ γ₁ qs 1 = 1) :
    PhaseRotation (γ₀ + qs.sum + γ₁) = 1 := by
  rw [lcRepoAmp_one] at h
  have hc : Real.cos (γ₀ + qs.sum + γ₁) = 1 := Complex.ofReal_eq_one.mp h
  have hs : Real.sin (γ₀ + qs.sum + γ₁) = 0 := by
    have hsq := Real.sin_sq_add_cos_sq (γ₀ + qs.sum + γ₁)
    rw [hc] at hsq
    nlinarith [sq_nonneg (Real.sin (γ₀ + qs.sum + γ₁))]
  have hp : Complex.exp (((γ₀ + qs.sum + γ₁ : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, hc, hs]
    simp
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [phaseRotation_apply, Matrix.one_apply]
  all_goals norm_num only [Fin.reduceFinMk, ite_true, ite_false]
  · exact hp
  · rfl
  · rfl
  · rw [neg_mul, Complex.exp_neg, hp, inv_one]
    simp

theorem lcSourceWord_of_normalized (γ₀ γ₁ : ℝ) (qs : List ℝ)
    (h : lcRepoAmp γ₀ γ₁ qs 1 = 1) :
    ∃ phis : List ℝ, phis.length = qs.length + 1 ∧
      ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
        lcPlusAmp phis θ = lcRepoAmp γ₀ γ₁ qs (Real.cos (θ / 2)) := by
  have hp := lcRepoAmp_one_phase γ₀ γ₁ qs h
  have he : PhaseRotation γ₁ = PhaseRotation (-(γ₀ + qs.sum)) := by
    have hh := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ =>
      PhaseRotation (-(γ₀ + qs.sum)) * M) hp
    change PhaseRotation (-(γ₀ + qs.sum)) * PhaseRotation (γ₀ + qs.sum + γ₁) =
      PhaseRotation (-(γ₀ + qs.sum)) * 1 at hh
    rw [lcPhaseRotation_mul, Matrix.mul_one] at hh
    simpa only [show -(γ₀ + qs.sum) + (γ₀ + qs.sum + γ₁) = γ₁ by ring] using! hh
  refine ⟨(lcSourceAngles γ₀ qs).reverse, ?_, ?_⟩
  · rw [List.length_reverse, lcSourceAngles_length]
  · intro θ hθ
    unfold lcPlusAmp lcRepoAmp
    rw [lcSourceAngles_word qs γ₀ θ hθ.1 hθ.2, he]
    simp only [Matrix.mul_assoc]

theorem lcRepoAmp_source_endpoint_required (γ₀ γ₁ : ℝ) (qs phis : List ℝ)
    (h : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      lcPlusAmp phis θ = lcRepoAmp γ₀ γ₁ qs (Real.cos (θ / 2))) :
    lcRepoAmp γ₀ γ₁ qs 1 = 1 := by
  have hh := h 0 ⟨le_refl _, by positivity⟩
  simpa only [zero_div, Real.cos_zero, lcPlusAmp_zero_angle] using! hh.symm

theorem lcRepoAmp_unrestricted_source_obstruction :
    ¬ ∃ phis : List ℝ, ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      lcPlusAmp phis θ = lcRepoAmp (Real.pi / 2) 0 [] (Real.cos (θ / 2)) := by
  rintro ⟨phis, h⟩
  have hh := lcRepoAmp_source_endpoint_required (Real.pi / 2) 0 [] phis h
  rw [lcRepoAmp_one] at hh
  norm_num [Real.cos_pi_div_two] at hh

end Qatlib.Concepts.QspSimulation.Achievability
