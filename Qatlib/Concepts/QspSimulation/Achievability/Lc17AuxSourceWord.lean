/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.WordModel.Equation1WordBridgeLowc

/-!
# Converting normalized amplitudes to source words

This module converts repository quantum signal processing amplitudes to the source-word
convention associated with [LowChuang2017]. The construction `lcSourceAngles` records negative
twice the successive accumulated phase sums, so its half-differences recover the original phase
list and its reversed word telescopes to a product involving `lcQspTilde`.

The endpoint identity `lcRepoAmp_one` makes normalization at `x = 1` explicit. This condition is
sufficient for the conversion in `lcSourceWord_of_normalized` and necessary for any matching
source amplitude on `[0, 2 * Real.pi]`; a concrete choice of endpoint rotations gives an
obstruction to unrestricted conversion.

## Main statements

* `lcSourceAngles_diffs` recovers the input phases from the constructed source angles.
* `lcSourceAngles_word` establishes the matrix word identity on the source angle interval.
* `lcSourceWord_of_normalized` constructs a source phase list when the repository amplitude
  equals one at the endpoint.
* `lcRepoAmp_source_endpoint_required` and `lcRepoAmp_unrestricted_source_obstruction` establish
  the endpoint requirement and a counterexample without it.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

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

/-- The source angle list formed from negative twice the successive accumulated phases,
beginning with `-2 * γ` and including one more angle than the input list. -/
noncomputable def lcSourceAngles (γ : ℝ) : List ℝ → List ℝ
  | [] => [-2 * γ]
  | q :: qs => (-2 * γ) :: lcSourceAngles (γ + q) qs

/-- The source angle list has length `qs.length + 1`. -/
theorem lcSourceAngles_length (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).length = qs.length + 1 := by
  induction qs generalizing γ with
  | nil => rfl
  | cons q qs ih => simp [lcSourceAngles, ih]

/-- The source angle list is nonempty for every starting angle and input phase list. -/
theorem lcSourceAngles_ne_nil (qs : List ℝ) (γ : ℝ) :
    lcSourceAngles γ qs ≠ [] := by
  cases qs <;> simp [lcSourceAngles]

/-- The first source angle is `-2 * γ`. -/
theorem lcSourceAngles_head (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).head (lcSourceAngles_ne_nil qs γ) = -2 * γ := by
  cases qs <;> rfl

/-- The last source angle is `-2 * (γ + qs.sum)`. -/
theorem lcSourceAngles_last (qs : List ℝ) (γ : ℝ) :
    (lcSourceAngles γ qs).getLast (lcSourceAngles_ne_nil qs γ) = -2 * (γ + qs.sum) := by
  induction qs generalizing γ with
  | nil => simp [lcSourceAngles]
  | cons q qs ih =>
    simp only [lcSourceAngles]
    rw [List.getLast_cons (lcSourceAngles_ne_nil qs (γ + q)), ih]
    simp only [List.sum_cons]
    ring

/-- Taking half-differences of the source angle list recovers the input phase list `qs`. -/
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

/-- On `[0, 2 * Real.pi]`, the word of the reversed source angle list equals `lcQspTilde` at
`cos (θ / 2)` with the stated endpoint rotations and an additional adjoint signal matrix. -/
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

/-- The signal matrix at `1` is the identity matrix. -/
theorem lcSignalMatrix_one : SignalMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [SignalMatrix, Matrix.one_apply]

/-- The phase rotation at angle zero is the identity matrix. -/
theorem lcPhaseRotation_zero : PhaseRotation 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [phaseRotation_apply, Matrix.one_apply]

/-- At signal value `1`, `lcQspTilde` is the phase rotation by the sum of its phase list. -/
theorem lcQspTilde_one (qs : List ℝ) : lcQspTilde qs 1 = PhaseRotation qs.sum := by
  have ht : lcWordTilde (1 : Matrix (Fin 2) (Fin 2) ℂ) qs = PhaseRotation qs.sum := by
    induction qs with
    | nil => simp [lcWordTilde, lcPhaseRotation_zero]
    | cons q qs ih =>
      rw [lcWordTilde_cons, one_mul, ih, lcPhaseRotation_mul, List.sum_cons]
  rw [← lcWordTilde_eq_lcQspTilde (S := 1) (x := 1)
    (by rw [lcSignalMatrix_one, Matrix.conjTranspose_one]) qs]
  exact ht

/-- The upper-left entry of a phase rotation conjugated by `lcHad` is the cosine of its rotation
angle. -/
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

/-- The repository amplitude at `1` is the cosine of the sum of its two endpoint angles and all
internal phases. -/
theorem lcRepoAmp_one (γ₀ γ₁ : ℝ) (qs : List ℝ) :
    lcRepoAmp γ₀ γ₁ qs 1 = (Real.cos (γ₀ + qs.sum + γ₁) : ℂ) := by
  unfold lcRepoAmp
  rw [lcSignalMatrix_one, Matrix.conjTranspose_one, Matrix.mul_one, lcQspTilde_one]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (PhaseRotation γ₀), lcPhaseRotation_mul,
      ← Matrix.mul_assoc (PhaseRotation (γ₀ + qs.sum)), lcPhaseRotation_mul]
  simpa only [Matrix.mul_assoc] using! lcHad_phase_corner (γ₀ + qs.sum + γ₁)

/-- If the repository amplitude at `1` equals one, the phase rotation by the total endpoint and
internal phase sum is the identity. -/
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

/-- A repository amplitude equal to one at `1` is realized on the source angle interval by
`lcPlusAmp` with a phase list of length `qs.length + 1`. -/
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

/-- Any source amplitude agreeing with the repository amplitude throughout `[0, 2 * Real.pi]`
forces the repository amplitude at `1` to equal one. -/
theorem lcRepoAmp_source_endpoint_required (γ₀ γ₁ : ℝ) (qs phis : List ℝ)
    (h : ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      lcPlusAmp phis θ = lcRepoAmp γ₀ γ₁ qs (Real.cos (θ / 2))) :
    lcRepoAmp γ₀ γ₁ qs 1 = 1 := by
  have hh := h 0 ⟨le_refl _, by positivity⟩
  simpa only [zero_div, Real.cos_zero, lcPlusAmp_zero_angle] using! hh.symm

/-- The repository amplitude with endpoint angles `Real.pi / 2` and zero and no internal phases
cannot agree with any source amplitude throughout `[0, 2 * Real.pi]`. -/
theorem lcRepoAmp_unrestricted_source_obstruction :
    ¬ ∃ phis : List ℝ, ∀ θ ∈ Set.Icc 0 (2 * Real.pi),
      lcPlusAmp phis θ = lcRepoAmp (Real.pi / 2) 0 [] (Real.cos (θ / 2)) := by
  rintro ⟨phis, h⟩
  have hh := lcRepoAmp_source_endpoint_required (Real.pi / 2) 0 [] phis h
  rw [lcRepoAmp_one] at hh
  norm_num [Real.cos_pi_div_two] at hh

end Qatlib.Concepts.QspSimulation.Achievability
