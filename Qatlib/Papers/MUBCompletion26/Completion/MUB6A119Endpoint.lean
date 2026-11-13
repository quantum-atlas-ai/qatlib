/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate

/-!
# Conditional obstruction from enclosed candidate rays

This module derives the candidate-ray completion obstruction of [Sun2026] from the finite
overlap certificate. For a normalized family satisfying `EnclosesOverlaps`, every choice of six
labels and unit phases has squared Gram defect strictly greater than 1/1200.

The theorem `no_orthonormal_candidates` applies this obstruction to any candidate predicate
covered, up to unit phase, by the certified family. All conclusions retain the normalization and
enclosure hypotheses.

## Main statements

* `enclosed_rays_gram_gap`: A uniform positive Gram-defect bound for six chosen rays.
* `no_orthonormal_candidates`: A covered candidate family cannot supply six orthonormal columns.

## References

* [Sun, 2026][Sun2026]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate

namespace Qatlib.Papers.MUBCompletion26.Completion

/-- Under `EnclosesOverlaps`, any distinct candidate labels outside `Edge` have inner-product
norm strictly greater than 1/120. -/
theorem enclosed_pair_gap (V : Fin 48 → Qatlib.Foundations.PureStateMath.QState (Fin 6))
    (hV : Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate.EnclosesOverlaps V) (a b : Fin 48) (hne : a ≠ b) (hno : ¬ Edge a b) :
    (1 : ℝ) / 120 < ‖Qatlib.Foundations.PureStateMath.Inner (V a) (V b)‖ := by
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact enclosed_ordered_pair_gap V hV a b hab hno
  · have h := enclosed_ordered_pair_gap V hV b a hba (fun he => hno (Or.symm he))
    have hs : ‖Qatlib.Foundations.PureStateMath.Inner (V a) (V b)‖ ^ 2 = ‖Qatlib.Foundations.PureStateMath.Inner (V b) (V a)‖ ^ 2 := by
      simpa only [Complex.normSq_eq_norm_sq] using
          Qatlib.Concepts.UnbiasedBases.ThreeBasis.normSq_inner_comm (V a) (V b)
    have he : ‖Qatlib.Foundations.PureStateMath.Inner (V a) (V b)‖ = ‖Qatlib.Foundations.PureStateMath.Inner (V b) (V a)‖ := by
      nlinarith [norm_nonneg (Qatlib.Foundations.PureStateMath.Inner (V a) (V b)), norm_nonneg (Qatlib.Foundations.PureStateMath.Inner (V b) (V a))]
    rw [he]
    exact h

/-- For a normalized family satisfying `EnclosesOverlaps`, any six selected rays with unit
phases have squared Gram defect greater than 1/1200 [Sun2026]. -/
theorem enclosed_rays_gram_gap (V : Fin 48 → Qatlib.Foundations.PureStateMath.QState (Fin 6))
    (hn : ∀ a, Qatlib.Foundations.PureStateMath.Normalized (V a)) (hV : Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate.EnclosesOverlaps V)
    (label : Fin 6 → Fin 48) (phase : Fin 6 → ℂ)
    (hp : ∀ j, Complex.normSq (phase j) = 1) :
    (1 : ℝ) / 1200 < gramDefectSquared (chosenRays V label phase) :=
  chosenRays_gram_gap graph graph_triangleFree V hn (enclosed_pair_gap V hV) label phase hp

/-- Six rays selected with unit phases from a normalized family satisfying `EnclosesOverlaps`
cannot form orthonormal columns. -/
theorem no_basis_from_enclosed_rays (V : Fin 48 → Qatlib.Foundations.PureStateMath.QState (Fin 6))
    (hn : ∀ a, Qatlib.Foundations.PureStateMath.Normalized (V a)) (hV : Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate.EnclosesOverlaps V)
    (label : Fin 6 → Fin 48) (phase : Fin 6 → ℂ)
    (hp : ∀ j, Complex.normSq (phase j) = 1) :
    ¬ Qatlib.Concepts.UnbiasedBases.ThreeBasis.OrthonormalColumns (chosenRays V label phase) := by
  intro h
  have hg := Qatlib.Papers.MUBCompletion26.Completion.enclosed_rays_gram_gap V hn hV label phase hp
  rw [gramDefectSquared_eq_zero _ h] at hg
  norm_num at hg

/-- If every candidate is a unit-phase multiple of a member of a normalized enclosed family, no
six candidate columns are orthonormal [Sun2026]. -/
theorem no_orthonormal_candidates
    (candidate : Qatlib.Foundations.PureStateMath.QState (Fin 6) → Prop) (V : Fin 48 → Qatlib.Foundations.PureStateMath.QState (Fin 6))
    (hn : ∀ a, Qatlib.Foundations.PureStateMath.Normalized (V a)) (hV : Qatlib.Papers.MUBCompletion26.Completion.MUB6A119Certificate.EnclosesOverlaps V)
    (cover : ∀ ψ, candidate ψ → ∃ a : Fin 48, ∃ c : ℂ,
      Complex.normSq c = 1 ∧ ψ = fun i => c * V a i)
    (B : Fin 6 → Qatlib.Foundations.PureStateMath.QState (Fin 6)) (hc : ∀ j, candidate (B j)) :
    ¬ Qatlib.Concepts.UnbiasedBases.ThreeBasis.OrthonormalColumns B := by
  classical
  choose label phase hp he using fun j => cover (B j) (hc j)
  have hB : B = chosenRays V label phase := by
    funext j
    exact he j
  rw [hB]
  exact no_basis_from_enclosed_rays V hn hV label phase hp

end Qatlib.Papers.MUBCompletion26.Completion
