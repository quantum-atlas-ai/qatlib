/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OpCalculus.PerturbTwo.ScalarTwoPerturbation

set_option backward.isDefEq.respectTransparency false

/-! The finite-dimensional specialization of Lemma 1. The auxiliary dilation
space may be infinite-dimensional; no general-Hilbert ultrapower reduction is
claimed by this consumer. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CrouzeixLS26.Perturbation
open Qatlib.Foundations.OpCalculus.PerturbTwo

/-- Lemma 1 for finite-dimensional complex source space, retaining all powers,
uniform defect bounds, and commutation with the actual operator. -/
theorem finite_complex_perturbation_bound
    {H K : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [FiniteDimensional ℂ H]
    (T : H →L[ℂ] H) (Q : K →L[ℂ] K) (V : H →L[ℂ] K)
    (hQ : ‖Q‖ ≤ 1) (hV : ∀ y, ‖V y‖ = ‖y‖)
    (C : ℝ) (hE : ∀ n, ‖complexPerturbation T Q V n‖ ≤ C)
    (hcomm : ∀ n, Commute (complexPerturbation T Q V n) T) : ‖T‖ ≤ 2 := by
  exact complex_perturbation_norm_le_two T Q V hQ hV C hE hcomm

end Qatlib.Papers.CrouzeixLS26.Perturbation
