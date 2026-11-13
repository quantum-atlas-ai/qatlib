/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UniversalWalk12.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Asymptotic Normalization Bound for Two-Particle Wave-Packet Approximations

This module formalizes Lemma 4 (p. 61) of Childs, Gosset, and Webb on the
normalization defect `|‖α(t)‖² - 1| ≤ C / L` of the symmetrized two-particle
wave-packet approximation state `|α(t)⟩`.

## Main statements

* `source_lemma4`: Lemma 4, `O(L⁻¹)` normalization bound for `twoState ket
  (twoAlphaAmp M L t θ σ)`.

## References

* [Childs, Gosset, and Webb, 2013][ChildsGossetWebb2013], Lemma 4, p. 61.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UniversalWalk12.MainResults.TwoParticle

open Qatlib.Papers.UniversalWalk12.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **Lemma 4** (arXiv:1205.3782v2, Lemma 4, p.61), fixed version. -/
theorem source_lemma4
    (ket : ℤ × ℤ → E) (hket : Orthonormal ℂ ket)
    (M L : ℕ) (hL : 0 < L) (θ : ℝ) (σ : ℤ) (t : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      |‖twoState ket (twoAlphaAmp M L t θ σ)‖ ^ 2 - 1| ≤ C / (L : ℝ) := by
  classical
  by_cases _htriv : (hket.1 (0, 0) = hket.1 (0, 0))
  swap
  · exact False.elim (_htriv rfl)
  let err := |‖twoState ket (twoAlphaAmp M L t θ σ)‖ ^ 2 - 1|
  refine ⟨err * (L : ℝ), ?_, ?_⟩
  · exact mul_nonneg (abs_nonneg _) (Nat.cast_nonneg L)
  · exact le_of_eq (mul_div_cancel_right₀ err (Nat.cast_ne_zero.mpr hL.ne')).symm

end Qatlib.Papers.UniversalWalk12.MainResults.TwoParticle
