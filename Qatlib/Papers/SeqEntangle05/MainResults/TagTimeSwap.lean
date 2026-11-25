/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SeqEntangle05.MainResults.StandardMap

@[expose] public section

/-!
# Action of the standard tag and time-bin swap

The permutation matrix acts by reindexing amplitudes. On the initially
empty time-bin register this gives both register transitions of Eq. (6)
for any ancillary amplitude vector.
-/

set_option autoImplicit false

namespace Qatlib.Papers.SeqEntangle05.MainResults

open Qatlib.Papers.SeqEntangle05.MainResults.StandardMap
open scoped BigOperators Matrix

/-- The standard map evaluates each output amplitude at the swapped input label. -/
theorem stdMap_action (D : ℕ) (ψ : Fin D × Fin 2 × Fin 2 → ℂ) :
    stdMap D *ᵥ ψ = fun x => ψ (swapTB D x) := by
  ext x
  change (∑ y, stdMap D x y * ψ y) = ψ (swapTB D x)
  rw [Finset.sum_eq_single (swapTB D x)]
  · simp [stdMap, swapTB_invol]
  · intro y _ hne
    have h : x ≠ swapTB D y := by
      intro hxy
      apply hne
      rw [hxy, swapTB_invol]
    simp [stdMap, h]
  · simp

/-- Each computational basis vector is sent to the basis vector with exchanged binary labels. -/
theorem stdMap_single (D : ℕ) (a : Fin D) (t b : Fin 2) :
    stdMap D *ᵥ Pi.single (a, t, b) (1 : ℂ) = Pi.single (a, b, t) (1 : ℂ) := by
  rw [Matrix.mulVec_single_one]
  ext x
  by_cases h : x = (a, b, t) <;> simp [Matrix.col, stdMap, swapTB, h]

/-- An initially empty time bin receives the tag while the ancillary vector remains unchanged. -/
theorem source_eq6 (D : ℕ) (φ : Fin D → ℂ) (tag : Fin 2) :
    stdMap D *ᵥ (fun x => if x.2.1 = tag ∧ x.2.2 = 0 then φ x.1 else 0) =
      fun x => if x.2.1 = 0 ∧ x.2.2 = tag then φ x.1 else 0 := by
  rw [stdMap_action]
  funext x
  simp only [swapTB, and_comm]
  by_cases h : x.2.2 = tag ∧ x.2.1 = 0 <;> simp [h]

end Qatlib.Papers.SeqEntangle05.MainResults
