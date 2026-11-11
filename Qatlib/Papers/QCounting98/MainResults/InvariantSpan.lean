/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma2RestrictedQuan
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma3RestrictedQuan

/-!
# Invariant spans for general-phase amplification

The good and bad parts sum to the original vector. `source_invariant_span_two` and
`source_invariant_span_four` show that the general-phase iterate preserves the spans generated
by these projections of the prepared state and an additional vector. The mathematical context is
[BrassardHoyerTapp1998Counting].

## Main statements

* `source_invariant_span_two`: Assuming `A * A.conjTranspose = 1`, the general-phase iterate
  preserves the span of the good and bad parts of the prepared column of `A`.
* `source_invariant_span_four`: Assuming `A * A.conjTranspose = 1`, the general-phase iterate
  preserves the span of the good and bad parts of an arbitrary vector together with those of the
  prepared column.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults

open Qatlib.Concepts.AEMeanReadout.RankOneSubspace
open Qatlib.Concepts.AEMeanReadout.RankOneSubspace.RankOneReflection
open scoped BigOperators

/-- The good and bad projections of a finite complex vector sum to that vector. -/
theorem source_goodPart_add_badPart {n : ℕ} (g : Fin (n + 1) → Bool)
    (v : Fin (n + 1) → ℂ) : goodPart g v + badPart g v = v := by
  funext i
  by_cases h : g i <;> simp [goodPart, badPart, h]

/-- Assuming `A * A.conjTranspose = 1`, the general-phase iterate preserves the span of the good
and bad parts of the prepared column of `A`. See [BrassardHoyerTapp1998Counting]. -/
theorem source_invariant_span_two {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ : ℂ) (hA : A * A.conjTranspose = 1) :
    ∀ w ∈ Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} :
          Set (Fin (n + 1) → ℂ)),
      (iterate A g φ ϕ).mulVec w ∈ Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} :
          Set (Fin (n + 1) → ℂ)) :=
  zoo_counting_two_dimensional_phase_action_span_invariant A g φ ϕ hA

/-- Assuming `A * A.conjTranspose = 1`, the general-phase iterate preserves the span of the good
and bad parts of an arbitrary vector together with those of the prepared column. See
[BrassardHoyerTapp1998Counting]. -/
theorem source_invariant_span_four {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (g : Fin (n + 1) → Bool)
    (φ ϕ : ℂ) (Υ : Fin (n + 1) → ℂ) (hA : A * A.conjTranspose = 1) :
    ∀ w ∈ Submodule.span ℂ
        ({goodPart g Υ, badPart g Υ, goodPart g (fun i => A i 0),
          badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)),
      (iterate A g φ ϕ).mulVec w ∈ Submodule.span ℂ
        ({goodPart g Υ, badPart g Υ, goodPart g (fun i => A i 0),
          badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)) := by
  intro w hw
  have hψ : (fun i => A i 0) =
      goodPart g (fun i => A i 0) + badPart g (fun i => A i 0) :=
    (source_goodPart_add_badPart g (fun i => A i 0)).symm
  obtain ⟨hg, hb⟩ := zoo_counting_good_bad_phase_action n A g φ ϕ Υ hA
  rw [hψ] at hg hb
  have hsub : Submodule.span ℂ
        ({goodPart g (fun i => A i 0), badPart g (fun i => A i 0)} :
          Set (Fin (n + 1) → ℂ)) ≤
      Submodule.span ℂ
        ({goodPart g Υ, badPart g Υ, goodPart g (fun i => A i 0),
          badPart g (fun i => A i 0)} : Set (Fin (n + 1) → ℂ)) := by
    apply Submodule.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact Submodule.subset_span (by simp)
    · exact Submodule.subset_span (by simp)
  have hinv := zoo_counting_two_dimensional_phase_action_span_invariant A g φ ϕ hA
  induction hw using Submodule.span_induction with
  | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [hg]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.add_mem _
            (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))))
      · rw [hb]
        exact Submodule.add_mem _
          (Submodule.neg_mem _ (Submodule.subset_span (by simp)))
          (Submodule.smul_mem _ _ (Submodule.add_mem _
            (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))))
      · exact hsub (hinv _ (Submodule.subset_span (by simp)))
      · exact hsub (hinv _ (Submodule.subset_span (by simp)))
  | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ r ih

end Qatlib.Papers.QCounting98.MainResults
