/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AdversaryBounds.AdvDuality.GeneralAdversaryIteration

/-!
# Relabeling adversary matrices and disagreement filters

For [HoyerLeeSpalek2007], Theorem 9 and Corollary 10, simultaneous permutation
of the input rows and columns preserves the spectral norm. When an input
permutation transports a coordinate's equality relation, the corresponding
filtered matrix transforms by the same relabeling. This gives equal filter
norms on all coordinates for an invariant witness under index transitivity.

The source is the [fixed preprint](https://arxiv.org/abs/quant-ph/0611054v2), §5.
-/

@[expose] public section

open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.AdversaryBounds.AdvDuality (genAdvFilter norm_submatrix_equiv)

namespace Qatlib.Papers.NegWeights06.MainResults

/-- A permutation transporting the disagreement relation from coordinate `i` to `j`
preserves the spectral norm of that filter under simultaneous row and column relabeling. -/
theorem adversary_filter_norm_relabel {X K A : Type} [Fintype X] [DecidableEq X]
    [DecidableEq A] (input : X → K → A) (Γ : Matrix X X ℂ) (π : Equiv.Perm X) (i j : K)
    (hπ : ∀ x y, input x i = input y i ↔ input (π x) j = input (π y) j) :
    ‖genAdvFilter input (Γ.submatrix π π) i‖ = ‖genAdvFilter input Γ j‖ := by
  have hfilter : genAdvFilter input (Γ.submatrix π π) i =
      (genAdvFilter input Γ j).submatrix π π := by
    ext x y
    simp only [genAdvFilter, Matrix.submatrix_apply]
    by_cases h : input x i = input y i
    · simp [h, (hπ x y).mp h]
    · rw [ite_eq_left h, ite_eq_left ((hπ x y).not.mp h)]
  rw [hfilter, norm_submatrix_equiv]

/-- An index-transitive family of input relabelings makes all disagreement-filter norms of an
invariant adversary matrix equal. The common norm is chosen before the coordinate. -/
theorem adversary_filter_common_norm_of_index_transitive {X K A : Type}
    [Fintype X] [DecidableEq X] [DecidableEq A]
    (input : X → K → A) (Γ : Matrix X X ℂ) (G : Set (Equiv.Perm X))
    (hinput : Function.Injective input) (hΓ : Γ ≠ 0) (hdiag : ∀ x, Γ x x = 0)
    (hinvariant : ∀ π ∈ G, ∀ x y, Γ (π x) (π y) = Γ x y)
    (htransitive : ∀ i j, ∃ π ∈ G,
      ∀ x y, input x i = input y i ↔ input (π x) j = input (π y) j) :
    ∃ B : ℝ, 0 < B ∧ ∀ i, ‖genAdvFilter input Γ i‖ = B := by
  classical
  have hentry : ∃ x y, Γ x y ≠ 0 := by
    by_contra! h
    exact hΓ (Matrix.ext h)
  obtain ⟨x, y, hxy⟩ := hentry
  have hwords : input x ≠ input y := fun he => hxy (by rw [hinput he]; exact hdiag y)
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hwords
  have hfilter : genAdvFilter input Γ j ≠ 0 := by
    intro hz
    apply hxy
    have hzxy := congrArg (fun M : Matrix X X ℂ => M x y) hz
    change (if input x j ≠ input y j then Γ x y else 0) = 0 at hzxy
    rwa [ite_eq_left hj] at hzxy
  refine ⟨‖genAdvFilter input Γ j‖, norm_pos_iff.mpr hfilter, fun i => ?_⟩
  obtain ⟨π, hmem, hπ⟩ := htransitive i j
  have hrelabeled : Γ.submatrix π π = Γ := Matrix.ext (hinvariant π hmem)
  simpa only [hrelabeled] using adversary_filter_norm_relabel input Γ π i j hπ

end Qatlib.Papers.NegWeights06.MainResults
