/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining.CoarseGrainingResults

@[expose] public section

/-!
# The coarse-graining of arXiv:2412.01732v1, Lemma 2.6, in dimension zero

`Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining.coarse_graining_exists`
records the existence statement of Lemma 2.6 as a predicate over the structure
`Qatlib.Papers.GibbsSampling25.MainResults.Model.CoarseGraining`, which stores
the cells, cores and shells together with the covering, disjointness, size and
overlap properties of Lemma B.2.

This file closes the lowest-dimensional instance `D = 0`. There the lattice is
`Λ_L = {-L,…,L}^0 = ℤ^0`, a single site, and the sup-metric is identically
zero, so the whole lattice can be taken as the only cell of the single level
`a = 0`, with the cell itself as core and shell. All eight properties then hold
vacuously or by definition, and the hypotheses `r ≤ k`, `2D(k+c) < ℓ`,
`ℓ ≤ 2L+1` are not needed.

Boundary: the general construction of Appendix B.2 (nested cubes of side `ℓ`
placed on shifted grids, shrunken cores and shells of width `k`) is not
formalised here, so Lemma 2.6 in positive dimension remains open; this file
only records that the statement is consistent and non-vacuous in the
zero-dimensional case.

## Main statements

* `coarse_graining_exists_zeroDim`: `Nonempty (CoarseGraining 0 L k c ℓ)`.

## References

* arXiv:2412.01732v1, Lemma 2.6 (p.6) and Lemma B.2 (p.31).
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining

open Qatlib.Papers.GibbsSampling25.MainResults.Model

/-- Lemma 2.6 of arXiv:2412.01732v1 in dimension `D = 0`: the lattice `Λ_L` has
a single site, so `Λ_L` itself is a suitable coarse-graining with one level,
its only cell being the whole lattice with itself as core and shell. The
hypotheses on `k`, `c`, `ℓ`, `L`, `r` are vacuous in this dimension. -/
theorem coarse_graining_exists_zeroDim (L k c ℓ : ℕ) :
    Nonempty (CoarseGraining 0 L k c ℓ) := by
  refine ⟨fun _ => {Finset.univ}, fun _ C => C, fun _ C => C,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a C _
    exact Finset.Subset.refl C
  · intro a C _
    exact Finset.Subset.refl C
  · intro x
    exact ⟨0, Finset.univ, by simp, Finset.mem_univ x⟩
  · intro x
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin (0 + 1)))
      (fun a : Fin (0 + 1) => ∃ C : Finset (Site 0 L),
        C ∈ ({Finset.univ} : Finset (Finset (Site 0 L))) ∧ x ∈ C)
    simpa using h
  · intro a C₁ h₁ C₂ h₂ hne
    simp only [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  · intro a C hC
    simp only [Finset.mem_singleton] at hC
    subst hC
    simp
  · intro a h
    omega
  · intro a C₁ h₁ C₂ h₂ hne
    simp only [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne
  · intro C _ x _ y _
    simp [latticeDist]
  · intro C₁ h₁ C₂ h₂ hne
    simp only [Finset.mem_singleton] at h₁ h₂
    exact absurd (h₁.trans h₂.symm) hne

end Qatlib.Papers.GibbsSampling25.MainResults.CoarseGraining
