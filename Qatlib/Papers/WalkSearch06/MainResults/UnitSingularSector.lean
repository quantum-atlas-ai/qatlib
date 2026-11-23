/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# WalkSearch06 — the unit singular-value sectors of the Szegedy walk

Source: [MagniezNayakRolandSantha2011], Theorem 4, parts 2 and 4, p. 7 of
[arXiv:quant-ph/0608026v4](https://arxiv.org/abs/quant-ph/0608026v4).

Theorem 4 describes the spectrum of the walk `W(P) = ref(B) * ref(A)` on the sum
`A + B` of the two Szegedy subspaces. Part 2 concerns the singular value `1` of the
discriminant matrix: on the intersection `A ⊓ B` the walk acts as the identity. Part 4
concerns the orthogonal complement of the sum: on `Aᗮ ⊓ Bᗮ` the walk also acts as the
identity.

This module proves those two identity actions for arbitrary subspaces of a complex
inner product space with orthogonal projections. Together with
`Qatlib.Papers.WalkSearch06.MainResults.szegedy_zero_singular_sector`, it gives
the pointwise reflection action on the four endpoint intersections. The general
rotation planes, the singular-vector spanning statements, and spectral exhaustiveness
remain open here.

## Main statements

* `szegedy_unit_singular_sector`: `ref(B) * ref(A)` acts as `Id` on `A ⊓ B` and on
  `Aᗮ ⊓ Bᗮ`.
-/

namespace Qatlib.Papers.WalkSearch06.MainResults

/-- The identity actions from [MagniezNayakRolandSantha2011], Theorem 4, parts 2 and 4:
the product of reflections `ref(B) * ref(A)` acts as the identity on `A ⊓ B` and
`Aᗮ ⊓ Bᗮ`.

On `A ⊓ B` both reflections fix `v`, so their product does. On `Aᗮ ⊓ Bᗮ` both
reflections negate `v`, and the two signs cancel. The hypotheses only require that both
subspaces have orthogonal projections; no finite-dimensionality, completeness of the
ambient space, or Markov chain structure is used. -/
theorem szegedy_unit_singular_sector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    (∀ v ∈ A ⊓ B, B.reflection (A.reflection v) = v) ∧
      (∀ v ∈ Aᗮ ⊓ Bᗮ, B.reflection (A.reflection v) = v) := by
  constructor
  · rintro v ⟨hvA, hvB⟩
    rw [Submodule.reflection_mem_subspace_eq_self hvA,
      Submodule.reflection_mem_subspace_eq_self hvB]
  · rintro v ⟨hvA, hvB⟩
    rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvA, map_neg,
      Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvB, neg_neg]

end Qatlib.Papers.WalkSearch06.MainResults
