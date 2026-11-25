/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

@[expose] public section

/-!
# WalkSearch06 — the zero singular-value sector of the Szegedy walk

Source: F. Magniez, A. Nayak, J. Roland, and M. Santha, *Search via Quantum Walk*,
arXiv:quant-ph/0608026v4, Theorem 4, part 3, printed p. 7.

Theorem 4 describes the spectrum of the walk `W(P) = ref(B) * ref(A)` on the sum
`A + B` of the two Szegedy subspaces. Part 3 concerns the singular value `0` of the
discriminant matrix: on the sectors `A ⊓ Bᗮ` and `Aᗮ ⊓ B` the walk acts as `-Id`.

This module proves exactly that sector statement, for arbitrary subspaces of a complex
inner product space with orthogonal projections. On `A ⊓ Bᗮ` the reflection in `A` fixes
the vector and the reflection in `B` negates it; on `Aᗮ ⊓ B` the two roles are exchanged.
No spectral decomposition is used. The remaining parts of Theorem 4 — the singular-value
`1` sector `A ⊓ B`, the nonzero singular values in `(0,1)`, and `Aᗮ ⊓ Bᗮ` — are not
covered here, and the matrix-level bridge from the discriminant of a Markov chain to
these subspaces is not constructed.

## Main statements

* `szegedy_zero_singular_sector`: `ref(B) * ref(A)` acts as `-Id` on `A ⊓ Bᗮ` and on
  `Aᗮ ⊓ B`.
-/

namespace Qatlib.Papers.WalkSearch06.MainResults

/-- Szegedy walk, Theorem 4 part 3: on `A ⊓ Bᗮ` and on `Aᗮ ⊓ B` the product of the two
frame reflections `ref(B) * ref(A)` acts as pointwise negation.

On `A ⊓ Bᗮ` the reflection in `A` fixes `v` because `v ∈ A`, and then the reflection in
`B` negates `v` because `v ∈ Bᗮ`. On `Aᗮ ⊓ B` the reflection in `A` negates `v` and the
reflection in `B` fixes the result. The hypotheses only require that both subspaces have
orthogonal projections; no finite-dimensionality, completeness of the ambient space, or
Markov chain structure is used. -/
theorem szegedy_zero_singular_sector {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A B : Submodule ℂ H) [A.HasOrthogonalProjection] [B.HasOrthogonalProjection] :
    (∀ v ∈ A ⊓ Bᗮ, B.reflection (A.reflection v) = -v) ∧
      (∀ v ∈ Aᗮ ⊓ B, B.reflection (A.reflection v) = -v) := by
  constructor
  · rintro v ⟨hvA, hvB⟩
    rw [Submodule.reflection_mem_subspace_eq_self hvA,
      Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvB]
  · rintro v ⟨hvA, hvB⟩
    rw [Submodule.reflection_mem_subspace_orthogonalComplement_eq_neg hvA, map_neg,
      Submodule.reflection_mem_subspace_eq_self hvB]

end Qatlib.Papers.WalkSearch06.MainResults
