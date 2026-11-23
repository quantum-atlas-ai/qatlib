/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphModel

/-!
# Fixed-sector connectedness and kernel predicates

Connectedness includes nonemptiness of the sector; the real kernel vector
is nonzero on that sector and satisfies exactly the rows in its restriction.
The vertex set and weights are those of the public graph model.
-/

@[expose] public section

namespace Qatlib.Papers.KhovanovHom25.MainResults

open Qatlib.Papers.KhovanovHom25.MainResults

/-- Connectedness on the actual nonempty fixed-particle vertex sector. -/
def IsConnectedSector {ℓ : ℕ} (k p : ℕ) (m : Fin p → Fin ℓ × Fin ℓ) : Prop :=
  (vertexSet ℓ k).Nonempty ∧
    ∀ v ∈ vertexSet ℓ k, ∀ v' ∈ vertexSet ℓ k,
      Relation.ReflTransGen (Adj p m) v v'

/-- A genuine nonzero vector in the specified particle sector, annihilated by its rows. -/
def HasSectorKernel {ℓ : ℕ} (k p t : ℕ) (m : Fin p → Fin ℓ × Fin ℓ)
    (d : Fin t → Fin ℓ) : Prop :=
  ∃ x : Vertex ℓ → ℝ,
    (∃ v ∈ vertexSet ℓ k, x v ≠ 0) ∧
      ∀ v ∈ vertexSet ℓ k,
        ∑ v' ∈ vertexSet ℓ k, signlessMatrix p t m d v v' * x v' = 0

end Qatlib.Papers.KhovanovHom25.MainResults
