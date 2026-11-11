/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Mathlib.Tactic

/-!
# Finite codomain encoding

This module chooses an equivalence `codomainEquiv` from a nonempty finite codomain to a cyclic
group of the same cardinality. This provides an additive oracle representation for the
algorithms in [BrassardHoyerTapp1998Collision].

The lemmas `encoded_collision_iff` and `encoded_table_mem_iff` show that this encoding preserves
equality of function values and membership in a table image.

## Main statements

* `codomainEquiv`: A chosen equivalence between a nonempty finite type `Y` and `ZMod
  (Fintype.card Y)`.
* `encoded_collision_iff`: Two encoded function values are equal exactly when the original
  values are equal.
* `encoded_table_mem_iff`: An encoded function value belongs to the encoded table image exactly
  when its original value belongs to `K.image F`.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CollisionProb97.MainResults.Encoding

/-- A chosen equivalence between a nonempty finite type `Y` and `ZMod (Fintype.card Y)`. -/
def codomainEquiv (Y : Type) [Fintype Y] [Nonempty Y] :
    Y ≃ ZMod (Fintype.card Y) := by
  haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  exact (Fintype.equivFin Y).trans (ZMod.finEquiv (Fintype.card Y)).toEquiv

/-- Two encoded function values are equal exactly when the original values are equal. -/
theorem encoded_collision_iff {X Y : Type} [Fintype Y] [Nonempty Y]
    (F : X → Y) (x z : X) :
    codomainEquiv Y (F x) = codomainEquiv Y (F z) ↔ F x = F z :=
  (codomainEquiv Y).injective.eq_iff

/-- An encoded function value belongs to the encoded table image exactly when its original value
belongs to `K.image F`. -/
theorem encoded_table_mem_iff {X Y : Type} [Fintype Y] [Nonempty Y]
    [DecidableEq X] [DecidableEq Y] (F : X → Y) (K : Finset X) (x : X) :
    codomainEquiv Y (F x) ∈ K.image (fun z => codomainEquiv Y (F z)) ↔ F x ∈ K.image F := by
  classical
  simp only [Finset.mem_image, (codomainEquiv Y).injective.eq_iff]
end Qatlib.Papers.CollisionProb97.MainResults.Encoding
