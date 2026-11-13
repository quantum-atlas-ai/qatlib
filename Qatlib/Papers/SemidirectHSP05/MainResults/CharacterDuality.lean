/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.Ring.Defs
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Defs
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic

/-!
# Dual maps for finite sums of automorphism iterates

`phiSum` is the additive endomorphism obtained by summing the first `b` iterates of an additive
automorphism. Given an identification of a finite abelian group with its complex additive
characters, `lemma7_exists_dual_map` constructs a map representing precomposition of characters
by this endomorphism. See [BaconChildsVanDam2005] for the mathematical setting.

## Main statements

* `lemma7_exists_dual_map`: constructs a map satisfying the character-pairing identity for
  `phiSum`.

## References

* [Bacon et al., 2005][BaconChildsVanDam2005]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.CharacterDuality

variable {A : Type*} [AddCommGroup A]

/-- The additive endomorphism obtained by summing the iterates of `φ` indexed by the natural
numbers strictly below `b`. -/
def phiSum (φ : AddAut A) (b : ℕ) : A →+ A :=
  ∑ i ∈ Finset.range b, (i • φ).toAddMonoidHom

/-- Given an equivalence between a finite abelian group and its complex additive characters,
there exists a map `Φhat` satisfying `e x (phiSum φ b d) = e (Φhat x) d` for every `d` and
`x`. See [Bacon et al., 2005, Lemma 7][BaconChildsVanDam2005]. -/
theorem lemma7_exists_dual_map [Fintype A]
    (e : A ≃ AddChar A ℂ) (φ : AddAut A) (b : ℕ) :
    ∃ Φhat : A → A, ∀ d x : A,
      e x (phiSum φ b d) = e (Φhat x) d := by
  refine ⟨fun x => e.symm ((e x).compAddMonoidHom (phiSum φ b)), ?_⟩
  intro d x
  simp [AddChar.compAddMonoidHom_apply]

end Qatlib.Papers.SemidirectHSP05.MainResults.CharacterDuality
