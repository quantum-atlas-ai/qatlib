/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic

@[expose] public section

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
