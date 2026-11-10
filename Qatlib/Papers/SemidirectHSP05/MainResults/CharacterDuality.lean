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
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SemidirectHSP05.MainResults.CharacterDuality

variable {A : Type*} [AddCommGroup A]

def phiSum (φ : AddAut A) (b : ℕ) : A →+ A :=
  ∑ i ∈ Finset.range b, (i • φ).toAddMonoidHom

theorem lemma7_exists_dual_map [Fintype A]
    (e : A ≃ AddChar A ℂ) (φ : AddAut A) (b : ℕ) :
    ∃ Φhat : A → A, ∀ d x : A,
      e x (phiSum φ b d) = e (Φhat x) d := by
  refine ⟨fun x => e.symm ((e x).compAddMonoidHom (phiSum φ b)), ?_⟩
  intro d x
  simp [AddChar.compAddMonoidHom_apply]

end Qatlib.Papers.SemidirectHSP05.MainResults.CharacterDuality
