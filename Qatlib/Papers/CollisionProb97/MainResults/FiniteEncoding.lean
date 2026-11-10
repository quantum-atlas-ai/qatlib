/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Mathlib.Tactic
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CollisionProb97.MainResults.Encoding

def codomainEquiv (Y : Type) [Fintype Y] [Nonempty Y] :
    Y ≃ ZMod (Fintype.card Y) := by
  haveI : NeZero (Fintype.card Y) := ⟨Fintype.card_ne_zero⟩
  exact (Fintype.equivFin Y).trans (ZMod.finEquiv (Fintype.card Y)).toEquiv

theorem encoded_collision_iff {X Y : Type} [Fintype Y] [Nonempty Y]
    (F : X → Y) (x z : X) :
    codomainEquiv Y (F x) = codomainEquiv Y (F z) ↔ F x = F z :=
  (codomainEquiv Y).injective.eq_iff

theorem encoded_table_mem_iff {X Y : Type} [Fintype Y] [Nonempty Y]
    [DecidableEq X] [DecidableEq Y] (F : X → Y) (K : Finset X) (x : X) :
    codomainEquiv Y (F x) ∈ K.image (fun z => codomainEquiv Y (F z)) ↔ F x ∈ K.image F := by
  classical
  simp only [Finset.mem_image, (codomainEquiv Y).injective.eq_iff]
end Qatlib.Papers.CollisionProb97.MainResults.Encoding
