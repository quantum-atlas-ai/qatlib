/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.FiniteEncoding
import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.Encoding
variable {X S Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]

def encoded (F : X → Y) : X → ZMod (Fintype.card Y) := fun x => codomainEquiv Y (F x)

omit [DecidableEq X] in

theorem encoded_fiber (F : X → Y) (x : X) :
    Finset.univ.filter (fun z => encoded F z = encoded F x) =
      Finset.univ.filter (fun z => F z = F x) := by
  ext z
  simp [encoded, (codomainEquiv Y).injective.eq_iff]

theorem encoded_regular (F : X → Y) (r : ℕ) (hF : RToOne F r) : RToOne (encoded F) r := by
  intro y hy
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
  rw [encoded_fiber]
  exact hF (F x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)

omit [DecidableEq X] in

theorem encoded_image_card (F : X → Y) :
    (Finset.univ.image (encoded F)).card = (Finset.univ.image F).card := by
  have he : Finset.univ.image (encoded F) = (Finset.univ.image F).image (codomainEquiv Y) := by
    rw [Finset.image_image]
    rfl
  rw [he, Finset.card_image_of_injective _ (codomainEquiv Y).injective]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in

theorem encoded_claw_iff (F : S → Y) (G : X → Y) (s : S) (x : X) :
    codomainEquiv Y (F s) = encoded G x ↔ F s = G x := (codomainEquiv Y).injective.eq_iff

end Qatlib.Papers.CollisionProb97.MainResults.Encoding
