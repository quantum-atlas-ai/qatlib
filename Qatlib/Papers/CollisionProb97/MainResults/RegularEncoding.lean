/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.FiniteEncoding
import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting

/-!
# Encoding regular functions in cyclic groups

This module defines `encoded` by composing a finite-valued function with `codomainEquiv`. The
encoding preserves fibers, regularity, image cardinality, and matching values needed for the
collision and claw algorithms of [BrassardHoyerTapp1998Collision].

## Main statements

* `encoded_regular`: Encoding preserves the property of being `r`-to-one.
* `encoded_image_card`: The encoded function has the same image cardinality as the original
  function.
* `encoded_claw_iff`: Equality between encoded `F`- and `G`-values is equivalent to equality
  between their original values [BrassardHoyerTapp1998Collision].

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Collision]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped Classical
namespace Qatlib.Papers.CollisionProb97.MainResults.Encoding
variable {X S Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq Y]

/-- The function obtained by encoding the finite codomain of `F` in a cyclic group of the same
cardinality. -/
def encoded (F : X → Y) : X → ZMod (Fintype.card Y) := fun x => codomainEquiv Y (F x)

omit [DecidableEq X] in

/-- Encoding preserves the fiber containing any given input exactly. -/
theorem encoded_fiber (F : X → Y) (x : X) :
    Finset.univ.filter (fun z => encoded F z = encoded F x) =
      Finset.univ.filter (fun z => F z = F x) := by
  ext z
  simp [encoded, (codomainEquiv Y).injective.eq_iff]

/-- Encoding preserves the property of being `r`-to-one. -/
theorem encoded_regular (F : X → Y) (r : ℕ) (hF : RToOne F r) : RToOne (encoded F) r := by
  intro y hy
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hy
  rw [encoded_fiber]
  exact hF (F x) (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)

omit [DecidableEq X] in

/-- The encoded function has the same image cardinality as the original function. -/
theorem encoded_image_card (F : X → Y) :
    (Finset.univ.image (encoded F)).card = (Finset.univ.image F).card := by
  have he : Finset.univ.image (encoded F) = (Finset.univ.image F).image (codomainEquiv Y) := by
    rw [Finset.image_image]
    rfl
  rw [he, Finset.card_image_of_injective _ (codomainEquiv Y).injective]

omit [Fintype X] [DecidableEq X] [DecidableEq Y] in

/-- Equality between encoded `F`- and `G`-values is equivalent to equality between their
original values [BrassardHoyerTapp1998Collision]. -/
theorem encoded_claw_iff (F : S → Y) (G : X → Y) (s : S) (x : X) :
    codomainEquiv Y (F s) = encoded G x ↔ F s = G x := (codomainEquiv Y).injective.eq_iff

end Qatlib.Papers.CollisionProb97.MainResults.Encoding
