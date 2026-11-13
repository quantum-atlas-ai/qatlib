/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonAbelianHSP01.MainResults.Defs
import Qatlib.Papers.NonAbelianHSP01.MainResults.MembershipReduction

/-!
# Membership and identity tests in quotients

Relates the identity fiber of a hiding function to the identity in a normal quotient. For
generators commuting in the quotient, `theorem_seven` combines a coprime integer-power
membership criterion with this identity test. See [IvanyosMagniezSantha2003] for the surrounding
analysis.

## Main statements

* `theorem_seven_test`: When `I.H = N` and `N` is normal, the hiding values `I.f y` and `I.f 1`
  agree exactly when the image of `y` in `G ⧸ N` is the identity.
* `theorem_seven`: For generators commuting modulo normal `N = I.H`, quotient membership is
  equivalent to an integer-power relation with exponent coprime to the order of the target's
  quotient image; the hiding function also tests whether that image is the identity.

## References

* [Ivanyos et al., 2003][IvanyosMagniezSantha2003]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonAbelianHSP01.MainResults.Claims

/-- When `I.H = N` and `N` is normal, the hiding values `I.f y` and `I.f 1` agree exactly when
the image of `y` in `G ⧸ N` is the identity [IvanyosMagniezSantha2003]. -/
theorem theorem_seven_test {G : Type*} [Group G] {X : Type*} (N : Subgroup G)
    [N.Normal] (I : HiddenSubgroupInstance G X) (hN : I.H = N) (y : G) :
    I.f y = I.f 1 ↔ (y : G ⧸ N) = 1 :=
  f_eq_one_iff_quotient_eq_one (N := N) I.f (fun a b => by rw [I.hides, hN]) y

/-- For generators commuting modulo normal `N = I.H`, quotient membership is equivalent to an
integer-power relation with exponent coprime to the order of the target's quotient image;
the hiding function also tests whether that image is the identity
[IvanyosMagniezSantha2003]. -/
theorem theorem_seven {G : Type*} [Group G] {X : Type*} (N : Subgroup G)
    [N.Normal] (I : HiddenSubgroupInstance G X) (hN : I.H = N)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : ι → G) (g : G)
    (hcomm : ∀ i j : ι, Commute ((h i : G ⧸ N)) ((h j : G ⧸ N))) :
    ((g : G ⧸ N) ∈ Subgroup.closure (Set.range (fun i => (h i : G ⧸ N))) ↔
        ∃ (m : ι → ℤ) (n : ℤ),
          Nat.Coprime n.natAbs (orderOf ((g : G ⧸ N))) ∧
            (zpowProd (fun i => (h i : G ⧸ N)) hcomm m : G ⧸ N) *
              (g : G ⧸ N) ^ (-n) = 1) ∧
      (I.f g = I.f 1 ↔ (g : G ⧸ N) = 1) :=
  ⟨quotient_membership_iff h g hcomm, theorem_seven_test N I hN g⟩

end Qatlib.Papers.NonAbelianHSP01.MainResults.Claims
