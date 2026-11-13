/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup

/-!
# Binary pairing on the wreath product

`mu` defines a binary-valued pairing on `Wreath n`, with formulas according to the two final
coordinates. `perp` and `perpSub` collect elements orthogonal to a set or subgroup.
Simultaneously swapping the two vector blocks preserves the pairing. This development
accompanies [RoettelerBeth1998].

## Main statements

* `mu_zero_zero`, `mu_zero_one`, `mu_one_zero`, and `mu_one_one`: the four pairing formulas.
* `perpSub`: the orthogonal-complement set of a subgroup.
* `mu_swapFun_swapFun`: invariance under simultaneous swapping.

## References

* [Roetteler and Beth, 1998][RoettelerBeth1998]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonabelianHSP98.MainResults.Pairing

open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup
open Qatlib.Papers.NonabelianHSP98.MainResults.WreathGroup.Wreath
open Finset

variable {n : ℕ}

macro "zring" : tactic => `(tactic| (ring_nf <;> reduce_mod_char))

/-- The `ZMod 2` pairing on wreath-product coordinates used to define orthogonality in
[RoettelerBeth1998]. -/
def mu (g h : Wreath n) : ZMod 2 :=
  ((∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i))
  + g.a * h.a
  + (g.a + h.a) * (((∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i)) + g.a * h.a
      + ((∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i)))

/-- When both final coordinates are zero, `mu g h` is the sum of the dot products of
corresponding vector blocks. -/
lemma mu_zero_zero (g h : Wreath n) (hg : g.a = 0) (hh : h.a = 0) :
    mu g h = (∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i) := by
  simp only [mu, hg, hh]
  zring

/-- When the final coordinates of `g` and `h` are zero and one, `mu g h` is the sum of the
cross-block dot products. -/
lemma mu_zero_one (g h : Wreath n) (hg : g.a = 0) (hh : h.a = 1) :
    mu g h = (∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i) := by
  simp only [mu, hg, hh]
  zring

/-- When the final coordinates of `g` and `h` are one and zero, `mu g h` is the sum of the
cross-block dot products. -/
lemma mu_one_zero (g h : Wreath n) (hg : g.a = 1) (hh : h.a = 0) :
    mu g h = (∑ i, g.x i * h.y i) + (∑ i, h.x i * g.y i) := by
  simp only [mu, hg, hh]
  zring

/-- When both final coordinates are one, `mu g h` is the sum of corresponding-block dot products
plus one. -/
lemma mu_one_one (g h : Wreath n) (hg : g.a = 1) (hh : h.a = 1) :
    mu g h = (∑ i, g.x i * h.x i) + (∑ i, g.y i * h.y i) + 1 := by
  simp only [mu, hg, hh]
  zring

/-- The set of elements whose `mu` pairing with every element of `U` is zero. -/
def perp (U : Set (Wreath n)) : Set (Wreath n) := {g | ∀ u ∈ U, mu g u = 0}

/-- Membership in `perp U` means that pairing with every element of `U` gives zero. -/
@[simp] lemma mem_perp {U : Set (Wreath n)} {g : Wreath n} :
    g ∈ perp U ↔ ∀ u ∈ U, mu g u = 0 := Iff.rfl

/-- The orthogonal-complement set of a subgroup under `mu`. -/
def perpSub (U : Subgroup (Wreath n)) : Set (Wreath n) := perp (U : Set (Wreath n))

/-- Membership in `perpSub U` means that pairing with every element of the subgroup gives zero. -/
lemma mem_perpSub {U : Subgroup (Wreath n)} {g : Wreath n} :
    g ∈ perpSub U ↔ ∀ u ∈ U, mu g u = 0 := Iff.rfl

/-- Simultaneously applying `swapFun` to both arguments preserves `mu`. -/
lemma mu_swapFun_swapFun (g h : Wreath n) : mu (swapFun g) (swapFun h) = mu g h := by
  simp only [mu, swapFun_x, swapFun_y, swapFun_a]
  rw [show (∑ i, g.y i * h.x i) = ∑ i, h.x i * g.y i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [show (∑ i, g.x i * h.y i) = ∑ i, h.y i * g.x i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [show (∑ i, h.y i * g.x i) = ∑ i, g.x i * h.y i from
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  zring

end Qatlib.Papers.NonabelianHSP98.MainResults.Pairing
