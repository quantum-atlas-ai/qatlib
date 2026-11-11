/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction.ActualSubstitution

/-!
# Hard permutation iteration and parity

`sourceLabels` identifies address-bit pairs with modular coordinates and conjugates
`hardPermutation` to the source iteration map. Summing the Boolean input over one full address
cycle identifies the `N`th iterate with parity, the reduction underlying the iteration lower
bound in [FarhiEtAl1998].

## Main statements

* `hardPermutation_iterate_conjugate`: modular labels intertwine every iterate of the hard
  permutation and the source map.
* `hardPermutation_iterate_card`: after one full cycle the answer bit equals the input parity.

## References

* [Farhi et al., 1998][FarhiEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
open Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

/-- The equivalence between `Bool` and `ZMod 2` sending `false` to zero and `true` to one. -/
def boolZmod : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

/-- The product equivalence identifying `Fin N × Bool` with `ZMod N × ZMod 2` for nonzero `N`. -/
def sourceLabels (N : ℕ) [NeZero N] : (Fin N × Bool) ≃ (ZMod N × ZMod 2) :=
  (zmodEquivFin N).prodCongr boolZmod

/-- The modular labeling intertwines the hard permutation with `iterMap` for the relabeled
Boolean input. -/
theorem hardPermutation_conjugate {N : ℕ} [NeZero N] (f : Fin N → Bool)
    (p : Fin N × Bool) :
    sourceLabels N (hardPermutation f p) =
      iterMap (fun x => f ((zmodEquivFin N).symm x)) (sourceLabels N p) := by
  rcases p with ⟨x,b⟩
  change ((zmodEquivFin N) (cycleNext N x), boolZmod (b ^^ f x)) =
    ((zmodEquivFin N) x + 1, boolZmod b +
      if f ((zmodEquivFin N).symm ((zmodEquivFin N) x)) = true then 1 else 0)
  rw [Equiv.symm_apply_apply]
  apply Prod.ext
  · exact (zmodEquivFin N).apply_symm_apply _
  · change boolZmod (b ^^ f x) = boolZmod b + (if f x = true then 1 else 0)
    cases b <;> cases f x <;> decide

/-- The modular labeling intertwines every natural iterate of the hard permutation with the
corresponding iterate of the relabeled `iterMap`. -/
theorem hardPermutation_iterate_conjugate {N : ℕ} [NeZero N] (f : Fin N → Bool)
    (k : ℕ) (p : Fin N × Bool) :
    sourceLabels N ((hardPermutation f)^[k] p) =
      (iterMap (fun x => f ((zmodEquivFin N).symm x)))^[k] (sourceLabels N p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hardPermutation_conjugate, ih,
      Function.iterate_succ_apply']

/-- The modular sum of the relabeled Boolean input equals the image of its parity under
`boolZmod`. -/
theorem truthSum_eq_bool_parity {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    truthSum (fun x => f ((zmodEquivFin N).symm x)) = boolZmod (parityOddB f) := by
  rw [truthSum_comp_eq_card]
  have h := Nat.mod_lt (Finset.univ.filter (fun i : Fin N => f i = true)).card (by omega : 0 < 2)
  rw [← ZMod.natCast_mod (n := 2)]
  change (((boolSupp f).card % 2 : ℕ) : ZMod 2) = boolZmod (parityOddB f)
  change (boolSupp f).card % 2 < 2 at h
  interval_cases hm : (boolSupp f).card % 2 <;> simp [parityOddB, hm, boolZmod]

/-- The `N`th iterate of the hard permutation sends `(0, false)` to `(0, parityOddB f)`. See
[FarhiEtAl1998]. -/
theorem hardPermutation_iterate_card {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    (hardPermutation f)^[N] (0, false) = (0, parityOddB f) := by
  apply (sourceLabels N).injective
  rw [hardPermutation_iterate_conjugate]
  have hz : sourceLabels N (0, false) = (0,0) := by
    simp [sourceLabels, zmodEquivFin, boolZmod]
  rw [hz, iterMap_iterate_card, truthSum_eq_bool_parity]
  simp [sourceLabels, zmodEquivFin]

end Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
