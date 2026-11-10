/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction.ActualSubstitution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
open Qatlib.Papers.ParityLimit98.MainResults.LowerBound
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.QueryComplexity.DegreeMethod

def boolZmod : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := decide (z = 1)
  left_inv := by decide
  right_inv := by decide

def sourceLabels (N : ℕ) [NeZero N] : (Fin N × Bool) ≃ (ZMod N × ZMod 2) :=
  (zmodEquivFin N).prodCongr boolZmod

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

theorem hardPermutation_iterate_conjugate {N : ℕ} [NeZero N] (f : Fin N → Bool)
    (k : ℕ) (p : Fin N × Bool) :
    sourceLabels N ((hardPermutation f)^[k] p) =
      (iterMap (fun x => f ((zmodEquivFin N).symm x)))^[k] (sourceLabels N p) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', hardPermutation_conjugate, ih,
      Function.iterate_succ_apply']

theorem truthSum_eq_bool_parity {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    truthSum (fun x => f ((zmodEquivFin N).symm x)) = boolZmod (parityOddB f) := by
  rw [truthSum_comp_eq_card]
  have h := Nat.mod_lt (Finset.univ.filter (fun i : Fin N => f i = true)).card (by omega : 0 < 2)
  rw [← ZMod.natCast_mod (n := 2)]
  change (((boolSupp f).card % 2 : ℕ) : ZMod 2) = boolZmod (parityOddB f)
  change (boolSupp f).card % 2 < 2 at h
  interval_cases hm : (boolSupp f).card % 2 <;> simp [parityOddB, hm, boolZmod]

theorem hardPermutation_iterate_card {N : ℕ} [NeZero N] (f : Fin N → Bool) :
    (hardPermutation f)^[N] (0, false) = (0, parityOddB f) := by
  apply (sourceLabels N).injective
  rw [hardPermutation_iterate_conjugate]
  have hz : sourceLabels N (0, false) = (0,0) := by
    simp [sourceLabels, zmodEquivFin, boolZmod]
  rw [hz, iterMap_iterate_card, truthSum_eq_bool_parity]
  simp [sourceLabels, zmodEquivFin]

end Qatlib.Papers.ParityLimit98.MainResults.IteratedFunction
