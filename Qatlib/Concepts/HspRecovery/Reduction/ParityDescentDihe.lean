/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentStat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Parity descent for dihedral hidden reflections

This module proves the algebraic properties of `paritySubgroupEmbedding` and `parityLift` needed
for the recursive parity step in the dihedral sieve of [Kuperberg2005]. Restricting an oracle
hiding a lifted reflection produces an oracle hiding the smaller reflection.

## Main statements

* `parityEmbedding_injective`: the parity embedding is injective.
* `parityRestriction_hides`: restriction preserves the hidden-reflection promise.
* `parityLift_unique`: the parity of a slope determines a unique smaller slope.
* `sourceParityDescent`: the combined descent specification holds.

## References

* [Kuperberg, 2005][Kuperberg2005]
-/

set_option warningAsError false


open Qatlib.Concepts.HspRecovery.RecordExtract

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib

/-- The map from residues modulo `2 ^ n` to residues modulo `2 ^ (n + 1)` obtained by doubling
the canonical representative. -/
private def evenLift (n : ℕ) (a : ZMod (2 ^ n)) : ZMod (2 ^ (n + 1)) :=
  2 * (a.val : ZMod (2 ^ (n + 1)))

/-- Doubling into the larger power-of-two modulus preserves addition. -/
private theorem evenLift_add (n : ℕ) (a b : ZMod (2 ^ n)) :
    evenLift n (a + b) = evenLift n a + evenLift n b := by
  have h : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have he (x : ZMod (2 ^ n)) : evenLift n x =
      ((2 * x.val : ℕ) : ZMod (2 ^ (n + 1))) := by simp [evenLift]
  rw [he, he, he, ← Nat.cast_add]
  apply ZMod.val_injective
  simp only [ZMod.val_natCast, ZMod.val_add, h]
  rw [← Nat.mul_add]
  simp only [Nat.mul_mod_mul_left, Nat.mod_mod]

/-- Doubling into the larger power-of-two modulus preserves subtraction. -/
private theorem evenLift_sub (n : ℕ) (a b : ZMod (2 ^ n)) :
    evenLift n (a - b) = evenLift n a - evenLift n b := by
  apply eq_sub_iff_add_eq.mpr
  rw [← evenLift_add, sub_add_cancel]

/-- The canonical representative of `parityLift n b t` is twice the representative of `t`, plus
one exactly when `b` is true. -/
theorem parityLift_val (n : ℕ) (b : Bool) (t : ZMod (2 ^ n)) :
    (parityLift n b t).val = 2 * t.val + if b then 1 else 0 := by
  have ht := ZMod.val_lt t
  have hN : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  have hcast : parityLift n b t =
      ((2 * t.val + if b then 1 else 0 : ℕ) : ZMod (2 ^ (n + 1))) := by
    cases b <;> simp [parityLift]
  rw [hcast, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- The dihedral parity embedding is injective for either choice of parity. -/
theorem parityEmbedding_injective (n : ℕ) (b : Bool) :
    Function.Injective (paritySubgroupEmbedding n b) := by
  rintro ⟨a, ta⟩ ⟨c, tc⟩ he
  have ht := congrArg (fun p : DihedralReg (2 ^ (n + 1)) => p.2) he
  have htag (d : ZMod (2 ^ n)) (tag : Bool) :
      (paritySubgroupEmbedding n b (d, tag)).2 = tag := by cases tag <;> rfl
  simp only [htag] at ht
  subst tc
  cases ta
  · have hv := congrArg (fun p : DihedralReg (2 ^ (n + 1)) => p.1.val) he
    have hv' : (parityLift n false a).val = (parityLift n false c).val := by
      simpa only [parityLift, Bool.false_eq_true, if_false, add_zero,
        paritySubgroupEmbedding] using hv
    rw [parityLift_val, parityLift_val] at hv'
    have hval : a.val = c.val := by omega
    exact Prod.ext ((ZMod.val_injective (2 ^ n)) hval) rfl
  · have hv := congrArg (fun p : DihedralReg (2 ^ (n + 1)) => p.1.val) he
    change (parityLift n b a).val = (parityLift n b c).val at hv
    rw [parityLift_val, parityLift_val] at hv
    have hval : a.val = c.val := by omega
    exact Prod.ext ((ZMod.val_injective (2 ^ n)) hval) rfl

/-- The parity embedding intertwines reflection by `t` with reflection by its parity lift. -/
private theorem parityEmbedding_reflect (n : ℕ) (b : Bool) (t : ZMod (2 ^ n))
    (p : DihedralReg (2 ^ n)) :
    paritySubgroupEmbedding n b (dihedralReflect (2 ^ n) t p) =
      dihedralReflect (2 ^ (n + 1)) (parityLift n b t) (paritySubgroupEmbedding n b p) := by
  rcases p with ⟨a, tag⟩
  cases tag <;> apply Prod.ext
  · change evenLift n (a + t) + (if b then 1 else 0) =
      evenLift n a + (evenLift n t + (if b then 1 else 0))
    rw [evenLift_add, add_assoc]
  · rfl
  · change evenLift n (a - t) =
      (evenLift n a + (if b then 1 else 0)) - (evenLift n t + (if b then 1 else 0))
    rw [evenLift_sub]
    ring
  · rfl

/-- Restricting an oracle that hides the lifted slope to the chosen parity embedding yields an
oracle hiding `t` over the smaller modulus. -/
theorem parityRestriction_hides (n : ℕ) {S : Type*}
    (f : DihedralReg (2 ^ (n + 1)) → S) (b : Bool) (t : ZMod (2 ^ n))
    (hf : DihedralReflectionHides (2 ^ (n + 1)) f (parityLift n b t)) :
    DihedralReflectionHides (2 ^ n) (parityRestrictedOracle n f b) t := by
  intro p q
  change f (paritySubgroupEmbedding n b p) = f (paritySubgroupEmbedding n b q) ↔ _
  rw [hf, ← parityEmbedding_reflect, (parityEmbedding_injective n b).eq_iff,
    (parityEmbedding_injective n b).eq_iff]

/-- Every residue modulo `2 ^ (n + 1)` has a unique preimage under the lift determined by its
representative's parity. -/
theorem parityLift_unique (n : ℕ) (s : ZMod (2 ^ (n + 1))) :
    ∃! t : ZMod (2 ^ n), parityLift n (decide (s.val % 2 = 1)) t = s := by
  have hs := ZMod.val_lt s
  have hN : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ, Nat.mul_comm]
  let t : ZMod (2 ^ n) := (s.val / 2 : ℕ)
  have ht : t.val = s.val / 2 := ZMod.val_natCast_of_lt (by omega)
  refine ⟨t, ?_, ?_⟩
  · apply ZMod.val_injective
    rw [parityLift_val, ht]
    split_ifs <;> simp_all <;> omega
  · intro u hu
    apply ZMod.val_injective
    have he := congrArg ZMod.val hu
    rw [ht]
    rw [parityLift_val] at he
    split_ifs at he <;> simp_all <;> omega

/-- The parity embeddings satisfy injectivity, preservation of the hiding promise, and unique
slope reconstruction, as required for the descent step of [Kuperberg2005]. -/
theorem sourceParityDescent : SourceParityDescent :=
  ⟨parityEmbedding_injective, fun n _ f b t => parityRestriction_hides n f b t,
    parityLift_unique⟩

end Qatlib.Concepts.HspRecovery.ReductionCore
