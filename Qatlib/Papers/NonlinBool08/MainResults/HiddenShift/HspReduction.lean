/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.BentCore.BentFacts
import Qatlib.Papers.NonlinBool08.MainResults.HiddenShift.Theorems
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.HiddenShift

open Qatlib.Papers.NonlinBool08.MainResults.BentCore

def qfun {n : ℕ} (f : BVec n → ZMod 2) (x : BVec n) (y : BVec n) : ℤ :=
  eps (f (x + y))

theorem qfun_injective {n : ℕ} {f : BVec n → ZMod 2} (hf : Bent f) :
    Function.Injective (qfun f) := by
  intro x x' hxx
  have hfun : qfun f x = qfun f x' := hxx
  have hpt : ∀ y : BVec n, eps (f (x + y)) = eps (f (x' + y)) := by
    intro y
    have := congrFun hfun y
    simpa [qfun] using this
  have hsum : (∑ y : BVec n, eps (f (x + y) + f (x' + y))) = (2 : ℤ) ^ n := by
    have hterm : ∀ y : BVec n, eps (f (x + y) + f (x' + y)) = 1 := by
      intro y
      rw [eps_add, hpt y, ← pow_two]
      exact eps_sq _
    rw [show (∑ y : BVec n, eps (f (x + y) + f (x' + y))) = ∑ _y : BVec n, (1 : ℤ) from
      Finset.sum_congr rfl (fun y _ => hterm y)]
    simp
  have hgram := bent_gram hf x x'
  rw [hgram] at hsum
  by_cases h : x = x'
  · exact h
  · rw [if_neg h] at hsum
    exact absurd hsum.symm (pow_ne_zero n (by norm_num : (2 : ℤ) ≠ 0))

def hidingFun {n : ℕ} (f g : BVec n → ZMod 2) (b : ZMod 2) (x y : BVec n) : ℤ :=
  if b = 0 then qfun f x y else qfun g x y

lemma hidingFun_one {n : ℕ} {f g : BVec n → ZMod 2} {s : BVec n}
    (hg : HidesShiftOn f g s) (x : BVec n) :
    hidingFun f g 1 x = qfun f (x + s) := by
  funext y
  simp only [hidingFun, qfun]
  rw [if_neg (by decide : (1 : ZMod 2) ≠ 0)]
  have hgy : g (x + y) = f (x + y + s) := hg (x + y)
  rw [hgy]
  congr 2
  abel

lemma add_add_self_left {n : ℕ} (x s : BVec n) : (x + s) + x = s := by
  rw [add_comm (x + s) x, ← add_assoc, BentCore.add_self_bvec, zero_add]

lemma add_add_self_right {n : ℕ} (x s : BVec n) : x + (x + s) = s := by
  rw [← add_assoc, BentCore.add_self_bvec, zero_add]

theorem hidingFun_eq_iff {n : ℕ} {f g : BVec n → ZMod 2} {s : BVec n}
    (hf : Bent f) (hg : HidesShiftOn f g s) (b b' : ZMod 2) (x x' : BVec n) :
    hidingFun f g b x = hidingFun f g b' x' ↔
      ((b, x) = (b', x') ∨ (b + b' = 1 ∧ x + x' = s)) := by
  have hinj := qfun_injective hf
  have honeslice : ∀ x : BVec n, hidingFun f g 1 x = qfun f (x + s) := hidingFun_one hg
  have hzero : ∀ x : BVec n, hidingFun f g 0 x = qfun f x := by
    intro x
    funext y
    simp [hidingFun, qfun]

  have hb : b = 0 ∨ b = 1 := zmod2_cases b
  have hb' : b' = 0 ∨ b' = 1 := zmod2_cases b'
  rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
  · rw [hzero, hzero, hinj.eq_iff]
    constructor
    · intro h; exact Or.inl (by rw [h])
    · rintro (h | h)
      · exact congrArg Prod.snd h
      · exact absurd h.1 (by decide)
  · rw [hzero, honeslice, hinj.eq_iff]
    constructor
    · intro h
      exact Or.inr ⟨by decide, by rw [h]; exact add_add_self_left x' s⟩
    · rintro (h | h)
      · have hfst : (0 : ZMod 2) = 1 := congrArg Prod.fst h
        exact absurd hfst (by decide)
      · calc x = x + 0 := (add_zero x).symm
          _ = x + (x' + x') := by rw [BentCore.add_self_bvec]
          _ = (x + x') + x' := by abel
          _ = s + x' := by rw [h.2]
          _ = x' + s := add_comm s x'
  · rw [honeslice, hzero, hinj.eq_iff]
    constructor
    · intro h
      exact Or.inr ⟨by decide, by rw [← h]; exact add_add_self_right x s⟩
    · rintro (h | h)
      · have hfst : (1 : ZMod 2) = 0 := congrArg Prod.fst h
        exact absurd hfst (by decide)
      · rw [← h.2]
        exact add_add_self_right x x'
  · rw [honeslice, honeslice, hinj.eq_iff]
    constructor
    · intro h
      refine Or.inl ?_
      have hx : x = x' := add_right_cancel h
      rw [hx]
    · rintro (h | h)
      · rw [show x = x' from congrArg Prod.snd h]
      · exact absurd h.1 (by decide)

end Qatlib.Papers.NonlinBool08.MainResults.HiddenShift
