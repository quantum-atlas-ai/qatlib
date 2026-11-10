/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HiddenShift02.MainResults.FieldCharacter
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.FieldTheory.Finite.Basic
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.HiddenShift02.MainResults.FieldCharacter
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.HomomorphicEncryption

variable {F S : Type*}

structure HomomorphicEncryption (F S : Type*) where

  enc : F → S

  dec : S → F

  add : S → S → S

  mul : S → S → S

  zeroTest : S → Bool

structure SchemeSpec [Zero F] [Add F] [Mul F] (H : HomomorphicEncryption F S) : Prop where

  dec_enc : ∀ x, H.dec (H.enc x) = x

  dec_add : ∀ c₁ c₂, H.dec (H.add c₁ c₂) = H.dec c₁ + H.dec c₂

  dec_mul : ∀ c₁ c₂, H.dec (H.mul c₁ c₂) = H.dec c₁ * H.dec c₂

  zeroTest_dec : ∀ c, H.zeroTest c = true ↔ H.dec c = 0

namespace HomomorphicEncryption

def epow [One F] (H : HomomorphicEncryption F S) (c : S) : ℕ → S
  | 0 => H.enc 1
  | n + 1 => H.mul c (epow H c n)

@[simp]
theorem epow_zero [One F] (H : HomomorphicEncryption F S) (c : S) :
    H.epow c 0 = H.enc 1 := rfl

@[simp]
theorem epow_succ [One F] (H : HomomorphicEncryption F S) (c : S) (n : ℕ) :
    H.epow c (n + 1) = H.mul c (H.epow c n) := rfl

end HomomorphicEncryption

open HomomorphicEncryption

theorem dec_epow [Field F] (H : HomomorphicEncryption F S) (h : SchemeSpec H)
    (c : S) (n : ℕ) :
    H.dec (H.epow c n) = (H.dec c) ^ n := by
  induction n with
  | zero => simp [HomomorphicEncryption.epow, h.dec_enc]
  | succ n ih =>
      rw [epow_succ, h.dec_mul, ih, pow_succ]
      ring

theorem zeroTest_enc [Field F] (H : HomomorphicEncryption F S) (h : SchemeSpec H)
    (x : F) :
    H.zeroTest (H.enc x) = true ↔ x = 0 := by
  rw [h.zeroTest_dec, h.dec_enc]

theorem zeroTest_add_enc [Field F] (H : HomomorphicEncryption F S) (h : SchemeSpec H)
    (c : S) (v : F) :
    H.zeroTest (H.add c (H.enc v)) = true ↔ H.dec c + v = 0 := by
  rw [h.zeroTest_dec, h.dec_add, h.dec_enc]

theorem zero_test_decides [Field F] (H : HomomorphicEncryption F S) (h : SchemeSpec H)
    (c : S) :
    (H.zeroTest c = true ↔ H.dec c = 0) ∧
      (H.zeroTest (H.add c (H.enc 1)) = true ↔ H.dec c = -1) ∧
      (H.zeroTest (H.add c (H.enc (-1))) = true ↔ H.dec c = 1) := by
  refine ⟨h.zeroTest_dec c, ?_, ?_⟩
  · rw [zeroTest_add_enc H h]
    exact eq_neg_iff_add_eq_zero.symm
  · rw [zeroTest_add_enc H h, show H.dec c + (-1) = H.dec c - 1 by ring, sub_eq_zero]

theorem dec_epow_card_sub_one [Field F] [Fintype F]
    (H : HomomorphicEncryption F S) (h : SchemeSpec H) {s : F} (hs : s ≠ 0) :
    H.dec (H.epow (H.enc s) (Fintype.card F - 1)) = 1 := by
  rw [dec_epow H h, h.dec_enc]
  exact FiniteField.pow_card_sub_one_eq_one s hs

theorem dec_epow_shift [Field F] (H : HomomorphicEncryption F S) (h : SchemeSpec H)
    (x s : F) (k : ℕ) :
    H.dec (H.epow (H.add (H.enc x) (H.enc s)) k) = (x + s) ^ k := by
  rw [dec_epow H h, h.dec_add, h.dec_enc, h.dec_enc]

theorem dec_encrypted_legendre_mem [Field F] [Fintype F] [DecidableEq F]
    (H : HomomorphicEncryption F S) (h : SchemeSpec H) (hodd : ringChar F ≠ 2)
    (x s : F) :
    H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = 0 ∨
      H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = 1 ∨
      H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = -1 := by
  rw [dec_epow_shift H h]
  have hcard2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hexp : Fintype.card F / 2 ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos hcard2 (by norm_num))
  by_cases hy : x + s = 0
  · left
    rw [hy]
    exact zero_pow hexp
  · rcases FiniteField.pow_dichotomy hodd hy with h1 | h1
    · right; left; exact h1
    · right; right; exact h1

theorem dec_encrypted_legendre_zero_test [Field F] [Fintype F] [DecidableEq F]
    (H : HomomorphicEncryption F S) (h : SchemeSpec H) (hodd : ringChar F ≠ 2)
    (x s : F) :
    H.zeroTest (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = true
      ↔ x + s = 0 := by
  rw [h.zeroTest_dec, dec_epow_shift H h]
  have hcard2 : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hexp : Fintype.card F / 2 ≠ 0 :=
    Nat.ne_of_gt (Nat.div_pos hcard2 (by norm_num))
  constructor
  · intro hzero
    by_contra hy
    rcases FiniteField.pow_dichotomy hodd hy with h1 | h1
    · rw [h1] at hzero
      exact one_ne_zero hzero
    · rw [h1] at hzero
      exact neg_ne_zero.mpr one_ne_zero hzero
  · intro hzero
    rw [hzero]
    exact zero_pow hexp

noncomputable def legendreChar (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    MulChar F ℂ :=
  (quadraticChar F).ringHomComp (Int.castRingHom ℂ)

theorem legendreChar_apply (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (x : F) : legendreChar F x = ((quadraticChar F x : ℤ) : ℂ) := by
  simp [legendreChar]

theorem legendreChar_ne_one (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hodd : ringChar F ≠ 2) : legendreChar F ≠ 1 := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' (F := F) hodd
  intro hone
  have h1 : legendreChar F (a : F) = 1 := by
    rw [hone]
    exact MulChar.one_apply a.isUnit
  have h2 : legendreChar F (a : F) = -1 := by
    rw [legendreChar_apply, ha]
    norm_num
  rw [h2] at h1
  exact Ring.neg_one_ne_one_of_char_ne_two (by norm_num : ringChar ℂ ≠ 2) h1

theorem source_corollary1 [Field F] [Fintype F] [DecidableEq F]
    (H : HomomorphicEncryption F S) (h : SchemeSpec H) (hodd : ringChar F ≠ 2)
    (hq : 2 ≤ Fintype.card F) (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (s : F) :
    (H.zeroTest (H.enc s) = true ↔ s = 0) ∧
      (s ≠ 0 → H.dec (H.epow (H.enc s) (Fintype.card F - 1)) = 1) ∧
      (∀ x : F,
        H.zeroTest (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = true
          ↔ x + s = 0) ∧
      (∀ x : F,
        H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = 0 ∨
          H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = 1 ∨
          H.dec (H.epow (H.add (H.enc x) (H.enc s)) (Fintype.card F / 2)) = -1) ∧
      ((Finset.univ.filter (fun x : F => legendreChar F (x + s) ≠ 0)).card : ℝ) /
          (Fintype.card F : ℝ) = 1 - 1 / (Fintype.card F : ℝ) ∧
      ‖(((Real.sqrt ((Fintype.card F : ℝ) - 1) : ℝ)) : ℂ)⁻¹ *
          algorithmAmplitude (legendreChar F) ψ s (-s)‖ ^ 2
        = 1 - 1 / (Fintype.card F : ℝ) := by
  have hχ : legendreChar F ≠ 1 := legendreChar_ne_one F hodd
  have hT1 := source_theorem1 (legendreChar F) hχ ψ hψ hq s
  exact
    ⟨zeroTest_enc H h s,
      fun hs => dec_epow_card_sub_one H h hs,
      fun x => dec_encrypted_legendre_zero_test H h hodd x s,
      fun x => dec_encrypted_legendre_mem H h hodd x s,
      hT1.1, hT1.2.1⟩

end Qatlib.Papers.HiddenShift02.MainResults.HomomorphicEncryption
