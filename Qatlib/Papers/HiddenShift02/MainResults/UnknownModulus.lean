/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HiddenShift02.MainResults.RingCharacter
import Qatlib.Papers.HiddenShift02.MainResults.FieldCharacter
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Nat.Totient
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.HiddenShift02.MainResults.FourierCore
open scoped BigOperators ComplexConjugate

namespace Qatlib.Papers.HiddenShift02.MainResults.UnknownModulus

theorem fourier_mulShift_zero {ell : ℕ} [Fact ell.Prime]
    (χ : MulChar (ZMod ell) ℂ) (hχ : χ ≠ 1) (ψ : AddChar (ZMod ell) ℂ) (s : ZMod ell) :
    fourier (fun x => χ (x + s)) (ψ.mulShift 0) = 0 := by
  classical
  have htriv : ψ.mulShift 0 = 1 := by
    ext x
    simp [AddChar.mulShift_apply]
  have hsum : fourier χ (1 : AddChar (ZMod ell) ℂ) = 0 := by
    rw [fourier_apply]
    have hz : (∑ x : ZMod ell, conj ((1 : AddChar (ZMod ell) ℂ) x) * χ x) = 0 := by
      simp only [AddChar.one_apply, map_one, one_mul]
      exact MulChar.sum_eq_zero_of_ne_one hχ
    rw [hz, mul_zero]
  rw [htriv, fourier_shift, hsum, mul_zero]

theorem fourier_mulShift_ne_zero_of_ne_zero {ell : ℕ} [Fact ell.Prime]
    (χ : MulChar (ZMod ell) ℂ) (hχ : χ ≠ 1) (ψ : AddChar (ZMod ell) ℂ)
    (hψhat : ‖fourier χ ψ‖ = 1) (s : ZMod ell) {y : ZMod ell} (hy : y ≠ 0) :
    fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0 := by
  have hF : fourier χ ψ ≠ 0 := by
    intro h
    rw [h] at hψhat
    simp at hψhat
  have hχy : χ⁻¹ y ≠ 0 := by
    intro h
    exact hy ((FieldCharacter.mulChar_eq_zero_iff χ⁻¹ y).mp h)
  have hval : (ψ.mulShift y) s ≠ 0 := (AddChar.val_isUnit (ψ.mulShift y) s).ne_zero
  rw [fourier_shift, FieldCharacter.fourier_mulShift_char χ ψ hy, ← mul_assoc]
  exact mul_ne_zero (mul_ne_zero hval hχy) hF

theorem source_theorem3_prime {ell : ℕ} [Fact ell.Prime]
    (χ : MulChar (ZMod ell) ℂ) (hχ : χ ≠ 1) (ψ : AddChar (ZMod ell) ℂ)
    (hψ : ψ.IsPrimitive) (hψhat : ‖fourier χ ψ‖ = 1) (s : ZMod ell) :
    (∀ y : ZMod ell,
        fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0 ↔ y ≠ 0) ∧
      (∀ y : ZMod ell,
        fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0 →
          Nat.Coprime y.val ell ∧ y.val < ell) ∧
      ((Finset.univ.filter
          (fun y : ZMod ell => fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0)).card
        = Nat.totient ell) := by
  classical
  have hsupp : ∀ y : ZMod ell,
      fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0 ↔ y ≠ 0 := by
    intro y
    constructor
    · intro h
      by_contra hy
      rw [hy] at h
      exact h (fourier_mulShift_zero χ hχ ψ s)
    · intro hy
      exact fourier_mulShift_ne_zero_of_ne_zero χ hχ ψ hψhat s hy
  refine ⟨hsupp, ?_, ?_⟩
  · intro y hy
    have hy0 : y ≠ 0 := (hsupp y).mp hy
    have hunit : IsUnit y := isUnit_iff_ne_zero.mpr hy0
    refine ⟨?_, ZMod.val_lt y⟩
    have h := ZMod.val_coe_unit_coprime hunit.unit
    rwa [IsUnit.unit_spec] at h
  · have hfilt : (Finset.univ.filter
        (fun y : ZMod ell => fourier (fun x => χ (x + s)) (ψ.mulShift y) ≠ 0))
        = Finset.univ.erase (0 : ZMod ell) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      rw [hsupp y]
      simp
    rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card,
      Nat.totient_prime (Fact.out)]

theorem source_theorem3_reduction {ell : ℕ} [NeZero ell]
    (χ : MulChar (ZMod ell) ℂ) (ψ : AddChar (ZMod ell) ℂ) (s : ZMod ell)
    (hU : 0 < Fintype.card (ZMod ell)ˣ) (hψhat : ‖fourier χ ψ‖ = 1) :
    ((Finset.univ.filter (fun x : ZMod ell => χ (x + s) ≠ 0)).card : ℝ) /
        (Fintype.card (ZMod ell) : ℝ) = (Nat.totient ell : ℝ) / (ell : ℝ) ∧
      ‖(((Real.sqrt ((Fintype.card (ZMod ell)ˣ : ℝ))) : ℝ) : ℂ)⁻¹ *
          RingCharacter.algorithmAmplitude (ZMod ell) χ ψ s (-s)‖ ^ 2
        = (Nat.totient ell : ℝ) / (ell : ℝ) ∧
      ((Nat.totient ell : ℝ) / (ell : ℝ)) * ((Nat.totient ell : ℝ) / (ell : ℝ)) ^ 2
        = ((Nat.totient ell : ℝ) / (ell : ℝ)) ^ 3 := by
  have h2 := RingCharacter.source_theorem2 (n := ell) (ell := ell)
    χ ψ s χ ψ s (by simpa using hU) (by simpa using hU)
    (by simpa using hψhat) (by simpa using hψhat) le_rfl
  exact ⟨h2.1, h2.2.1, by ring⟩

end Qatlib.Papers.HiddenShift02.MainResults.UnknownModulus
