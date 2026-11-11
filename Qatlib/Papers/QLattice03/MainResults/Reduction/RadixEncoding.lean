/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.ZMod.Basic

/-!
# Radix encoding and decoding of vector differences

`radix` and `enc` encode finite vectors as base-`B` integers. The shift `shiftConst` allows
`decode` to recover coordinate differences from encoded integer differences when `B = 2 * M` and
`M > 0`. See [Regev2004] for the paper context.

## Main statements

* `radix_eq_sum`: The radix encoding equals `∑ i, a i * B^i`.
* `digitsAppend_radix`: For `B > 1`, extracting `n` padded digits from a radix encoding recovers
  the original length-`n` digit list.
* `decode_enc`: When `B = 2 * M` and `M > 0`, decoding the difference of two encoded vectors
  recovers their coordinatewise integer difference.

## References

* [Regev, 2004][Regev2004]
-/

set_option autoImplicit false

open scoped Classical
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.QLattice03.MainResults.Reduction

open Finset

/-- The integer formed from the length-`n` digit list `a` in base `B`, with the first coordinate
least significant. -/
def radix (B n : ℕ) (a : Fin n → ℕ) : ℕ := Nat.ofDigits B (List.ofFn a)

/-- Converting the digit list of a finite function to an integer equals the sum of its
coordinates times successive powers of the base. -/
theorem ofDigits_ofFn (B n : ℕ) (a : Fin n → ℕ) :
    Nat.ofDigits B (List.ofFn a) = ∑ i : Fin n, a i * B ^ (i : ℕ) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    simp only [List.ofFn_succ', List.concat_eq_append, Nat.ofDigits_append,
      Nat.ofDigits_singleton, List.length_ofFn, ih (fun i => a (Fin.castSucc i)),
      Fin.sum_univ_castSucc, Fin.val_last, Fin.val_castSucc]
    ring

/-- The radix encoding equals `∑ i, a i * B^i`. -/
theorem radix_eq_sum (B n : ℕ) (a : Fin n → ℕ) :
    radix B n a = ∑ i : Fin n, a i * B ^ (i : ℕ) :=
  ofDigits_ofFn B n a

/-- If `B > 1`, the radix encoding of `n` digits from `Fin B` is strictly less than `B^n`. -/
theorem radix_lt {B n : ℕ} (hB : 1 < B) (a : Fin n → Fin B) :
    radix B n (fun i => (a i : ℕ)) < B ^ n := by
  have hl : ∀ x ∈ List.ofFn (fun i : Fin n => (a i : ℕ)), x < B := by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (a i).isLt
  have h := Nat.ofDigits_lt_base_pow_length hB hl
  rw [List.length_ofFn] at h
  simpa [radix] using h

/-- For `B > 1`, extracting `n` padded digits from a radix encoding recovers the original
length-`n` digit list. -/
theorem digitsAppend_radix {B n : ℕ} (hB : 1 < B) (d : Fin n → Fin B) :
    Nat.digitsAppend B n (radix B n (fun i => (d i : ℕ)))
      = List.ofFn (fun i => (d i : ℕ)) := by
  have hmem : List.ofFn (fun i : Fin n => ((d i : Fin B) : ℕ))
      ∈ {L : List ℕ | L.length = n ∧ ∀ x ∈ L, x < B} := by
    simp only [Set.mem_setOf_eq, List.length_ofFn, true_and]
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact (d i).isLt
  exact (Nat.setInvOn_digitsAppend_ofDigits hB n).1 hmem

/-- Defaulted lookup at a valid index in `List.ofFn f` returns the corresponding value of `f`. -/
theorem getD_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) (d : α) :
    List.getD (List.ofFn f) (i : ℕ) d = f i := by
  rw [List.getD_eq_get (i := ⟨i, by rw [List.length_ofFn]; exact i.isLt⟩)]
  rw [List.get_ofFn]
  simp

/-- The radix encoding in base `B` of the natural values of the coordinates of `a`. -/
def enc (B n : ℕ) {M : ℕ} (a : Fin n → Fin M) : ℕ :=
  radix B n (fun i => (a i : ℕ))

/-- The radix encoding of the constant length-`n` digit vector with value `M`. -/
def shiftConst (B n M : ℕ) : ℕ := radix B n (fun _ => M)

/-- The coordinate decoder that adds `shiftConst`, converts to a natural number, extracts `n`
padded base-`B` digits, and subtracts `M` from each digit. -/
noncomputable def decode (B n M : ℕ) (D : ℤ) : Fin n → ℤ :=
  fun i =>
    ((List.getD (Nat.digitsAppend B n (D + (shiftConst B n M : ℤ)).toNat) (i : ℕ) 0 : ℕ) : ℤ)
      - (M : ℤ)

/-- When `B = 2 * M` and `M > 0`, decoding the difference of two encoded vectors recovers their
coordinatewise integer difference. -/
theorem decode_enc {B n M : ℕ} (hB : B = 2 * M) (hM : 0 < M)
    (a a' : Fin n → Fin M) :
    decode B n M ((enc B n a' : ℤ) - (enc B n a : ℤ))
      = fun i => (a' i : ℤ) - (a i : ℤ) := by
  have hB2 : 1 < B := by omega

  set dN : Fin n → ℕ := fun i => ((a' i : ℤ) - (a i : ℤ) + (M : ℤ)).toNat with hdN
  have hdc_nonneg : ∀ i, 0 ≤ (a' i : ℤ) - (a i : ℤ) + (M : ℤ) := by
    intro i
    have h1 : (a' i : ℤ) ≤ (M : ℤ) - 1 := by have := (a' i).isLt; omega
    have h2 : (0 : ℤ) ≤ (a i : ℤ) := Int.natCast_nonneg _
    omega
  have hd_eq : ∀ i, (dN i : ℤ) = (a' i : ℤ) - (a i : ℤ) + (M : ℤ) := by
    intro i
    rw [hdN]
    exact Int.toNat_of_nonneg (hdc_nonneg i)
  have hd_lt : ∀ i, dN i < B := by
    intro i
    have ha : (0 : ℤ) ≤ (a i : ℤ) := Int.natCast_nonneg _
    have ha' : (a' i : ℤ) ≤ (M : ℤ) - 1 := by have := (a' i).isLt; omega
    have hlt : (a' i : ℤ) - (a i : ℤ) + (M : ℤ) < (B : ℤ) := by omega
    have hcast : ((dN i : ℤ)) < (B : ℤ) := by rw [hd_eq i]; exact hlt
    exact_mod_cast hcast

  have hcoord : ∀ i, (a' i : ℕ) + M = (a i : ℕ) + dN i := by
    intro i
    have hZ : (a' i : ℤ) + (M : ℤ) = (a i : ℤ) + (dN i : ℤ) := by
      have h := hd_eq i; linarith
    exact_mod_cast hZ
  have hnat : enc B n a' + shiftConst B n M = enc B n a + radix B n dN := by
    simp only [enc, shiftConst, radix_eq_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Nat.add_mul, ← Nat.add_mul, hcoord i]
  have hZ : ((enc B n a' : ℤ) - (enc B n a : ℤ)) + (shiftConst B n M : ℤ)
      = (radix B n dN : ℤ) := by
    have hZ' : (enc B n a' : ℤ) + (shiftConst B n M : ℤ)
        = (enc B n a : ℤ) + (radix B n dN : ℤ) := by
      exact_mod_cast hnat
    linarith
  have htoNat : (((enc B n a' : ℤ) - (enc B n a : ℤ)) + (shiftConst B n M : ℤ)).toNat
      = radix B n dN := by
    rw [hZ, Int.toNat_natCast]
  have hdigits : Nat.digitsAppend B n
      ((((enc B n a' : ℤ) - (enc B n a : ℤ)) + (shiftConst B n M : ℤ)).toNat)
      = List.ofFn (fun i : Fin n => dN i) := by
    rw [htoNat]
    simpa using digitsAppend_radix (B := B) (n := n) hB2 (fun i => (⟨dN i, hd_lt i⟩ : Fin B))
  funext i
  simp only [decode]
  rw [hdigits]
  rw [getD_ofFn (fun i : Fin n => dN i) i 0]
  have hZi : (a' i : ℤ) + (M : ℤ) = (a i : ℤ) + (dN i : ℤ) := by
    have h := hcoord i
    exact_mod_cast h
  linarith

end Qatlib.Papers.QLattice03.MainResults.Reduction
