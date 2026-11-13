/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Fin
import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Reduction of Boolean quadratic systems over `𝔽₂` to complex polynomial systems

This file formalizes Lemma 3.3 of [Ding et al., 2021][DingEtAl2021] (pp. 4–5, Eqs. (3)–(8)),
giving the polynomial-time bijection between solutions of a Boolean polynomial system over `𝔽₂`
(Problem 3.1) and solutions of the reduced complex polynomial system (Problem 3.2) in
`n + m · ⌊log₂ #F⌋` variables and `n + m · (⌊log₂ #F⌋ + 1)` equations.

For each polynomial `i`, the integer lift `fᵢ(x)` is expanded in binary with exponents `b + 1`
(`fᵢ(x) = ∑_{b=0}^{K-1} 2^{b+1} y_{i,b}` with Boolean carry bits `y_{i,b} ∈ {0, 1}`), encoding
evenness `2 ∣ fᵢ(x)`.

## Main statements

* `ReducedSystemSol`: the constructed complex system (Eqs. (6)–(8)).
* `lemma33_sound`: every solution of the reduced system assigns `{0, 1}` values to `x` and
  makes every integer lift `fᵢ(x)` even.
* `lemma33_binaryRep_exists`: every even integer in `[0, 2^K)` admits a `K`-bit representation
  with exponents `1 .. K`.
* `lemma33_reduction`: bidirectional solution equivalence between Problem 3.1 and Eqs. (6)–(8)
  (Lemma 3.3).
* `lemma33_equationCount`: equation count `m + m · K + n = n + m · (K + 1)`.

## References

* [Ding et al., 2021][DingEtAl2021]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma33

open Qatlib.Papers.MacaulayHHL21.MainResults

/-- The Boolean part of a complex assignment `x`, read as an element of `𝔽₂ⁿ`. -/
noncomputable def BoolVal {n : ℕ} (x : Fin n → ℂ) : Fin n → ZMod 2 := by
  classical
  exact fun j => if x j = 0 then 0 else 1

/-- The constructed complex system (Eqs. (6)–(8)): `x` is `{0, 1}`-valued, and for each `i` the
integer lift `f i` is represented by the binary digits `y i b` with exponents `b + 1`. -/
def ReducedSystemSol {n m K : ℕ} (f : (Fin n → ZMod 2) → Fin m → ℤ)
    (x : Fin n → ℂ) (y : Fin m → Fin K → ℤ) : Prop :=
  IsZeroOne x ∧
    ∀ i, (∀ b, y i b = 0 ∨ y i b = 1) ∧
      f (BoolVal x) i = ∑ b : Fin K, (2 : ℤ) ^ ((b : ℕ) + 1) * y i b

/-- Soundness of the reduction ([Ding et al., 2021][DingEtAl2021], Lemma 3.3, pp. 4–5): any
solution of Eqs. (6)–(8) has Boolean `x` and makes every integer lift `fᵢ(x)` divisible by `2`. -/
theorem lemma33_sound {n m K : ℕ} (f : (Fin n → ZMod 2) → Fin m → ℤ)
    {x : Fin n → ℂ} {y : Fin m → Fin K → ℤ} (h : ReducedSystemSol f x y) :
    IsZeroOne x ∧ ∀ i, (2 : ℤ) ∣ f (BoolVal x) i := by
  obtain ⟨hx, hy⟩ := h
  refine ⟨hx, fun i => ?_⟩
  obtain ⟨_, heq⟩ := hy i
  refine ⟨∑ b : Fin K, (2 : ℤ) ^ (b : ℕ) * y i b, ?_⟩
  rw [heq, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro b _
  rw [pow_succ]
  ring

/-- Binary expansion of an even integer in `[0, 2^K)` into `K` bits with exponents `1 .. K`. -/
theorem lemma33_binaryRep_exists {K : ℕ} {z : ℤ}
    (hz0 : 0 ≤ z) (hz : z < 2 ^ K) (heven : (2 : ℤ) ∣ z) :
    ∃ y : Fin K → ℤ, (∀ b, y b = 0 ∨ y b = 1) ∧
      z = ∑ b : Fin K, (2 : ℤ) ^ ((b : ℕ) + 1) * y b := by
  induction K generalizing z with
  | zero =>
    have hz_eq : z = 0 := by
      simp only [pow_zero] at hz
      omega
    refine ⟨fun b => b.elim0, fun b => b.elim0, ?_⟩
    simp [hz_eq]
  | succ K ih =>
    obtain ⟨m, rfl⟩ := heven
    have hm0 : 0 ≤ m := by omega
    have hm_lt : m < 2 ^ K := by
      have hpow : (2 : ℤ) ^ (K + 1) = 2 * 2 ^ K := by ring
      linarith
    let r : ℤ := m % 2
    let q : ℤ := m / 2
    have hm_decomp : m = r + 2 * q := by omega
    have hr_bit : r = 0 ∨ r = 1 := by omega
    have h2q0 : 0 ≤ 2 * q := by omega
    have h2q_lt : 2 * q < 2 ^ K := by omega
    have h2q_even : (2 : ℤ) ∣ 2 * q := ⟨q, rfl⟩
    obtain ⟨y', hy'_bits, hy'_sum⟩ := ih h2q0 h2q_lt h2q_even
    refine ⟨Fin.cons r y', ?_, ?_⟩
    · intro b
      refine Fin.cases ?_ ?_ b
      · simpa using hr_bit
      · intro i
        simpa using hy'_bits i
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, zero_add, pow_one, Fin.cons_zero, Fin.val_succ, Fin.cons_succ]
      have htail : (∑ x : Fin K, (2 : ℤ) ^ ((x : ℕ) + 1 + 1) * y' x) =
          2 * ∑ x : Fin K, (2 : ℤ) ^ ((x : ℕ) + 1) * y' x := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [pow_succ']
        ring
      rw [htail, ← hy'_sum]
      linarith

/-- **Lemma 3.3** ([Ding et al., 2021][DingEtAl2021], pp. 4–5): the reduction (3)–(8) establishes
equivalence between Boolean solutions of Problem 3.1 and solutions of the complex system (6)–(8)
in `n + m · K` variables and `n + m · (K + 1)` equations. -/
theorem lemma33_reduction {n m K : ℕ} (f : (Fin n → ZMod 2) → Fin m → ℤ)
    (hrange : ∀ (x : Fin n → ℂ), IsZeroOne x → ∀ i,
      0 ≤ f (BoolVal x) i ∧ f (BoolVal x) i < 2 ^ K) :
    (∀ (x : Fin n → ℂ) (y : Fin m → Fin K → ℤ),
        ReducedSystemSol f x y → IsZeroOne x ∧ ∀ i, (2 : ℤ) ∣ f (BoolVal x) i) ∧
    (∀ x, IsZeroOne x → (∀ i, (2 : ℤ) ∣ f (BoolVal x) i) →
        ∃ y : Fin m → Fin K → ℤ, ReducedSystemSol f x y) := by
  constructor
  · intro x y h
    exact lemma33_sound f h
  · intro x hx hdvd
    have hex : ∀ i, ∃ y : Fin K → ℤ, (∀ b, y b = 0 ∨ y b = 1) ∧
        f (BoolVal x) i = ∑ b : Fin K, (2 : ℤ) ^ ((b : ℕ) + 1) * y b :=
      fun i => lemma33_binaryRep_exists (hrange x hx i).1 (hrange x hx i).2 (hdvd i)
    refine ⟨fun i => (hex i).choose, hx, fun i => ?_⟩
    exact ⟨((hex i).choose_spec).1, ((hex i).choose_spec).2⟩

/-- Equation count of Lemma 3.3: `m` equations (6), `m · K` equations (7), and `n` equations (8)
amount to `n + m · (K + 1)`. -/
theorem lemma33_equationCount (n m K : ℕ) : m + m * K + n = n + m * (K + 1) := by
  ring

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma33
