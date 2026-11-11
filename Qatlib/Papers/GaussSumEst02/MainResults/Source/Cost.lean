/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polylogarithmic costs for phase estimation

This module defines the bit-length scale `bitLength`, the uniform cost predicate `PolyLog`, and
the precision factor `sampleCount`. Closure lemmas combine these costs, while `timeBound`
packages the precision and input-size factors used by the phase-estimation statements. See
[VanDamSeroussi2002].

## Main statements

* `polyLog_add`: The pointwise sum of two polylogarithmic costs is polylogarithmic.
* `polyLog_mul_bitLength`: Multiplying a polylogarithmic cost by `bitLength` preserves
  `PolyLog`.
* `sampleCount_third_le`: For positive precision, replacing `ε` by `ε/3` increases `sampleCount`
  by at most a factor of three.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- The binary logarithmic size scale `Nat.log 2 n + 1`, including at zero. -/
def bitLength (n : ℕ) : ℕ := Nat.log 2 n + 1

/-- A natural-valued cost is bounded at every input by a positive constant times a positive
integer power of `bitLength`. -/
def PolyLog (f : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, 0 < c ∧ 0 < d ∧ ∀ n : ℕ, f n ≤ c * (bitLength n) ^ d

/-- The bit-length scale is at least one at every natural input. -/
lemma one_le_bitLength (n : ℕ) : 1 ≤ bitLength n := by
  unfold bitLength
  omega

/-- Every positive constant natural-valued cost satisfies `PolyLog`. -/
theorem polyLog_const (c : ℕ) (hc : 0 < c) : PolyLog (fun _ => c) := by
  refine ⟨c, 1, hc, by norm_num, ?_⟩
  intro n
  have h : 1 ≤ bitLength n := one_le_bitLength n
  simpa using Nat.mul_le_mul_left c h

/-- The pointwise sum of two polylogarithmic costs is polylogarithmic. -/
theorem polyLog_add {f g : ℕ → ℕ} (hf : PolyLog f) (hg : PolyLog g) :
    PolyLog (fun n => f n + g n) := by
  obtain ⟨c₁, d₁, hc₁, hd₁, h₁⟩ := hf
  obtain ⟨c₂, d₂, hc₂, hd₂, h₂⟩ := hg
  refine ⟨c₁ + c₂, max d₁ d₂, by omega, lt_of_lt_of_le hd₁ (le_max_left _ _), ?_⟩
  intro n
  have hl : 1 ≤ bitLength n := one_le_bitLength n
  have hd₁' : d₁ ≤ max d₁ d₂ := le_max_left _ _
  have hd₂' : d₂ ≤ max d₁ d₂ := le_max_right _ _
  calc f n + g n
      ≤ c₁ * bitLength n ^ d₁ + c₂ * bitLength n ^ d₂ := Nat.add_le_add (h₁ n) (h₂ n)
    _ ≤ c₁ * bitLength n ^ max d₁ d₂ + c₂ * bitLength n ^ max d₁ d₂ := by
        exact Nat.add_le_add
          (Nat.mul_le_mul_left c₁ (pow_le_pow_right₀ hl hd₁'))
          (Nat.mul_le_mul_left c₂ (pow_le_pow_right₀ hl hd₂'))
    _ = (c₁ + c₂) * bitLength n ^ max d₁ d₂ := by ring

/-- Multiplication by a positive natural constant preserves `PolyLog`. -/
theorem polyLog_const_mul (c : ℕ) {f : ℕ → ℕ} (hc : 0 < c) (hf : PolyLog f) :
    PolyLog (fun n => c * f n) := by
  obtain ⟨c', d, hc', hd, h⟩ := hf
  refine ⟨c * c', d, Nat.mul_pos hc hc', hd, ?_⟩
  intro n
  rw [mul_assoc]
  exact Nat.mul_le_mul_left c (h n)

/-- Multiplying a polylogarithmic cost by `bitLength` preserves `PolyLog`. -/
theorem polyLog_mul_bitLength {f : ℕ → ℕ} (hf : PolyLog f) :
    PolyLog (fun n => bitLength n * f n) := by
  obtain ⟨c, d, hc, hd, h⟩ := hf
  refine ⟨c, d + 1, hc, by omega, ?_⟩
  intro n
  calc bitLength n * f n
      ≤ bitLength n * (c * bitLength n ^ d) := Nat.mul_le_mul_left _ (h n)
    _ = c * bitLength n ^ (d + 1) := by ring

/-- The natural ceiling of the reciprocal precision `1 / ε`. -/
def sampleCount (ε : ℝ) : ℕ := Nat.ceil (1 / ε)

/-- For positive precision, replacing `ε` by `ε/3` increases `sampleCount` by at most a factor
of three. -/
lemma sampleCount_third_le (ε : ℝ) (hε : 0 < ε) :
    sampleCount (ε / 3) ≤ 3 * sampleCount ε := by
  have hε0 : ε ≠ 0 := hε.ne'
  have h1 : 1 / ε ≤ (Nat.ceil (1 / ε) : ℝ) := Nat.le_ceil (1 / ε)
  have hthird : 1 / (ε / 3) = 3 * (1 / ε) := by
    field_simp [hε0]
  calc sampleCount (ε / 3) = Nat.ceil (1 / (ε / 3)) := rfl
    _ = Nat.ceil (3 * (1 / ε)) := by rw [hthird]
    _ ≤ 3 * Nat.ceil (1 / ε) := by
        rw [Nat.ceil_le]
        push_cast
        nlinarith [h1]
    _ = 3 * sampleCount ε := rfl

/-- The product of `sampleCount ε` and the bit-length cost `c * bitLength n ^ d`. -/
def timeBound (c d : ℕ) (ε : ℝ) (n : ℕ) : ℕ := sampleCount ε * (c * bitLength n ^ d)

/-- The product of the precision factor and bit-length cost equals `timeBound`. -/
theorem timeBound_le (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (ε : ℝ) (n : ℕ) :
    sampleCount ε * (c * bitLength n ^ d) = timeBound c d ε n := rfl

end Qatlib.Papers.GaussSumEst02.MainResults.Source
