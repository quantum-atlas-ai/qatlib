/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.SignedClock.ClockSpectral

/-!
# Clock weights and scaled integer entries

The function `wPlus` records the corrected clock weight as an affine function of an acceptance
parameter. Its bounds separate the parameters at most `1 / 3` from those at least `2 / 3` in the
signed-clock analysis of [JanzingWocjan2006].

The predicate `InScaledInt` tracks a common real scale for integer matrix entries. Closure under
products and powers gives the corresponding scale for repeated gate products.

## Main statements

* `wPlus_lower` and `wPlus_upper`: explicit separated bounds on the corrected clock weight.
* `inScaledInt_mul`: matrix multiplication multiplies the entry scales.
* `gateProduct_scaled`: powers of a matrix scaled by `1 / √2` have the expected power scale.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.SignedClock

open Finset Matrix

/-- The real number `√2` is positive. -/
theorem sqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)

/-- The affine clock weight `(1 + (1 - 2 * p) / √2) / 2`. -/
def wPlus (p : ℝ) : ℝ := (1 + (1 - 2 * p) / Real.sqrt 2) / 2

/-- If `p ≤ 1 / 3`, then `wPlus p` is at least `(1 + 1 / (3 * √2)) / 2` [JanzingWocjan2006]. -/
theorem wPlus_lower {p : ℝ} (hp : p ≤ 1 / 3) :
    (1 + 1 / (3 * Real.sqrt 2)) / 2 ≤ wPlus p := by
  have hs := sqrt2_pos
  have h1 : (1 : ℝ) / 3 ≤ 1 - 2 * p := by linarith
  have h2 : (1 / 3) / Real.sqrt 2 ≤ (1 - 2 * p) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right h1 (le_of_lt hs)
  have h3 : (1 / 3) / Real.sqrt 2 = 1 / (3 * Real.sqrt 2) := by
    field_simp
  unfold wPlus
  rw [← h3]
  linarith

/-- If `p ≥ 2 / 3`, then `wPlus p` is at most `(1 - 1 / (3 * √2)) / 2` [JanzingWocjan2006]. -/
theorem wPlus_upper {p : ℝ} (hp : 2 / 3 ≤ p) :
    wPlus p ≤ (1 - 1 / (3 * Real.sqrt 2)) / 2 := by
  have hs := sqrt2_pos
  have h1 : 1 - 2 * p ≤ -(1 / 3 : ℝ) := by linarith
  have h2 : (1 - 2 * p) / Real.sqrt 2 ≤ (-(1 / 3)) / Real.sqrt 2 :=
    div_le_div_of_nonneg_right h1 (le_of_lt hs)
  have h3 : (-(1 / 3)) / Real.sqrt 2 = -(1 / (3 * Real.sqrt 2)) := by
    field_simp
  unfold wPlus
  rw [h3] at h2
  linarith

/-- The property that every entry of `A` is an integer multiple of the common real scale `s`. -/
def InScaledInt {N : ℕ} (s : ℝ) (A : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, ∃ k : ℤ, A i j = (k : ℝ) * s

/-- The identity matrix has integer entries with common scale one. -/
theorem inScaledInt_one {N : ℕ} :
    InScaledInt (1 : ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) := by
  intro i j
  refine ⟨if i = j then 1 else 0, ?_⟩
  rw [Matrix.one_apply]
  split_ifs <;> simp

/-- If the entries of `A` and `B` are integer multiples of `s` and `t`, respectively, the
entries of their product are integer multiples of `s * t`. -/
theorem inScaledInt_mul {N : ℕ} {s t : ℝ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt s A) (hB : InScaledInt t B) :
    InScaledInt (s * t) (A * B) := by
  classical
  intro i j
  choose a ha using hA
  choose b hb using hB
  have hterm : ∀ l : Fin N,
      A i l * B l j = (((a i l) * (b l j) : ℤ) : ℝ) * (s * t) := by
    intro l
    rw [ha i l, hb l j]
    push_cast
    ring
  refine ⟨∑ l, a i l * b l j, ?_⟩
  calc (A * B) i j = ∑ l, A i l * B l j := by rw [Matrix.mul_apply]
    _ = ∑ l, (((a i l) * (b l j) : ℤ) : ℝ) * (s * t) :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = (∑ l, (((a i l) * (b l j) : ℤ) : ℝ)) * (s * t) := by rw [Finset.sum_mul]
    _ = (((∑ l, a i l * b l j) : ℤ) : ℝ) * (s * t) := by rw [Int.cast_sum]

/-- If the entries of `A` are integer multiples of `s`, the entries of `A ^ m` are integer
multiples of `s ^ m` [JanzingWocjan2006]. -/
theorem inScaledInt_pow {N : ℕ} {s : ℝ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt s A) (m : ℕ) : InScaledInt (s ^ m) (A ^ m) := by
  induction m with
  | zero => simpa using (inScaledInt_one (N := N))
  | succ m ih =>
      rw [pow_succ, pow_succ]
      exact inScaledInt_mul ih hA

/-- A matrix whose entries are integer multiples of `1 / √2` has its `M`th power scaled by `(1 /
√2) ^ M` [JanzingWocjan2006]. -/
theorem gateProduct_scaled {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : InScaledInt ((Real.sqrt 2)⁻¹) A) (M : ℕ) :
    InScaledInt (((Real.sqrt 2)⁻¹) ^ M) (A ^ M) :=
  inScaledInt_pow hA M

end Qatlib.Papers.BQPMixSparse06.SignedClock
