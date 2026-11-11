/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CorrWalkSim16.MainResults.CoeffFunctional

set_option backward.isDefEq.respectTransparency false

/-!
# CorrWalkSim16, Lemma 3: parity symmetry of the walk coefficients

Berry--Novo, arXiv:1606.03443v3, Lemma 3 and Eq. (64) on PDF pp. 10-11.

At every stage of Algorithms 1 and 2 the implemented operation is a sum
`∑ n, c n • U^n` of powers of the walk step whose coefficients obey

  `c (-n) = (-1)^n * c n`.

The paper derives this from the Bessel identity `J_{-m}(z) = (-1)^m J_m(z)` for
`V` and `Ṽ`, and observes that the property survives sums, products (Eq. (64))
and truncation of higher powers.

This file formalizes

* `walkSymmetric_signedExtension`: the `m ↦ (-1)^m`-signed extension of a
  sequence indexed by `ℕ` is symmetric (the Bessel input of the paper);
* `walkSymmetric_add`, `walkSymmetric_smul`, `walkSymmetric_coeffTrunc`: sums,
  scalar multiples and truncations preserve the symmetry;
* `walkSymmetric_coeffMul`: products preserve the symmetry, which is the
  substitution `m ↦ -m`, `n ↦ -n` of Eq. (64).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.CorrWalkSim16.MainResults

open scoped BigOperators

/-- `(-1)^k` is its own inverse as a complex number. -/
theorem neg_one_zpow_mul_self (k : ℤ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← mul_zpow]
  simp

/-- `(-1)^k` is its own inverse, so it only depends on `|k|`. -/
theorem neg_one_zpow_eq_natAbs (k : ℤ) : (-1 : ℂ) ^ k = (-1 : ℂ) ^ k.natAbs := by
  have hself : (-1 : ℂ) ^ k = ((-1 : ℂ) ^ k)⁻¹ :=
    (inv_eq_of_mul_eq_one_right (neg_one_zpow_mul_self k)).symm
  by_cases h : 0 ≤ k
  · rw [← zpow_natCast, Int.natAbs_of_nonneg h]
  · have hk : ((k.natAbs : ℕ) : ℤ) = -k := by
      rw [← Int.natAbs_neg k]
      exact Int.natAbs_of_nonneg (by omega)
    rw [← zpow_natCast, hk, zpow_neg]
    exact hself

/-- For `m ≥ 0` the powers `(-1)^{|m|}` and `(-1)^m` agree. -/
theorem neg_one_pow_natAbs {m : ℤ} (h : 0 ≤ m) :
    (-1 : ℂ) ^ m.natAbs = (-1 : ℂ) ^ m := by
  rw [← zpow_natCast, Int.natAbs_of_nonneg h]

/-- For `m < 0` the product `(-1)^m (-1)^{|m|}` is one. -/
theorem neg_one_zpow_mul_pow_natAbs {m : ℤ} (h : m < 0) :
    (-1 : ℂ) ^ m * (-1 : ℂ) ^ m.natAbs = 1 := by
  have hcast : ((m.natAbs : ℕ) : ℤ) = -m := by
    rw [← Int.natAbs_neg m]
    exact Int.natAbs_of_nonneg (by omega)
  rw [← zpow_natCast, hcast, ← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
  rw [show m + -m = 0 by ring, zpow_zero]

/-- The symmetry of Lemma 3: `c (-n) = (-1)^n c n`. -/
def WalkSymmetric (c : ℤ → ℂ) : Prop := ∀ n : ℤ, c (-n) = (-1 : ℂ) ^ n * c n

/-- The signed extension of a family indexed by `ℕ`: the value at `-m` is
`(-1)^m` times the value at `m`, which is the Bessel symmetry
`J_{-m}(z) = (-1)^m J_m(z)`. -/
def signedExtension (d : ℕ → ℂ) : ℤ → ℂ :=
  fun m => if 0 ≤ m then d m.natAbs else (-1 : ℂ) ^ m.natAbs * d m.natAbs

/-- `V` and `Ṽ` are symmetric: the signed extension of the Bessel weights is
symmetric. -/
theorem walkSymmetric_signedExtension (d : ℕ → ℂ) :
    WalkSymmetric (signedExtension d) := by
  intro n
  rcases lt_trichotomy n 0 with hn | hn | hn
  · have hpos : 0 ≤ -n := by omega
    have hneg : ¬ 0 ≤ n := by omega
    have hnn : (-n).natAbs = n.natAbs := Int.natAbs_neg n
    simp only [signedExtension]
    rw [if_pos hpos, if_neg hneg, hnn, ← mul_assoc, neg_one_zpow_mul_pow_natAbs hn, one_mul]
  · subst hn
    simp [signedExtension]
  · have hneg : ¬ 0 ≤ -n := by omega
    have hpos : 0 ≤ n := le_of_lt hn
    have hnn : (-n).natAbs = n.natAbs := Int.natAbs_neg n
    simp only [signedExtension]
    rw [if_neg hneg, if_pos hpos, hnn, neg_one_pow_natAbs hpos]

/-- Sums of symmetric coefficient families are symmetric. -/
theorem walkSymmetric_add {c d : ℤ → ℂ} (hc : WalkSymmetric c) (hd : WalkSymmetric d) :
    WalkSymmetric (fun n => c n + d n) := by
  intro n
  simp only
  rw [hc n, hd n]
  ring

/-- Scalar multiples of symmetric coefficient families are symmetric. -/
theorem walkSymmetric_smul {c : ℤ → ℂ} (hc : WalkSymmetric c) (α : ℂ) :
    WalkSymmetric (fun n => α * c n) := by
  intro n
  simp only
  rw [hc n]
  ring

/-- Truncating the powers at `N`. -/
def coeffTrunc (N : ℕ) (c : ℤ → ℂ) : ℤ → ℂ := fun n => if |n| ≤ (N : ℤ) then c n else 0

/-- Truncation preserves the symmetry of Lemma 3. -/
theorem walkSymmetric_coeffTrunc (N : ℕ) {c : ℤ → ℂ} (hc : WalkSymmetric c) :
    WalkSymmetric (coeffTrunc N c) := by
  intro n
  simp only [coeffTrunc]
  rw [abs_neg]
  by_cases h : |n| ≤ (N : ℤ)
  · rw [if_pos h, if_pos h, hc n]
  · rw [if_neg h, if_neg h, mul_zero]

/-- Eq. (64): products of symmetric coefficient families are symmetric. -/
theorem walkSymmetric_coeffMul {c d : ℤ → ℂ} (hc : WalkSymmetric c) (hd : WalkSymmetric d) :
    WalkSymmetric (coeffMul c d) := by
  intro n
  simp only [coeffMul]
  have hstep : (∑' k : ℤ, c (-n - k) * d k)
      = ∑' k : ℤ, c (-n + k) * d (-k) := by
    rw [← Equiv.tsum_eq (Equiv.neg ℤ) (fun k : ℤ => c (-n - k) * d k)]
    refine tsum_congr fun k => ?_
    have hneg : (Equiv.neg ℤ) k = -k := rfl
    rw [hneg, sub_neg_eq_add]
  rw [hstep]
  have hterm : ∀ k : ℤ, c (-n + k) * d (-k) = (-1 : ℂ) ^ n * (c (n - k) * d k) := by
    intro k
    have h1 : c (-n + k) = (-1 : ℂ) ^ (n - k) * c (n - k) := by
      have harg : -n + k = -(n - k) := by ring
      rw [harg, hc]
    have h2 : d (-k) = (-1 : ℂ) ^ k * d k := hd k
    rw [h1, h2]
    have h3 : (-1 : ℂ) ^ (n - k) * (-1 : ℂ) ^ k = (-1 : ℂ) ^ n := by
      rw [← zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0)]
      congr 1
      ring
    calc (-1 : ℂ) ^ (n - k) * c (n - k) * ((-1 : ℂ) ^ k * d k)
        = ((-1 : ℂ) ^ (n - k) * (-1 : ℂ) ^ k) * (c (n - k) * d k) := by ring
      _ = (-1 : ℂ) ^ n * (c (n - k) * d k) := by rw [h3]
  calc (∑' k : ℤ, c (-n + k) * d (-k))
      = ∑' k : ℤ, (-1 : ℂ) ^ n * (c (n - k) * d k) := tsum_congr hterm
    _ = (-1 : ℂ) ^ n * ∑' k : ℤ, c (n - k) * d k := tsum_mul_left

end Qatlib.Papers.CorrWalkSim16.MainResults
