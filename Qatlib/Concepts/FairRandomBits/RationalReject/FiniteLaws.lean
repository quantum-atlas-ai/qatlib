/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.RationalReject.RationalRejectionSampling
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Dyadic sampling from rational cumulative laws

`RationalCDF` stores a monotone rational cumulative distribution with endpoints zero and one.
Flooring its scaled cumulative values defines `bucketWeight`, whose total is exactly `2 ^ b`, so
`sampleCounted` decodes every `b`-bit input without rejection.

The module relates the resulting dyadic output masses to the input increments and proves
pointwise and total variation error bounds, together with pathwise bit and comparison counts.
Finite probability laws and randomized computation provide the background
[KitaevShenVyalyi2002].

## Main statements

* `sampleCounted_no_rejection`: every bit register decodes to a label.
* `sampleProgram_paths`: each supported path uses exactly `b` bits and at most `N` comparisons.
* `categorical_total_variation_bound`: the total variation error is at most `N / 2 ^ b`.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

open scoped BigOperators ENNReal
open Qatlib

namespace Qatlib.Concepts.FairRandomBits.RationalReject.DyadicCategoricalSampling

/-- A monotone rational cumulative distribution on `N` labels, with initial value zero and final
value one. -/
structure RationalCDF (N : ℕ) where
  value : Fin (N + 1) → ℚ
  monotone_value : Monotone value
  first : value 0 = 0
  last : value (Fin.last N) = 1

variable {N : ℕ}

/-- Normalize nonnegative rational weights with positive total mass to construct a rational
cumulative distribution. -/
def ofWeights (w : Fin N → ℚ) (hw : ∀ j, 0 ≤ w j) (htotal : 0 < ∑ j, w j) :
    RationalCDF N where
  value j := (∑ i ∈ Finset.univ.filter (fun i : Fin N => i.val < j.val), w i) / ∑ i, w i
  monotone_value := by
    intro j k hjk
    apply div_le_div_of_nonneg_right _ htotal.le
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact lt_of_lt_of_le hi hjk
    · intro i _ _
      exact hw i
  first := by simp
  last := by
    have hf : Finset.univ.filter (fun i : Fin N => i.val < N) = Finset.univ := by
      ext i
      simp
    simp only [Fin.val_last, hf]
    exact div_self htotal.ne'

/-- Extend the cumulative distribution to natural-number cutoffs by clamping the cutoff at `N`. -/
def cumulative (C : RationalCDF N) (j : ℕ) : ℚ :=
  C.value ⟨min j N, Nat.lt_succ_of_le (Nat.min_le_right j N)⟩

/-- The clamped cumulative distribution is monotone. -/
theorem cumulative_mono (C : RationalCDF N) : Monotone (cumulative C) := by
  intro i j hij
  exact C.monotone_value (min_le_min_right N hij)

/-- The clamped cumulative distribution has value zero at cutoff zero. -/
@[simp] theorem cumulative_zero (C : RationalCDF N) : cumulative C 0 = 0 := by
  simpa [cumulative] using C.first

/-- The clamped cumulative distribution has value one at cutoff `N`. -/
@[simp] theorem cumulative_last (C : RationalCDF N) : cumulative C N = 1 := by
  simpa [cumulative, Fin.last] using C.last

/-- Every clamped cumulative value is nonnegative. -/
theorem cumulative_nonneg (C : RationalCDF N) (j : ℕ) : 0 ≤ cumulative C j := by
  simpa using cumulative_mono C (Nat.zero_le j)

/-- The natural-number floor of the cumulative probability scaled by `2 ^ b`. -/
def cutoff (C : RationalCDF N) (b j : ℕ) : ℕ :=
  ⌊(2 ^ b : ℚ) * cumulative C j⌋₊

/-- The dyadic integer cutoff is monotone in the label cutoff. -/
theorem cutoff_mono (C : RationalCDF N) (b : ℕ) : Monotone (cutoff C b) := by
  intro i j hij
  exact Nat.floor_mono (mul_le_mul_of_nonneg_left (cumulative_mono C hij) (by positivity))

/-- The initial dyadic integer cutoff is zero. -/
@[simp] theorem cutoff_zero (C : RationalCDF N) (b : ℕ) : cutoff C b 0 = 0 := by
  simp [cutoff]

/-- The final dyadic integer cutoff is `2 ^ b`. -/
@[simp] theorem cutoff_last (C : RationalCDF N) (b : ℕ) : cutoff C b N = 2 ^ b := by
  unfold cutoff
  rw [cumulative_last, mul_one]
  have hc : (2 ^ b : ℚ) = ((2 ^ b : ℕ) : ℚ) := by norm_cast
  rw [hc, Nat.floor_natCast]

/-- The natural-number width between consecutive dyadic cutoffs for label `j`. -/
def bucketWeight (C : RationalCDF N) (b : ℕ) (j : Fin N) : ℕ :=
  cutoff C b (j.val + 1) - cutoff C b j.val

/-- The dyadic bucket weights sum to exactly `2 ^ b`. -/
theorem bucketWeight_total (C : RationalCDF N) (b : ℕ) :
    Qatlib.Concepts.FairRandomBits.RationalReject.weightTotal (bucketWeight C b) = 2 ^ b := by
  unfold Qatlib.Concepts.FairRandomBits.RationalReject.weightTotal bucketWeight
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => cutoff C b (j + 1) - cutoff C b j) N,
    Finset.sum_range_tsub (cutoff_mono C b)]
  simp

/-- The sum of dyadic bucket weights below `k ≤ N` equals the dyadic cutoff at `k`. -/
private theorem prefix_sum (C : RationalCDF N) (b k : ℕ) (hk : k ≤ N) :
    (∑ j ∈ Finset.univ.filter (fun j : Fin N => j.val < k), bucketWeight C b j) =
      cutoff C b k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkN : k < N := by omega
    let j : Fin N := ⟨k, hkN⟩
    have hs : Finset.univ.filter (fun i : Fin N => i.val < k + 1) =
        insert j (Finset.univ.filter (fun i : Fin N => i.val < k)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        by_cases he : i.val = k
        · exact Or.inl (Fin.ext he)
        · exact Or.inr (by omega)
      · rintro (rfl | h)
        · exact Nat.lt_succ_self k
        · omega
    have hj : j ∉ Finset.univ.filter (fun i : Fin N => i.val < k) := by simp [j]
    rw [hs, Finset.sum_insert hj, ih (by omega)]
    change cutoff C b (k + 1) - cutoff C b k + cutoff C b k = cutoff C b (k + 1)
    exact Nat.sub_add_cancel (cutoff_mono C b (Nat.le_succ k))

/-- The prefix weight of a label's dyadic bucket equals its lower dyadic cutoff. -/
theorem bucketWeight_prefix (C : RationalCDF N) (b : ℕ) (j : Fin N) :
    Qatlib.Concepts.FairRandomBits.RationalReject.weightPrefix (bucketWeight C b) j = cutoff C b j.val :=
  prefix_sum C b j.val (Nat.le_of_lt j.isLt)

/-- Decode a bit register using the dyadic bucket weights, returning an optional label and the
comparison count. -/
def sampleCounted (C : RationalCDF N) (b : ℕ) (bits : Qatlib.Foundations.PureStateMath.Reg b) : Option (Fin N) × ℕ :=
  Qatlib.Concepts.FairRandomBits.RationalReject.weightDecodeCounted (bucketWeight C b) (Qatlib.Foundations.PureStateMath.bitVecEquiv b bits).val

/-- The dyadic cumulative sampler returns a label on every bit register. -/
theorem sampleCounted_no_rejection (C : RationalCDF N) (b : ℕ) (bits : Qatlib.Foundations.PureStateMath.Reg b) :
    (sampleCounted C b bits).1 ≠ none := by
  intro h
  have hu :=
      (Qatlib.Concepts.FairRandomBits.RationalReject.weightDecodeCounted_none_iff (bucketWeight C b) (Qatlib.Foundations.PureStateMath.bitVecEquiv b bits).val).mp h
  rw [bucketWeight_total] at hu
  exact (Nat.not_le_of_lt (Qatlib.Foundations.PureStateMath.bitVecEquiv b bits).isLt) hu

/-- The sampler returns `j` exactly when the encoded integer lies between the consecutive dyadic
cutoffs of `j`. -/
theorem sampleCounted_interval (C : RationalCDF N) (b : ℕ) (bits : Qatlib.Foundations.PureStateMath.Reg b) (j : Fin N) :
    (sampleCounted C b bits).1 = some j ↔
      cutoff C b j.val ≤ (Qatlib.Foundations.PureStateMath.bitVecEquiv b bits).val ∧
        (Qatlib.Foundations.PureStateMath.bitVecEquiv b bits).val < cutoff C b (j.val + 1) := by
  rw [sampleCounted, Qatlib.Concepts.FairRandomBits.RationalReject.weightDecodeCounted_some_iff,
      bucketWeight_prefix]
  rw [bucketWeight, Nat.add_sub_of_le (cutoff_mono C b (Nat.le_succ j.val))]

/-- The sampler uses at most `N` comparisons and exactly `j.val + 1` comparisons when it returns
`j`. -/
theorem sampleCounted_comparisons (C : RationalCDF N) (b : ℕ) (bits : Qatlib.Foundations.PureStateMath.Reg b) :
    (sampleCounted C b bits).2 ≤ N ∧
      ∀ j, (sampleCounted C b bits).1 = some j →
        (sampleCounted C b bits).2 = j.val + 1 := by
  exact ⟨(Qatlib.Concepts.FairRandomBits.RationalReject.weightDecodeCounted_bounds _ _).1,
      (Qatlib.Concepts.FairRandomBits.RationalReject.weightDecodeCounted_bounds _ _).2.2⟩

/-- Generate `b` fair bits and return their counted dyadic decoding while retaining the bit
cost. -/
noncomputable def sampleProgram (C : RationalCDF N) (b : ℕ) :
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw (Option (Fin N) × ℕ) :=
  (Qatlib.Concepts.FairRandomBits.FiniteCoinExecution.fairBitsCosted b).map (fun bc => (sampleCounted C b bc.1, bc.2))

/-- Every supported sampling path returns a label, uses at most `N` comparisons, and consumes
exactly `b` bits. -/
theorem sampleProgram_paths (C : RationalCDF N) (b : ℕ)
    (z : (Option (Fin N) × ℕ) × ℕ) (hz : z ∈ (sampleProgram C b).support) :
    z.1.1 ≠ none ∧ z.1.2 ≤ N ∧ z.2 = b := by
  obtain ⟨bc, hbc, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
  have hc : bc.2 = b := by
    by_contra hne
    have hzero : Qatlib.Concepts.FairRandomBits.FiniteCoinExecution.fairBitsCosted b bc = 0 := by
      change Qatlib.Concepts.FairRandomBits.FiniteCoinExecution.fairBitsCosted b (bc.1, bc.2) = 0
      rw [Qatlib.Concepts.FairRandomBits.FiniteCoinExecution.fair_bit_program_joint_distribution,
          if_neg hne]
    exact ((PMF.mem_support_iff _ _).mp hbc) hzero
  exact ⟨sampleCounted_no_rejection C b bc.1, (sampleCounted_comparisons C b bc.1).1, hc⟩

/-- The number of bit registers decoded to label `j` equals its dyadic bucket weight. -/
theorem sampleCounted_fiber (C : RationalCDF N) (b : ℕ) (j : Fin N) :
    (Finset.univ.filter (fun bits : Qatlib.Foundations.PureStateMath.Reg b => (sampleCounted C b bits).1 = some j)).card =
      bucketWeight C b j :=
  (Qatlib.Concepts.FairRandomBits.RationalReject.rational_fair_bit_step_distribution N (bucketWeight C b) b
    (le_of_eq (bucketWeight_total C b))).1 j

/-- The one-step rejection kernel for the dyadic weights assigns label `j` mass `bucketWeight C
b j / 2 ^ b`. -/
theorem fair_bit_output_mass (C : RationalCDF N) (b : ℕ) (j : Fin N) :
    Qatlib.Concepts.FairRandomBits.RationalReject.rationalRejectionNext (bucketWeight C b) b () (Sum.inl j) =
      (bucketWeight C b j : ℝ≥0∞) / (2 ^ b : ℝ≥0∞) := by
  simpa using (Qatlib.Concepts.FairRandomBits.RationalReject.rational_fair_bit_step_distribution N (bucketWeight C b) b
    (le_of_eq (bucketWeight_total C b))).2.2.1 j

/-- The rational input probability of label `j`, given by its cumulative increment. -/
def inputMass (C : RationalCDF N) (j : Fin N) : ℚ :=
  cumulative C (j.val + 1) - cumulative C j.val

/-- The rational dyadic output probability of label `j`, given by its bucket width divided by `2
^ b`. -/
def outputMass (C : RationalCDF N) (b : ℕ) (j : Fin N) : ℚ :=
  (bucketWeight C b j : ℚ) / (2 ^ b : ℚ)

/-- Every input cumulative increment is nonnegative. -/
theorem inputMass_nonneg (C : RationalCDF N) (j : Fin N) : 0 ≤ inputMass C j :=
  sub_nonneg.mpr (cumulative_mono C (Nat.le_succ j.val))

/-- The input cumulative increments sum to one. -/
theorem inputMass_sum (C : RationalCDF N) : ∑ j : Fin N, inputMass C j = 1 := by
  unfold inputMass
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => cumulative C (j + 1) - cumulative C j) N,
    Finset.sum_range_sub]
  simp

/-- Every dyadic output mass is nonnegative. -/
theorem outputMass_nonneg (C : RationalCDF N) (b : ℕ) (j : Fin N) :
    0 ≤ outputMass C b j := by
  unfold outputMass
  positivity

/-- The dyadic output masses sum to one. -/
theorem outputMass_sum (C : RationalCDF N) (b : ℕ) :
    ∑ j : Fin N, outputMass C b j = 1 := by
  unfold outputMass
  rw [← Finset.sum_div, ← Nat.cast_sum]
  change (Qatlib.Concepts.FairRandomBits.RationalReject.weightTotal (bucketWeight C b) : ℚ) /
      (2 ^ b : ℚ) = 1
  rw [bucketWeight_total]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  exact div_self (by positivity : (2 ^ b : ℚ) ≠ 0)

/-- The absolute difference between each output mass and its input mass is at most `2 / 2 ^ b`. -/
theorem outputMass_error (C : RationalCDF N) (b : ℕ) (j : Fin N) :
    |outputMass C b j - inputMass C j| ≤ 2 / (2 ^ b : ℚ) := by
  have hd : (0 : ℚ) < 2 ^ b := by positivity
  have hlo := Nat.floor_le (mul_nonneg hd.le (cumulative_nonneg C j.val))
  have hhi := Nat.floor_le (mul_nonneg hd.le (cumulative_nonneg C (j.val + 1)))
  have hlo' := Nat.lt_floor_add_one ((2 ^ b : ℚ) * cumulative C j.val)
  have hhi' := Nat.lt_floor_add_one ((2 ^ b : ℚ) * cumulative C (j.val + 1))
  change (cutoff C b j.val : ℚ) ≤ _ at hlo
  change (cutoff C b (j.val + 1) : ℚ) ≤ _ at hhi
  change _ < (cutoff C b j.val : ℚ) + 1 at hlo'
  change _ < (cutoff C b (j.val + 1) : ℚ) + 1 at hhi'
  have hid : outputMass C b j - inputMass C j =
      (((cutoff C b (j.val + 1) : ℚ) - (2 ^ b : ℚ) * cumulative C (j.val + 1)) -
        ((cutoff C b j.val : ℚ) - (2 ^ b : ℚ) * cumulative C j.val)) / (2 ^ b : ℚ) := by
    unfold outputMass inputMass bucketWeight
    rw [Nat.cast_sub (cutoff_mono C b (Nat.le_succ j.val))]
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hd]
  apply (div_le_div_iff_of_pos_right hd).2
  rw [abs_le]
  constructor <;> linarith

/-- The total variation distance between the dyadic output masses and the input masses is at
most `N / 2 ^ b`. -/
theorem categorical_total_variation_bound (C : RationalCDF N) (b : ℕ) :
    (∑ j : Fin N, |outputMass C b j - inputMass C j|) / 2 ≤
      (N : ℚ) / (2 ^ b : ℚ) := by
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => outputMass_error C b j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  calc
    _ ≤ ((N : ℚ) * (2 / (2 ^ b : ℚ))) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by ring

end Qatlib.Concepts.FairRandomBits.RationalReject.DyadicCategoricalSampling
