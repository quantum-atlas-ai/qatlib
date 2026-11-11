/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ProbabilityCore.DistributionAA.DegreeInfluenceBounds

/-!
# Couplings between adjacent Hamming slices

The module counts edges between adjacent Hamming slices by deleting a true coordinate or
inserting a false coordinate. Double counting yields the adjacent cardinality identity and
expectation formulas for these operations.

The resulting finite coupling identities express differences of neighboring slice means as
averages of coordinate flip differences. They provide slice probability infrastructure for
Boolean cube analysis in the polynomial query setting of [BealsEtAl2001].

## Main statements

* `cube_slice_adjacent_card_identity`: the edge count relating neighboring slice cardinalities.
* `cube_slice_delete_expect` and `cube_slice_insert_expect`: expectation transport between
  adjacent slices.
* `cube_slice_difference_down` and `cube_slice_difference_up`: differences of adjacent slice
  means.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ProbabilityCore.DistributionAA

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace Qatlib.Concepts.ProbabilityCore.DistributionAA
open scoped Classical BigOperators

/-- Flipping the same Boolean coordinate twice recovers the original input. -/
theorem cube_flip_involution {n : ℕ} (x : Fin n → Bool) (i : Fin n) : cubeFlip (cubeFlip x i) i = x := by
  ext j
  by_cases hj : j=i <;> simp [cubeFlip,hj]

/-- The involutive equivalence of Boolean inputs obtained by flipping a fixed coordinate. -/
def cubeFlipEquiv {n : ℕ} (i : Fin n) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := fun x => cubeFlip x i
  invFun := fun x => cubeFlip x i
  left_inv x := cube_flip_involution x i
  right_inv x := cube_flip_involution x i

/-- Flipping a true coordinate decreases Hamming weight by one, while flipping a false
coordinate increases it by one, expressed as an additive balance identity. -/
theorem cube_hamming_flip_balance {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    cubeHamming (cubeFlip x i)+(if x i then 1 else 0) = cubeHamming x+(if x i then 0 else 1) := by
  have hx := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => if x j then (1 : ℕ) else 0) (Finset.mem_univ i)
  have hy := Finset.sum_erase_add (Finset.univ : Finset (Fin n))
    (fun j => if cubeFlip x i j then (1 : ℕ) else 0) (Finset.mem_univ i)
  have he : (∑ j ∈ Finset.univ.erase i, if cubeFlip x i j then (1 : ℕ) else 0) =
      ∑ j ∈ Finset.univ.erase i, if x j then (1 : ℕ) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [cubeFlip,(Finset.mem_erase.1 hj).1]
  rw [he] at hy
  rw [← cube_hamming_eq_sum] at hx hy
  cases hi : x i <;> simp [cubeFlip,hi] at hy hx ⊢ <;> omega

/-- The number of false coordinates plus the Hamming weight equals the input length. -/
theorem cube_zero_count {n : ℕ} (x : Fin n → Bool) :
    (Finset.univ.filter (fun i : Fin n => x i=false)).card+cubeHamming x = n := by
  rw [cube_hamming_eq_sum]
  have he : (Finset.univ.filter (fun i : Fin n => x i=false)).card =
      ∑ i : Fin n, if x i then (0 : ℕ) else 1 := by
    calc
      _ = ∑ i : Fin n, if x i=false then (1 : ℕ) else 0 :=
        (Finset.sum_boole (R := ℕ) (fun i : Fin n => x i=false) Finset.univ).symm
      _ = _ := by apply Finset.sum_congr rfl; intro i _; cases x i <;> simp
  rw [he, ← Finset.sum_add_distrib]
  have hf (i : Fin n) : (if x i then (0 : ℕ) else 1)+(if x i then 1 else 0) = 1 := by
    cases x i <;> simp
  simp only [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- For `0 < k ≤ n`, summing a function after deleting each true bit from every input in the `k`
slice counts every input in the `k - 1` slice `n - k + 1` times. -/
theorem cube_slice_delete_double_sum (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    (∑ x : Fin n → Bool, if cubeHamming x=k then
      ∑ i : Fin n, if x i then f (cubeFlip x i) else 0 else 0) =
      (n-k+1 : ℕ)*∑ y : Fin n → Bool, if cubeHamming y=k-1 then f y else 0 := by
  have hleft : (∑ x : Fin n → Bool, if cubeHamming x=k then
      ∑ i : Fin n, if x i then f (cubeFlip x i) else 0 else 0) =
      ∑ i : Fin n, ∑ x : Fin n → Bool, if cubeHamming x=k ∧ x i=true then f (cubeFlip x i) else 0 := by
    rw [← Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : cubeHamming x=k <;> simp [hx]
  rw [hleft]
  have hmap (i : Fin n) :
      (∑ x : Fin n → Bool, if cubeHamming x=k ∧ x i=true then f (cubeFlip x i) else 0) =
        ∑ y : Fin n → Bool, if cubeHamming y=k-1 ∧ y i=false then f y else 0 := by
    rw [← Equiv.sum_comp (cubeFlipEquiv i) (fun x => if cubeHamming x=k ∧ x i=true then f (cubeFlip x i) else 0)]
    apply Finset.sum_congr rfl
    intro y _
    change (if cubeHamming (cubeFlip y i)=k ∧ cubeFlip y i i=true then f (cubeFlip (cubeFlip y i) i) else 0) = _
    have hb := cube_hamming_flip_balance y i
    cases hi : y i
    · have hbit : cubeFlip y i i=true := by simp [cubeFlip,hi]
      have hc : cubeHamming (cubeFlip y i) = cubeHamming y+1 := by simpa [hi] using hb
      have hiff : cubeHamming (cubeFlip y i)=k ↔ cubeHamming y=k-1 := by omega
      simp [hbit,hiff,cube_flip_involution]
    · have hbit : cubeFlip y i i=false := by simp [cubeFlip,hi]
      simp [hbit]
  simp_rw [hmap]
  rw [Finset.sum_comm]
  apply Eq.trans _ (by rw [Finset.mul_sum])
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : cubeHamming y=k-1
  · have hcount := cube_zero_count y
    have hc : (Finset.univ.filter (fun i : Fin n => y i=false)).card = n-k+1 := by omega
    simp [hy, Finset.sum_ite, Finset.sum_const, hc]
  · simp [hy]

/-- The sum of the real zero and one encodings of the input coordinates equals the real cast of
its Hamming weight. -/
theorem cube_hamming_cast_sum {n : ℕ} (x : Fin n → Bool) :
    (∑ i : Fin n, if x i then (1 : ℝ) else 0) = (cubeHamming x : ℝ) :=
  Finset.sum_boole (R := ℝ) _ _

/-- The Hamming `k` slice is nonempty when `k ≤ n`. -/
theorem cube_slice_card_pos (n k : ℕ) (hk : k ≤ n) :
    0 < (Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card := by
  let S := Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)
  have hw := sliceWeight_cubeWeight n k hk
  by_contra h
  have hc : S.card=0 := Nat.eq_zero_of_not_pos h
  have hz (x : Fin n → Bool) : sliceWeight n k x=0 := by
    unfold sliceWeight
    change (if cubeHamming x=k then (S.card : ℝ)⁻¹ else 0) = 0
    simp [hc]
  have hs := hw.2
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

/-- Slice expectation is the reciprocal slice cardinality times the sum of function values on
that slice. -/
theorem cube_slice_expect_uniform (n k : ℕ) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n k) f =
      ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ)⁻¹ *
        ∑ x : Fin n → Bool, if cubeHamming x=k then f x else 0 := by
  unfold cubeExpect sliceWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

/-- For `0 < k ≤ n`, the `k` slice cardinality times `k` equals the `k - 1` slice cardinality
times `n - k + 1`. -/
theorem cube_slice_adjacent_card_identity (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) :
    ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ)*(k : ℝ) =
      ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k-1)).card : ℝ)*(n-k+1 : ℕ) := by
  have he := cube_slice_delete_double_sum n k hk0 hk (fun _ => (1 : ℝ))
  simp only [cube_hamming_cast_sum] at he
  have hl : (∑ x : Fin n → Bool, if cubeHamming x=k then (cubeHamming x : ℝ) else 0) =
      (k : ℝ)*((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ) := by
    have hv (x : Fin n → Bool) : (if cubeHamming x=k then (cubeHamming x : ℝ) else 0) =
        (k : ℝ)*(if cubeHamming x=k then 1 else 0) := by split_ifs with h <;> simp [h]
    simp_rw [hv]
    rw [← Finset.mul_sum, Finset.sum_boole]
  rw [hl, Finset.sum_boole] at he
  linarith

/-- For `0 < k ≤ n`, the expected sum of function values after deleting a true bit from the `k`
slice equals `k` times its mean on the `k - 1` slice. -/
theorem cube_slice_delete_expect (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n k) (fun x => ∑ i : Fin n, if x i then f (cubeFlip x i) else 0) =
      (k : ℝ)*cubeExpect n (sliceWeight n (k-1)) f := by
  have hn : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ) ≠ 0 :=
    by exact_mod_cast (cube_slice_card_pos n k hk).ne'
  have hm : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k-1)).card : ℝ) ≠ 0 :=
    by exact_mod_cast (cube_slice_card_pos n (k-1) (by omega)).ne'
  rw [cube_slice_expect_uniform, cube_slice_expect_uniform, cube_slice_delete_double_sum n k hk0 hk]
  have he := cube_slice_adjacent_card_identity n k hk0 hk
  have hr : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ)⁻¹*(n-k+1 : ℕ) =
      (k : ℝ)*((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k-1)).card : ℝ)⁻¹ := by
    field_simp
    linarith only [he]
  rw [← mul_assoc, hr, mul_assoc]

/-- For `k > 0`, the sum of any function of adjacent slice endpoints is unchanged when deletion
edges are enumerated as insertion edges. -/
theorem cube_slice_edge_balance (n k : ℕ) (hk0 : 0 < k)
    (g : (Fin n → Bool) → (Fin n → Bool) → ℝ) :
    (∑ x : Fin n → Bool, if cubeHamming x=k then
      ∑ i : Fin n, if x i then g x (cubeFlip x i) else 0 else 0) =
      ∑ y : Fin n → Bool, if cubeHamming y=k-1 then
        ∑ i : Fin n, if y i=false then g (cubeFlip y i) y else 0 else 0 := by
  have hl : (∑ x : Fin n → Bool, if cubeHamming x=k then
      ∑ i : Fin n, if x i then g x (cubeFlip x i) else 0 else 0) =
      ∑ i : Fin n, ∑ x : Fin n → Bool, if cubeHamming x=k ∧ x i=true then g x (cubeFlip x i) else 0 := by
    rw [← Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : cubeHamming x=k <;> simp [hx]
  rw [hl]
  have hmap (i : Fin n) :
      (∑ x : Fin n → Bool, if cubeHamming x=k ∧ x i=true then g x (cubeFlip x i) else 0) =
        ∑ y : Fin n → Bool, if cubeHamming y=k-1 ∧ y i=false then g (cubeFlip y i) y else 0 := by
    rw [← Equiv.sum_comp (cubeFlipEquiv i) (fun x => if cubeHamming x=k ∧ x i=true then g x (cubeFlip x i) else 0)]
    apply Finset.sum_congr rfl
    intro y _
    change (if cubeHamming (cubeFlip y i)=k ∧ cubeFlip y i i=true then g (cubeFlip y i) (cubeFlip (cubeFlip y i) i) else 0) = _
    have hb := cube_hamming_flip_balance y i
    cases hi : y i
    · have hbit : cubeFlip y i i=true := by simp [cubeFlip,hi]
      have hc : cubeHamming (cubeFlip y i)=cubeHamming y+1 := by simpa [hi] using hb
      have hiff : cubeHamming (cubeFlip y i)=k ↔ cubeHamming y=k-1 := by omega
      simp [hbit,hiff,cube_flip_involution]
    · have hbit : cubeFlip y i i=false := by simp [cubeFlip,hi]
      simp [hbit]
  simp_rw [hmap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : cubeHamming y=k-1 <;> simp [hy]

/-- The expected sum of a function over true coordinates on the `k` slice is `k` times its slice
expectation. -/
theorem cube_slice_ones_expect (n k : ℕ) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n k) (fun x => ∑ i : Fin n, if x i then f x else 0) =
      (k : ℝ)*cubeExpect n (sliceWeight n k) f := by
  have hp (x : Fin n → Bool) : (∑ i : Fin n, if x i then f x else 0) = (cubeHamming x : ℝ)*f x := by
    rw [← cube_hamming_cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp
  simp_rw [hp]
  rw [← cube_expect_const_mul n (sliceWeight n k) (k : ℝ) f]
  unfold cubeExpect sliceWeight
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · (try dsimp only)
    rw [hx]
  · simp

/-- For `0 < k ≤ n`, the expected sum of function values after inserting a true bit into the `k
- 1` slice equals `n - k + 1` times its mean on the `k` slice. -/
theorem cube_slice_insert_expect (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n (k-1)) (fun y => ∑ i : Fin n, if y i=false then f (cubeFlip y i) else 0) =
      (n-k+1 : ℕ)*cubeExpect n (sliceWeight n k) f := by
  have he := cube_slice_edge_balance n k hk0 (fun x _ => f x)
  have hp (x : Fin n → Bool) : (∑ i : Fin n, if x i then f x else 0) = (cubeHamming x : ℝ)*f x := by
    rw [← cube_hamming_cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> simp
  simp_rw [hp] at he
  have hl : (∑ x : Fin n → Bool, if cubeHamming x=k then (cubeHamming x : ℝ)*f x else 0) =
      (k : ℝ)*∑ x : Fin n → Bool, if cubeHamming x=k then f x else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h <;> simp [h]
  rw [hl] at he
  have hn : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ) ≠ 0 :=
    by exact_mod_cast (cube_slice_card_pos n k hk).ne'
  have hm : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k-1)).card : ℝ) ≠ 0 :=
    by exact_mod_cast (cube_slice_card_pos n (k-1) (by omega)).ne'
  rw [cube_slice_expect_uniform, cube_slice_expect_uniform, ← he]
  have hc := cube_slice_adjacent_card_identity n k hk0 hk
  have hr : ((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k-1)).card : ℝ)⁻¹*(k : ℝ) =
      (n-k+1 : ℕ)*((Finset.univ.filter (fun x : Fin n → Bool => cubeHamming x=k)).card : ℝ)⁻¹ := by
    field_simp
    linarith only [hc]
  rw [← mul_assoc, hr, mul_assoc]

/-- When `k ≤ n`, the expected sum of a function over false coordinates on the `k` slice is `n -
k` times its slice expectation. -/
theorem cube_slice_zeros_expect (n k : ℕ) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n k) (fun x => ∑ i : Fin n, if x i=false then f x else 0) =
      (n-k : ℕ)*cubeExpect n (sliceWeight n k) f := by
  have hp (x : Fin n → Bool) : (∑ i : Fin n, if x i=false then f x else 0) =
      ((Finset.univ.filter (fun i : Fin n => x i=false)).card : ℝ)*f x := by
    simp only [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  simp_rw [hp]
  rw [← cube_expect_const_mul n (sliceWeight n k) (n-k : ℕ) f]
  unfold cubeExpect sliceWeight
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · have hc : (Finset.univ.filter (fun i : Fin n => x i=false)).card = n-k := by
      have he := cube_zero_count x
      omega
    (try dsimp only)
    rw [hc]
  · simp

/-- For `0 < k ≤ n`, the expected sum of differences from deleting true bits on the `k` slice is
`k` times the difference between the `k` and `k - 1` slice means. -/
theorem cube_slice_difference_down (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n k) (fun x => ∑ i : Fin n, if x i then f x-f (cubeFlip x i) else 0) =
      (k : ℝ)*(cubeExpect n (sliceWeight n k) f-cubeExpect n (sliceWeight n (k-1)) f) := by
  have hp (x : Fin n → Bool) : (∑ i : Fin n, if x i then f x-f (cubeFlip x i) else 0) =
      (∑ i : Fin n, if x i then f x else 0)-(∑ i : Fin n, if x i then f (cubeFlip x i) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [hp]
  rw [cube_expect_sub, cube_slice_ones_expect, cube_slice_delete_expect n k hk0 hk]
  ring

/-- For `0 < k ≤ n`, the expected sum of differences from inserting true bits on the `k - 1`
slice is `n - k + 1` times the difference between the `k` and `k - 1` slice means. -/
theorem cube_slice_difference_up (n k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (f : (Fin n → Bool) → ℝ) :
    cubeExpect n (sliceWeight n (k-1)) (fun x => ∑ i : Fin n, if x i=false then f (cubeFlip x i)-f x else 0) =
      (n-k+1 : ℕ)*(cubeExpect n (sliceWeight n k) f-cubeExpect n (sliceWeight n (k-1)) f) := by
  have hp (x : Fin n → Bool) : (∑ i : Fin n, if x i=false then f (cubeFlip x i)-f x else 0) =
      (∑ i : Fin n, if x i=false then f (cubeFlip x i) else 0)-(∑ i : Fin n, if x i=false then f x else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  simp_rw [hp]
  rw [cube_expect_sub, cube_slice_insert_expect n k hk0 hk,
      cube_slice_zeros_expect n (k-1) (by omega)]
  have he : n-(k-1) = n-k+1 := by omega
  rw [he]
  ring

end Qatlib.Concepts.ProbabilityCore.DistributionAA
