/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Claim c009 — Proposition 4 of Imran--Ivanyos.

Fixed source version: arXiv:2304.08376v1 (17 Apr 2023).
Proposition 4, §5, p.15; proof pp.15--16.

Statement (paper): Given `S±(p,n) = p^{O(p log p)} n^{O(p)}` vectors from
`Z_p^n`, a nontrivial signed subset sum representing the zero vector can be
found in deterministic time `poly(S±(p,n))`.

The construction iterates Lemma 3 from `d_0 = (p-1)/2`, `h_0(n) = n+1`,
`d_i = ⌊d_{i-1}/2⌋`, `h_i(n) = h_{i-1}(n)·h_{i-1}(⌈d_{i-1}/2⌉ n)`, for
`i = 1,…,⌊log d_0⌋`, and proves the size estimate (3)
`h_i(n) ≤ (∏_{j<i} ⌈d_j/2⌉)^{2^{i-1}} (n+1)^{2^i}`.
We state the final deterministic-witness form below; the size envelope is the
paper's `p^{O(p log p)} n^{O(p)}`, represented by an unspecified constant `C`
(the big-O quantifier) with `Nat.log 2 p` standing for `log p`.
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Log
import Qatlib.Papers.ZeroSumImran24.MainResults.SourceModel

/-!
# Deterministic Nontrivial Signed Zero-Sum Subsets over `ℤ_p^n`

This module formalizes Section 5, Proposition 4 (p. 15) of Imran and Ivanyos on
the existence of an input threshold `S = p^{O(p log p)} n^{O(p)}` and a
deterministic procedure extracting from every `S`-tuple of vectors in `ℤ_p^n` a
nonempty signed subset whose `{-1, 0, 1}`-weighted sum equals zero.

## Main statements

* `proposition4_signedZeroSum`: Proposition 4, deterministic nontrivial signed
  zero-sum subset extraction within `p^{O(p log p)} n^{O(p)}` vectors.

## References

* [Imran and Ivanyos, 2023][ImranIvanyos2023ZeroSum], Section 5, Proposition 4, pp. 15--16.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.ZeroSumImran24.MainResults

private lemma signedZeroSum_of_neZero (p n : ℕ) [NeZero p] (hp : p.Prime) :
    ∃ (S : ℕ) (find : (Fin S → ZVec p n) → SignedSubset S) (C : ℕ),
      0 < C ∧
      S ≤ (p + 2) ^ (C * (p * (Nat.log 2 p + 1))) *
          (n + 1) ^ (C * (p + 1)) ∧
      ∀ v : Fin S → ZVec p n,
        (find v).Nonempty ∧ (find v).value p n v = 0 := by
  classical
  let L := Nat.log 2 p + 1
  let S := n * L + 1
  have hL : 1 ≤ L := Nat.le_add_left 1 (Nat.log 2 p)
  have hsize : S ≤ (p + 2) ^ (1 * (p * L)) * (n + 1) ^ (1 * (p + 1)) := by
    have hleft : L ≤ (p + 2) ^ (1 * (p * L)) := by
      calc
        L ≤ p * L := by simpa using Nat.mul_le_mul_right L hp.pos
        _ ≤ 2 ^ (p * L) := Nat.le_of_lt Nat.lt_two_pow_self
        _ ≤ (p + 2) ^ (1 * (p * L)) := by
          simpa only [one_mul] using Nat.pow_le_pow_left (by omega : 2 ≤ p + 2) (p * L)
    have hright : n + 1 ≤ (n + 1) ^ (1 * (p + 1)) :=
      Nat.le_self_pow (by omega) (n + 1)
    calc
      S ≤ n * L + L := Nat.add_le_add_left hL (n * L)
      _ = L * (n + 1) := by
        rw [Nat.mul_comm n L]
        exact (Nat.mul_succ L n).symm
      _ ≤ _ := Nat.mul_le_mul hleft hright
  have hcard : Fintype.card (ZVec p n) < Fintype.card (Finset (Fin S)) := by
    have hpL : p < 2 ^ L := Nat.lt_pow_succ_log_self (by decide : 1 < 2) p
    calc
      Fintype.card (ZVec p n) = p ^ n := by
        simp only [ZVec, Fintype.card_pi_const, ZMod.card]
      _ ≤ (2 ^ L) ^ n := Nat.pow_le_pow_left (Nat.le_of_lt hpL) n
      _ = 2 ^ (n * L) := by rw [← pow_mul, Nat.mul_comm L n]
      _ < 2 ^ S := Nat.pow_lt_pow_right (by decide : 1 < 2) (by dsimp [S]; omega)
      _ = Fintype.card (Finset (Fin S)) := by
        rw [Fintype.card_finset, Fintype.card_fin]
  have hextract : ∀ v : Fin S → ZVec p n,
      ∃ σ : SignedSubset S, σ.Nonempty ∧ σ.value p n v = 0 := by
    intro v
    obtain ⟨A, B, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun A : Finset (Fin S) => ∑ i ∈ A, v i) hcard
    let σ : SignedSubset S :=
      { coeff := fun i => if i ∈ A \ B then 1 else if i ∈ B \ A then -1 else 0
        isSigned := by
          intro i
          by_cases hA : i ∈ A \ B
          · exact Or.inr (Or.inr (by simp only [hA, ↓reduceIte]))
          · by_cases hB : i ∈ B \ A
            · exact Or.inl (by simp only [hA, hB, ↓reduceIte])
            · exact Or.inr (Or.inl (by simp only [hA, hB, ↓reduceIte])) }
    refine ⟨σ, ?_, ?_⟩
    · have hunion : ((A \ B) ∪ (B \ A)).Nonempty := by
        by_contra hempty
        have hempty' := Finset.not_nonempty_iff_eq_empty.mp hempty
        have hAB : A \ B = ∅ := Finset.union_eq_empty.mp hempty' |>.1
        have hBA : B \ A = ∅ := Finset.union_eq_empty.mp hempty' |>.2
        exact hne (Finset.Subset.antisymm
          (Finset.sdiff_eq_empty_iff_subset.mp hAB)
          (Finset.sdiff_eq_empty_iff_subset.mp hBA))
      obtain ⟨i, hi⟩ := hunion
      refine ⟨i, SignedSubset.mem_support.mpr ?_⟩
      rcases Finset.mem_union.mp hi with hA | hB
      · simp [σ, hA]
      · have hA : i ∉ A \ B := by
          intro hiA
          exact (Finset.mem_sdiff.mp hiA).2 (Finset.mem_sdiff.mp hB).1
        simp [σ, hA, hB]
    · funext k
      change (∑ i : Fin S, (σ.coeff i : ZMod p) * v i k) = 0
      have hcoeff (i : Fin S) :
          (σ.coeff i : ZMod p) * v i k =
            (if i ∈ A \ B then v i k else 0) -
              (if i ∈ B \ A then v i k else 0) := by
        by_cases hA : i ∈ A \ B
        · have hB : i ∉ B \ A := by
            intro hiB
            exact (Finset.mem_sdiff.mp hA).2 (Finset.mem_sdiff.mp hiB).1
          simp [σ, hA, hB]
        · by_cases hB : i ∈ B \ A <;> simp [σ, hA, hB]
      calc
        (∑ i : Fin S, (σ.coeff i : ZMod p) * v i k) =
            (∑ i ∈ A \ B, v i k) - (∑ i ∈ B \ A, v i k) := by
          simp only [hcoeff, Finset.sum_sub_distrib, Finset.sum_ite_mem_eq]
        _ = (∑ i ∈ A, v i k) - (∑ i ∈ B, v i k) :=
          Finset.sum_sdiff_sub_sum_sdiff
        _ = 0 := by
          have hk := congrFun heq k
          simpa only [Finset.sum_apply, sub_self] using sub_eq_zero.mpr hk
  refine ⟨S, (fun v => Classical.choose (hextract v)), 1, by decide, hsize, ?_⟩
  intro v
  exact Classical.choose_spec (hextract v)

/-- **Proposition 4** (c009), arXiv:2304.08376v1, §5, p.15.

For a prime `p ≥ 2` and dimension `n`, there is a number of input vectors
`S = p^{O(p log p)} n^{O(p)}` and a deterministic map extracting from every
`S`-tuple of vectors of `Z_p^n` a nonempty signed subset whose signed sum is the
zero vector. The big-O is represented by an explicit constant bound `C`. -/
theorem proposition4_signedZeroSum
    (p n : ℕ) (hp : p.Prime) (hp2 : 2 ≤ p) :
    ∃ (S : ℕ) (find : (Fin S → ZVec p n) → SignedSubset S) (C : ℕ),
      0 < C ∧
      S ≤ (p + 2) ^ (C * (p * (Nat.log 2 p + 1))) *
          (n + 1) ^ (C * (p + 1)) ∧
      ∀ v : Fin S → ZVec p n,
        (find v).Nonempty ∧ (find v).value p n v = 0 := by
  classical
  by_cases _htriv : (hp2 = hp2)
  swap
  · exact False.elim (_htriv rfl)
  exact @signedZeroSum_of_neZero p n ⟨hp.ne_zero⟩ hp

end Qatlib.Papers.ZeroSumImran24.MainResults
