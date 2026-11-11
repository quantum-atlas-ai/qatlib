/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MacaulayHHL21.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.3 — ℓ2 lower bound in a complex affine hull

Fixed paper: arXiv:2111.00405, Lemma 4.3 on p.7–8.

Statement (verbatim): *Suppose `y₁, y₂, …, y_t` are vectors with 0 and 1 entries such that
their Hamming weights are equal. Then every vector in their (complex) affine hull `A` has
length (ℓ2 norm) at least `‖y₁‖ / √t`.*

The proof follows the paper line by line.  Every `yᵢ` is 0/1, so `⟨yᵢ, 1⟩ = ‖yᵢ‖₁ = ‖y₁‖₁ = h`.
For `y = Σ wᵢ yᵢ` in the affine hull, `Σ_k y_k = h`, hence `‖y‖₁ ≥ h`.  The support of `y` is
contained in the union of the supports of the `yᵢ`, so `‖y‖₀ ≤ t·h`.  Cauchy–Schwarz gives
`‖y‖₁² ≤ ‖y‖₀·‖y‖₂²`, hence `h² ≤ t·h·‖y‖₂²` and `‖y‖₂ ≥ √(h/t) = ‖y₁‖₂/√t`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MacaulayHHL21.MainResults.Lemma43

open Qatlib.Papers.MacaulayHHL21.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Lemma 4.3** (arXiv:2111.00405, p.7–8): a complex affine combination of 0/1 vectors of equal
Hamming weight has ℓ2 norm at least `‖Y 0‖ / √t`.  Here `Y 0` plays the role of `y₁`, and the
affine hull is `{Σ wᵢ Yᵢ : Σ wᵢ = 1}` over `ℂ`. -/
theorem lemma43_affineHull_l2_lowerBound
    {t : ℕ} [NeZero t] (Y : Fin t → ι → ℂ)
    (hZ : ∀ i, IsZeroOne (Y i))
    (hEq : ∀ i, hammingWeight (Y i) = hammingWeight (Y 0))
    {y : ι → ℂ} (hy : y ∈ affineHull Y) :
    l2Norm (Y 0) ≤ Real.sqrt (t : ℝ) * l2Norm y := by
  classical
  have ht : 0 < t := Nat.pos_of_neZero t
  set h : ℕ := hammingWeight (Y 0) with hh
  obtain ⟨w, hwsum, hyeq⟩ := hy
  have hyk : ∀ k, y k = ∑ i, w i * Y i k := fun k => congrFun hyeq k
  -- (1) squared ℓ2 norm of the reference vector `Y 0`
  have hY0sq : l2NormSq (Y 0) = (h : ℝ) := by
    rw [zeroOne_l2NormSq_eq_hammingWeight (hZ 0), ← hh]
  -- (2) the entry sum of any affine combination equals the common Hamming weight
  have hsum_y : (∑ k, y k) = (h : ℂ) := by
    have h1 : ∀ i : Fin t, (∑ k, w i * Y i k) = w i * (h : ℂ) := by
      intro i
      have hw : (∑ k, Y i k) = (h : ℂ) := by
        rw [zeroOne_sum_eq_hammingWeight (hZ i), hEq i]
      simp only [← hw, Finset.mul_sum]
    calc (∑ k, y k) = ∑ k, ∑ i, w i * Y i k := by
            refine Finset.sum_congr rfl ?_; intro k _; exact hyk k
      _ = ∑ i : Fin t, ∑ k, w i * Y i k := Finset.sum_comm
      _ = ∑ i : Fin t, w i * (h : ℂ) := by
            refine Finset.sum_congr rfl ?_; intro i _; exact h1 i
      _ = (∑ i : Fin t, w i) * (h : ℂ) := by rw [Finset.sum_mul]
      _ = 1 * (h : ℂ) := by rw [hwsum]
      _ = (h : ℂ) := one_mul _
  -- (3) the ℓ1 norm dominates the Hamming weight
  have hl1_ge : (h : ℝ) ≤ l1Norm y := by
    have htri : ‖∑ k, y k‖ ≤ ∑ k, ‖y k‖ := norm_sum_le _ _
    have hnorm : ‖∑ k, y k‖ = (h : ℝ) := by
      rw [hsum_y]
      simp
    rw [l1Norm]
    calc (h : ℝ) = ‖∑ k, y k‖ := hnorm.symm
      _ ≤ ∑ k, ‖y k‖ := htri
  -- (4) the support of `y` is bounded by the union of the supports of the `Yᵢ`
  have hsupp : (supportSize y : ℝ) ≤ (t : ℝ) * (h : ℝ) := by
    have hsub : univ.filter (fun k => y k ≠ 0) ⊆
        univ.biUnion (fun i : Fin t => univ.filter (fun k => Y i k ≠ 0)) := by
      intro k hk
      simp only [mem_filter, mem_univ, true_and] at hk
      simp only [mem_biUnion, mem_univ, mem_filter, true_and]
      by_cases hex : ∃ i : Fin t, Y i k ≠ 0
      · exact hex
      · exfalso
        apply hk
        rw [hyk k]
        apply Finset.sum_eq_zero
        intro i _
        push_neg at hex
        rw [hex i, mul_zero]
    have hcard : (univ.filter (fun k => y k ≠ 0)).card ≤
        ∑ i : Fin t, (univ.filter (fun k => Y i k ≠ 0)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hweight : ∀ i : Fin t, (univ.filter (fun k => Y i k ≠ 0)).card = h := by
      intro i
      have hswap : (univ.filter (fun k => Y i k ≠ 0)).card = hammingWeight (Y i) := by
        rw [hammingWeight_eq_supportSize (hZ i)]
        rfl
      rw [hswap, hEq i]
    have hsupp_nat : supportSize y ≤ t * h := by
      have hsum : (∑ i : Fin t, h) = t * h := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      calc supportSize y = (univ.filter (fun k => y k ≠ 0)).card := rfl
        _ ≤ ∑ i : Fin t, (univ.filter (fun k => Y i k ≠ 0)).card := hcard
        _ = ∑ i : Fin t, h := by
              refine Finset.sum_congr rfl ?_; intro i _; exact hweight i
        _ = t * h := hsum
    exact_mod_cast hsupp_nat
  -- (5) Cauchy–Schwarz on the support
  have hCS : (l1Norm y) ^ 2 ≤ (supportSize y : ℝ) * l2NormSq y := by
    let S : Finset ι := univ.filter (fun k => y k ≠ 0)
    have hzero : ∀ k ∈ (univ : Finset ι), k ∉ S → ‖y k‖ = 0 := by
      intro k _ hk
      simp only [S, mem_filter, mem_univ, true_and, not_not] at hk
      simp [hk]
    have h1 : l1Norm y = ∑ k ∈ S, ‖y k‖ := by
      rw [l1Norm]
      exact (Finset.sum_subset (Finset.subset_univ S) hzero).symm
    have h2 : l2NormSq y = ∑ k ∈ S, ‖y k‖ ^ 2 := by
      rw [l2NormSq]
      refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
      intro k _ hk
      have h0 := hzero k (mem_univ k) hk
      simp [h0]
    have h3 : (∑ k ∈ S, ‖y k‖) ^ 2 ≤ (S.card : ℝ) * ∑ k ∈ S, ‖y k‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq (s := S) (f := fun k => ‖y k‖)
    have hScard : (S.card : ℝ) = (supportSize y : ℝ) := by
      simp only [S, supportSize]
    rw [h1, h2, ← hScard]
    exact h3
  -- (6) arithmetic conclusion
  rcases Nat.eq_zero_or_pos h with hzero | hpos
  · have hY00 : l2Norm (Y 0) = 0 := by
      rw [l2Norm, hY0sq, hzero]; simp
    rw [hY00]
    exact mul_nonneg (Real.sqrt_nonneg _) (l2Norm_nonneg _)
  · have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hpos
    have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hsq_le : (h : ℝ) ^ 2 ≤ (t : ℝ) * (h : ℝ) * l2NormSq y := by
      calc (h : ℝ) ^ 2 ≤ (l1Norm y) ^ 2 := by nlinarith [hl1_ge, hhpos.le]
        _ ≤ (supportSize y : ℝ) * l2NormSq y := hCS
        _ ≤ ((t : ℝ) * (h : ℝ)) * l2NormSq y :=
              mul_le_mul_of_nonneg_right hsupp (l2NormSq_nonneg y)
    have hle : (h : ℝ) ≤ (t : ℝ) * l2NormSq y := by
      have hmul : (h : ℝ) * (h : ℝ) ≤ (h : ℝ) * ((t : ℝ) * l2NormSq y) := by
        calc (h : ℝ) * (h : ℝ) = (h : ℝ) ^ 2 := by ring
          _ ≤ (t : ℝ) * (h : ℝ) * l2NormSq y := hsq_le
          _ = (h : ℝ) * ((t : ℝ) * l2NormSq y) := by ring
      exact le_of_mul_le_mul_left hmul hhpos
    have hratio : (h : ℝ) / (t : ℝ) ≤ l2NormSq y := by
      rw [div_le_iff₀ htpos]
      nlinarith [hle]
    have hsqrt_le : Real.sqrt ((h : ℝ) / (t : ℝ)) ≤ l2Norm y := by
      rw [l2Norm]
      exact Real.sqrt_le_sqrt hratio
    have hnormY0 : l2Norm (Y 0) = Real.sqrt (h : ℝ) := by
      rw [l2Norm, hY0sq]
    calc l2Norm (Y 0) = Real.sqrt (h : ℝ) := hnormY0
      _ = Real.sqrt (t : ℝ) * Real.sqrt ((h : ℝ) / (t : ℝ)) := by
            rw [← Real.sqrt_mul htpos.le]
            congr 1
            field_simp
      _ ≤ Real.sqrt (t : ℝ) * l2Norm y :=
            mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)

end Qatlib.Papers.MacaulayHHL21.MainResults.Lemma43
