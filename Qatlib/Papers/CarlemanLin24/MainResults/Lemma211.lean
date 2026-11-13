/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CarlemanLin24.MainResults.Source.SourceModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Block Back-Substitution Bound for Carleman Eigenvectors

This module formalizes Lemma 2.11 of [Wu, Wang, and Li, 2024][WuWangLi2024], bounding the `ℓ₁`
norm of each block of `V⁻¹ *ᵥ forcingVec F2 x` in terms of the terminal block via block
back-substitution through the upper-triangular Carleman eigenvector matrix `V`.

## Main statements

* `lemma_2_11`: geometric `ℓ₁` block bound `(4 * Real.exp 1 * kappa1 W Winv * matOneNorm F2 / Δ) ^ (N - (j.1 + 1))`
  relative to the `N`-th block.

## References

* [Wu, Wang, and Li, 2024][WuWangLi2024]
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.CarlemanLin24.MainResults.Lemma211

open Qatlib.Papers.CarlemanLin24.MainResults.Source

private lemma matOneNorm_nonneg {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) : 0 ≤ matOneNorm M :=
  NNReal.coe_nonneg _

private lemma vecL1_mulVec_le {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℂ) (v : J → ℂ) :
    vecL1 (M.mulVec v) ≤ matOneNorm M * vecL1 v := by
  classical
  have hcol (j : J) : (∑ i, ‖M i j‖) ≤ matOneNorm M := by
    simpa only [matOneNorm, NNReal.coe_sum, coe_nnnorm] using
      (NNReal.coe_le_coe.mpr (Finset.le_sup (f := fun j => ∑ i, ‖M i j‖₊)
        (Finset.mem_univ j)))
  calc
    vecL1 (M.mulVec v) ≤ ∑ i, ∑ j, ‖M i j‖ * ‖v j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [Matrix.mulVec, dotProduct, norm_mul] using
        (norm_sum_le Finset.univ (fun j => M i j * v j))
    _ = ∑ j, (∑ i, ‖M i j‖) * ‖v j‖ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ ∑ j, matOneNorm M * ‖v j‖ :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hcol j) (norm_nonneg _)
    _ = matOneNorm M * vecL1 v := by rw [vecL1, Finset.mul_sum]

private lemma vecL1_sum_le {I J : Type*} [Fintype I]
    (s : Finset J) (v : J → I → ℂ) :
    vecL1 (∑ j ∈ s, v j) ≤ ∑ j ∈ s, vecL1 (v j) := by
  classical
  simp only [vecL1, Finset.sum_apply]
  exact (Finset.sum_le_sum fun i _ => norm_sum_le s (fun j => v j i)).trans_eq
    (Finset.sum_comm)

private lemma vecL1_blockAt {n N : ℕ} (w : CarlemanIdx n N → ℂ)
    (b : ℕ) (hb : 0 < b) (hbN : b ≤ N) :
    vecL1 (blockAt w b hb hbN) =
      vecL1 (carlemanBlockVec w ⟨b - 1, by omega⟩) := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  rfl

private lemma scalar_recurrence_bound (A : ℝ) (hA : 0 ≤ A) (f : ℕ → ℝ)
    (D : ℕ)
    (hrec : ∀ d, 0 < d → d ≤ D →
      f d ≤ ∑ r ∈ Finset.range d, A ^ (d - r) * f r)
    (d : ℕ) (hd : 0 < d) (hdD : d ≤ D) :
    f d ≤ (2 : ℝ) ^ (d - 1) * A ^ d * f 0 := by
  have hgeom (t : ℕ) : 1 + ∑ r ∈ Finset.range t, (2 : ℝ) ^ r = 2 ^ t := by
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.sum_range_succ, pow_succ]; linarith
  induction d using Nat.strong_induction_on with
  | h d ih =>
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
    calc
      f (t + 1) ≤ ∑ r ∈ Finset.range (t + 1), A ^ (t + 1 - r) * f r :=
        hrec _ hd hdD
      _ = A ^ (t + 1) * f 0 +
          ∑ r ∈ Finset.range t, A ^ (t + 1 - (r + 1)) * f (r + 1) := by
        rw [Finset.sum_range_succ']
        simp only [Nat.sub_zero]
        ring
      _ ≤ A ^ (t + 1) * f 0 +
          ∑ r ∈ Finset.range t, (2 : ℝ) ^ r * A ^ (t + 1) * f 0 := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro r hr
        have hrlt : r < t := Finset.mem_range.mp hr
        calc
          A ^ (t + 1 - (r + 1)) * f (r + 1) ≤
              A ^ (t + 1 - (r + 1)) *
                ((2 : ℝ) ^ (r + 1 - 1) * A ^ (r + 1) * f 0) :=
            mul_le_mul_of_nonneg_left (ih (r + 1) (by omega) (by omega) (by omega))
              (pow_nonneg hA _)
          _ = (2 : ℝ) ^ r * (A ^ (t + 1 - (r + 1)) * A ^ (r + 1)) * f 0 := by
            simp only [Nat.add_sub_cancel]
            ring
          _ = (2 : ℝ) ^ r * A ^ (t + 1) * f 0 := by
            rw [← pow_add, Nat.sub_add_cancel (by omega : r + 1 ≤ t + 1)]
      _ = (2 : ℝ) ^ (t + 1 - 1) * A ^ (t + 1) * f 0 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        simp only [Nat.add_sub_cancel]
        calc
          _ = (1 + ∑ r ∈ Finset.range t, (2 : ℝ) ^ r) * A ^ (t + 1) * f 0 := by ring
          _ = _ := by rw [hgeom]

/-- **Lemma 2.11** (arXiv:2405.12714v2, p. 13, Eq. (50)).

Let `V` be the eigenvector matrix of Theorem 2.10: invertible, block upper
triangular (`V_{k,j} = 0` for `j < k`), identity diagonal blocks, and with the
normalized block-product bound of Corollary 2.10.1.  Let
`ζ := V⁻¹ · (0,…,0, A_{N,N+1} x^{⊗(N+1)})` be the vector of Eq. (49).  Then,
for every block index `b = j.1 + 1` with `b < N`,

`‖ζ_b‖₁ ≤ (4e κ₁(W) ‖F₂‖₁ / Δ)^{N−b} ‖ζ_N‖₁`.

(`4e = 4 · Real.exp 1`.) -/
theorem lemma_2_11
    {n N : ℕ} (hN : 2 ≤ N)
    (F1 : Matrix (Fin n) (Fin n) ℂ) (F2 : Matrix (Fin n) (PairIdx n) ℂ)
    (W Winv : Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℂ) (Δ : ℝ)
    (hass : AssumptionOne F1 W Winv lam Δ)
    (V : Matrix (CarlemanIdx n N) (CarlemanIdx n N) ℂ)
    (hVunit : IsUnit V)
    (hdiag : ∀ k : Fin N, blockMat V k k = 1)
    (hzero : ∀ (k j : Fin N), j.1 < k.1 → blockMat V k j = 0)
    (hprod : ∀ (k j : Fin N), k.1 ≤ j.1 →
      matOneNorm ((blockMat V k k)⁻¹ * blockMat V k j) ≤
        (2 * Real.exp 1 * kappa1 W Winv * matOneNorm F2 / Δ) ^ (j.1 - k.1))
    (x : Vec n)
    (j : Fin N) (hj : j.1 + 1 < N) :
    vecL1 (blockAt (V⁻¹.mulVec (forcingVec F2 x)) (j.1 + 1) (by omega) (by omega)) ≤
      (4 * Real.exp 1 * kappa1 W Winv * matOneNorm F2 / Δ) ^ (N - (j.1 + 1)) *
        vecL1 (blockAt (V⁻¹.mulVec (forcingVec F2 x)) N (by omega) (by omega)) := by
  classical
  let ζ := V⁻¹.mulVec (forcingVec F2 x)
  let A : ℝ := 2 * Real.exp 1 * kappa1 W Winv * matOneNorm F2 / Δ
  have hA : 0 ≤ A :=
    div_nonneg
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos 1).le)
        (mul_nonneg (matOneNorm_nonneg W) (matOneNorm_nonneg Winv)))
        (matOneNorm_nonneg F2)) hass.delta_pos.le
  have hsolve : V.mulVec ζ = forcingVec F2 x := by
    dsimp [ζ]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V
      (V.isUnit_iff_isUnit_det.mp hVunit), Matrix.one_mulVec]
  have hrow (k : Fin N) (hk : k.1 < N - 1) :
      carlemanBlockVec ζ k =
        -∑ m ∈ Finset.univ.filter (fun m : Fin N => k.1 < m.1),
          (blockMat V k m).mulVec (carlemanBlockVec ζ m) := by
    have hsum : (∑ m : Fin N,
        (blockMat V k m).mulVec (carlemanBlockVec ζ m)) = 0 := by
      ext α
      have he := congrFun hsolve ⟨k, α⟩
      have hkN : k.1 + 1 ≠ N := by omega
      simpa only [Matrix.mulVec, dotProduct, Fintype.sum_sigma, blockMat,
        carlemanBlockVec, forcingVec, hkN, ite_false, Finset.sum_apply,
        Pi.zero_apply] using he
    have hlow : (∑ m ∈ Finset.univ.filter (fun m : Fin N => ¬k.1 < m.1),
        (blockMat V k m).mulVec (carlemanBlockVec ζ m)) = carlemanBlockVec ζ k := by
      rw [Finset.sum_eq_single k]
      · rw [hdiag k, Matrix.one_mulVec]
      · intro m hm hmk
        have hmle := (Finset.mem_filter.mp hm).2
        have hmne : m.1 ≠ k.1 := fun h => hmk (Fin.ext h)
        rw [hzero k m (by omega), Matrix.zero_mulVec]
      · simp
    have he := Finset.sum_filter_not_add_sum_filter Finset.univ
      (fun m : Fin N => k.1 < m.1)
      (fun m => (blockMat V k m).mulVec (carlemanBlockVec ζ m))
    rw [hlow, hsum] at he
    exact eq_neg_of_add_eq_zero_left he
  have hnorm (k : Fin N) (hk : k.1 < N - 1) :
      vecL1 (carlemanBlockVec ζ k) ≤
        ∑ m ∈ Finset.univ.filter (fun m : Fin N => k.1 < m.1),
          A ^ (m.1 - k.1) * vecL1 (carlemanBlockVec ζ m) := by
    rw [hrow k hk]
    have hneg (v : TensorIdx n (k.1 + 1) → ℂ) : vecL1 (-v) = vecL1 v := by
      simp [vecL1]
    rw [hneg]
    refine (vecL1_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro m hm
    have hkm := (Finset.mem_filter.mp hm).2
    have hb : matOneNorm (blockMat V k m) ≤ A ^ (m.1 - k.1) := by
      simpa only [hdiag k, inv_one, Matrix.one_mul] using hprod k m hkm.le
    exact (vecL1_mulVec_le _ _).trans
      (mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun _ _ => norm_nonneg _))
  -- Reverse the block order: the argument is the distance from the terminal block.
  let f : ℕ → ℝ := fun d =>
    if hd : d < N then vecL1 (carlemanBlockVec ζ ⟨N - 1 - d, by omega⟩) else 0
  have hrec (d : ℕ) (hd : 0 < d) (hdN : d ≤ N - 1) :
      f d ≤ ∑ r ∈ Finset.range d, A ^ (d - r) * f r := by
    have hdlt : d < N := by omega
    let k : Fin N := ⟨N - 1 - d, by omega⟩
    have hk : k.1 < N - 1 := by dsimp [k]; omega
    have hf : f d = vecL1 (carlemanBlockVec ζ k) := by simp [f, hdlt, k]
    rw [hf]
    refine (hnorm k hk).trans_eq ?_
    refine Finset.sum_bij (fun m _ => N - 1 - m.1) ?_ ?_ ?_ ?_
    · intro m hm
      have hkm := (Finset.mem_filter.mp hm).2
      apply Finset.mem_range.mpr
      dsimp [k] at hkm
      omega
    · intro m hm m' hm' he
      apply Fin.ext
      have hmN := m.isLt
      have hmN' := m'.isLt
      omega
    · intro r hr
      have hrd : r < d := Finset.mem_range.mp hr
      refine ⟨⟨N - 1 - r, by omega⟩, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ _, by dsimp [k]; omega⟩
      · dsimp
        omega
    · intro m hm
      have hkm := (Finset.mem_filter.mp hm).2
      have hrN : N - 1 - m.1 < N := by omega
      have hmEq : (⟨N - 1 - (N - 1 - m.1), by omega⟩ : Fin N) = m := by
        apply Fin.ext
        dsimp
        omega
      have hexp : m.1 - k.1 = d - (N - 1 - m.1) := by dsimp [k] at *; omega
      simp only [f, hrN, dite_true, hexp]
      exact congrArg (fun m' : Fin N =>
        A ^ (d - (N - 1 - m.1)) * vecL1 (carlemanBlockVec ζ m')) hmEq.symm
  let d := N - (j.1 + 1)
  have hd : 0 < d := by dsimp [d]; omega
  have hdN : d ≤ N - 1 := by dsimp [d]; omega
  have hsharp := scalar_recurrence_bound A hA f (N - 1) hrec d hd hdN
  have hfj : f d = vecL1 (carlemanBlockVec ζ j) := by
    have hdlt : d < N := by omega
    have he : (⟨N - 1 - d, by omega⟩ : Fin N) = j := by
      apply Fin.ext
      dsimp [d]
      omega
    simp only [f, hdlt, dite_true]
    exact congrArg (fun k : Fin N => vecL1 (carlemanBlockVec ζ k)) he
  have hlast : f 0 = vecL1 (blockAt ζ N (by omega) (by omega)) := by
    have hN0 : 0 < N := by omega
    simp only [f, hN0, dite_true, Nat.sub_zero]
    exact (vecL1_blockAt ζ N (by omega) (by omega)).symm
  rw [hfj, hlast] at hsharp
  rw [vecL1_blockAt]
  change vecL1 (carlemanBlockVec ζ j) ≤ _
  calc
    vecL1 (carlemanBlockVec ζ j) ≤
        (2 : ℝ) ^ (d - 1) * A ^ d * vecL1 (blockAt ζ N (by omega) (by omega)) := hsharp
    _ ≤ (2 : ℝ) ^ d * A ^ d * vecL1 (blockAt ζ N (by omega) (by omega)) := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.sub_le d 1))
          (pow_nonneg hA d)
      · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
    _ = _ := by
      have he : 2 * A = 4 * Real.exp 1 * kappa1 W Winv * matOneNorm F2 / Δ := by
        dsimp [A]
        ring
      rw [← mul_pow, he]

end Qatlib.Papers.CarlemanLin24.MainResults.Lemma211
