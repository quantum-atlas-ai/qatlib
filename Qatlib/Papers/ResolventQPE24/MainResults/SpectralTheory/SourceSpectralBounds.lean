/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ResolventQPE24.MainResults.Prelude

set_option backward.isDefEq.respectTransparency false

/-!
# Schur Spectral Norm, Jordan Resolvent, and Restricted Kreiss Bounds

This module formalizes Section 2.2 (Lemma 2.7, Proposition 2.8, and Lemma 2.11,
pp. 8--9) of Alase and Karuvade on the Schur row/column-sum spectral norm bound,
the Jordan-decomposition resolvent norm bound, and the strip and circle
restricted Kreiss constant bounds.

## Main statements

* `spectral_norm_le_rowCol_sums`: Lemma 2.7, Equation (18),
  `‖C‖ ≤ √rowMax · √colMax` from row and column `ℓ_1` bounds.
* `resolvent_norm_bound`: Proposition 2.8, Equation (19),
  `‖(z · 1 - C)⁻¹‖ ≤ κ̄ (1 - δ^d) / (δ^d (1 - δ))` for Jordan decompositions.
* `kreiss_strip_bound`, `kreiss_circle_bound`: Lemma 2.11, Equations (27)--(28),
  strip and circle restricted Kreiss constant upper bounds.

## References

* [Alase and Karuvade, 2024][AlaseKaruvade2024], Section 2.2, Lemma 2.7,
  Proposition 2.8, and Lemma 2.11, pp. 8--9.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.ResolventQPE24.MainResults.SpectralTheory

open Qatlib.Papers.ResolventQPE24.MainResults.Prelude

private def jordanInverse (a : ℂ) (m : ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun i j => if j.val ≤ i.val then a⁻¹ ^ (i.val - j.val + 1) else 0

private lemma jordan_inverse_mul {m : ℕ} (z lam : ℂ) (ha : z - lam ≠ 0) :
    (z • 1 - jordanBlock lam m) * jordanInverse (z - lam) m = 1 := by
  have hentry (i k : Fin m) :
      (z • 1 - jordanBlock lam m) i k =
        (if i = k then z - lam else 0) - (if k.val + 1 = i.val then 1 else 0) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul, jordanBlock, Matrix.of_apply]
    by_cases hik : i = k
    · subst k
      simp
    · simp [hik]
  ext i j
  simp only [Matrix.mul_apply, hentry, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ite_true]
  rw [← sub_mul]
  by_cases hi : i.val = 0
  · have hzero : ∀ k : Fin m, ¬ k.val + 1 = i.val := by intro k; omega
    simp only [hzero, ite_false, Finset.sum_const_zero, sub_zero]
    by_cases hij : i = j
    · subst j
      simp [jordanInverse, ha]
    · have hj : ¬ j.val ≤ i.val := by
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp only [jordanInverse, Matrix.of_apply, hj, ite_false, mul_zero, Matrix.one_apply, hij]
  · let p : Fin m := ⟨i.val - 1, by omega⟩
    have hp : p.val + 1 = i.val := by dsimp [p]; omega
    have hsum : (∑ k : Fin m, if k.val + 1 = i.val then jordanInverse (z - lam) m k j else 0) =
        jordanInverse (z - lam) m p j := by
      rw [Finset.sum_eq_single p]
      · simp [hp]
      · intro b _ hb
        have : ¬ b.val + 1 = i.val := by
          intro h
          apply hb
          apply Fin.ext
          omega
        simp [this]
      · simp
    rw [hsum]
    by_cases hij : i = j
    · subst j
      have hpi : ¬ i.val ≤ p.val := by omega
      simp only [jordanInverse, Matrix.of_apply, hpi, ite_false, le_refl, ite_true,
        Nat.sub_self, zero_add, pow_one, mul_inv_cancel₀ ha, sub_zero, Matrix.one_apply, ite_true]
    · by_cases hji : j.val ≤ i.val
      · have hjp : j.val ≤ p.val := by
          have : i.val ≠ j.val := fun h => hij (Fin.ext h)
          omega
        have hexp : i.val - j.val + 1 = (p.val - j.val + 1) + 1 := by omega
        simp only [jordanInverse, Matrix.of_apply, hji, hjp, ite_true, Matrix.one_apply, hij, ite_false]
        rw [hexp, pow_succ, mul_left_comm, mul_inv_cancel₀ ha, mul_one, sub_self]
      · have hjp : ¬ j.val ≤ p.val := by omega
        simp only [jordanInverse, Matrix.of_apply, hji, hjp, ite_false, mul_zero, sub_zero,
          Matrix.one_apply, hij]

private lemma jordanInverse_sums {m D : ℕ} (a : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (hdis : δ ≤ ‖a‖) (hm : m ≤ D) :
    (∀ i, ∑ j, ‖jordanInverse a m i j‖ ≤ ∑ k ∈ Finset.range D, δ⁻¹ ^ (k + 1)) ∧
    (∀ j, ∑ i, ‖jordanInverse a m i j‖ ≤ ∑ k ∈ Finset.range D, δ⁻¹ ^ (k + 1)) := by
  have hpow (k : ℕ) : ‖a⁻¹‖ ^ (k + 1) ≤ δ⁻¹ ^ (k + 1) := by
    rw [norm_inv]
    exact pow_le_pow_left₀ (by positivity) (inv_anti₀ hδ hdis) _
  constructor
  · intro i
    have heq : (∑ j, ‖jordanInverse a m i j‖) =
        ∑ j ∈ Finset.univ.filter (fun j : Fin m => j.val ≤ i.val),
          ‖a⁻¹‖ ^ (i.val - j.val + 1) := by
      simp only [jordanInverse, Matrix.of_apply, Finset.sum_filter,
        apply_ite norm, norm_pow, norm_zero]
    rw [heq]
    apply Finset.sum_le_sum_of_injOn (fun j : Fin m => i.val - j.val)
    · intro j hj k hk he
      have hj' := (Finset.mem_filter.mp hj).2
      have hk' := (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp at he
      omega
    · intro k hk
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
      simp only [Finset.mem_range]
      have hi := i.isLt
      omega
    · intro j _
      exact hpow _
    · intro k _ _
      positivity
  · intro j
    have heq : (∑ i, ‖jordanInverse a m i j‖) =
        ∑ i ∈ Finset.univ.filter (fun i : Fin m => j.val ≤ i.val),
          ‖a⁻¹‖ ^ (i.val - j.val + 1) := by
      simp only [jordanInverse, Matrix.of_apply, Finset.sum_filter,
        apply_ite norm, norm_pow, norm_zero]
    rw [heq]
    apply Finset.sum_le_sum_of_injOn (fun i : Fin m => i.val - j.val)
    · intro i hi k hk he
      have hi' := (Finset.mem_filter.mp hi).2
      have hk' := (Finset.mem_filter.mp hk).2
      apply Fin.ext
      dsimp at he
      omega
    · intro k hk
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
      simp only [Finset.mem_range]
      have hi' := i.isLt
      omega
    · intro i _
      exact hpow _
    · intro k _ _
      positivity

private lemma inverse_geom_sum (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (D : ℕ) :
    (∑ k ∈ Finset.range D, δ⁻¹ ^ (k + 1)) =
      (1 - δ ^ D) / (δ ^ D * (1 - δ)) := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [Finset.sum_range_succ, ih]
    simp only [inv_pow, pow_succ]
    field_simp [ne_of_gt hδ0, ne_of_gt (sub_pos.mpr hδ1)]
    ring


/-- **c004 — Lemma 2.7 (Spectral norm bound for matrices), p. 8, Eq. (18).**
For `C ∈ ℂ^{N×N}` with all row sums bounded by `rowMax` and all column sums
bounded by `colMax`,
`‖C‖ ≤ √rowMax · √colMax`.

Taking `rowMax = max_j ∑_k |C_jk|` and `colMax = max_k ∑_j |C_jk|` gives the
paper's Eq. (18) verbatim. -/
theorem spectral_norm_le_rowCol_sums {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ)
    (rowMax colMax : ℝ)
    (hrow : ∀ i, ∑ j, ‖C i j‖ ≤ rowMax)
    (hcol : ∀ j, ∑ i, ‖C i j‖ ≤ colMax)
    (hrow0 : 0 ≤ rowMax) (hcol0 : 0 ≤ colMax) :
    ‖C‖ ≤ Real.sqrt rowMax * Real.sqrt colMax := by
  by_cases _htriv : (∀ i, ∑ j, ‖C i j‖ ≤ rowMax) ∧
      (∀ j, ∑ i, ‖C i j‖ ≤ colMax) ∧ 0 ≤ rowMax ∧ 0 ≤ colMax
  swap
  · exact False.elim (_htriv ⟨hrow, hcol, hrow0, hcol0⟩)
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) ?_
  intro x
  have hsq : ‖toEuclideanLin C x‖ ^ 2 ≤ rowMax * colMax * ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ i, ‖(C *ᵥ x.ofLp) i‖ ^ 2) ≤
      rowMax * colMax * ∑ j, ‖x.ofLp j‖ ^ 2
    have hrowx (i : Fin N) : ‖(C *ᵥ x.ofLp) i‖ ^ 2 ≤
        rowMax * ∑ j, ‖C i j‖ * ‖x.ofLp j‖ ^ 2 := by
      have htri : ‖(C *ᵥ x.ofLp) i‖ ≤ ∑ j, ‖C i j‖ * ‖x.ofLp j‖ := by
        simpa only [Matrix.mulVec, dotProduct, norm_mul] using
          (norm_sum_le (s := Finset.univ) (f := fun j => C i j * x.ofLp j))
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun j => Real.sqrt ‖C i j‖)
        (fun j => Real.sqrt ‖C i j‖ * ‖x.ofLp j‖)
      have heq : (∑ j, Real.sqrt ‖C i j‖ *
          (Real.sqrt ‖C i j‖ * ‖x.ofLp j‖)) =
          ∑ j, ‖C i j‖ * ‖x.ofLp j‖ := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
      rw [heq] at hcs
      simp only [mul_pow, Real.sq_sqrt (norm_nonneg _)] at hcs
      exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans
        (hcs.trans (mul_le_mul_of_nonneg_right (hrow i)
          (Finset.sum_nonneg fun j hj => mul_nonneg (norm_nonneg _) (sq_nonneg _))))
    calc
      (∑ i, ‖(C *ᵥ x.ofLp) i‖ ^ 2) ≤
          ∑ i, rowMax * ∑ j, ‖C i j‖ * ‖x.ofLp j‖ ^ 2 :=
        Finset.sum_le_sum fun i hi => hrowx i
      _ = rowMax * ∑ j, (∑ i, ‖C i j‖) * ‖x.ofLp j‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [Finset.sum_mul]
      _ ≤ rowMax * ∑ j, colMax * ‖x.ofLp j‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hrow0
        exact Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg _)
      _ = _ := by rw [← Finset.mul_sum, mul_assoc]
  change ‖toEuclideanLin C x‖ ≤ (Real.sqrt rowMax * Real.sqrt colMax) * ‖x‖
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  simpa only [mul_pow, Real.sq_sqrt hrow0, Real.sq_sqrt hcol0, mul_assoc] using hsq

/-- **c005 — Proposition 2.8 (spectral norm bound on the resolvent), p. 8,
Eq. (19).**  Let `C = T J T⁻¹` have a Jordan decomposition with largest block
size `d`, let `z` be outside the spectrum, and suppose the distance of `z`
to every Jordan eigenvalue is at least `δ` with `0 < δ < 1`.  Then
`‖(z·1 - C)⁻¹‖ ≤ κ̄ · (1-δ^d)/(δ^d(1-δ))` for every `κ̄ ≥ ‖T‖‖T⁻¹‖`.

The paper's `κ̄_C` is the minimum of `‖T‖‖T⁻¹‖` over all Jordan
decompositions (Def. 2.6), so an arbitrary upper bound `κ̄` is the faithful
formulation. -/
theorem resolvent_norm_bound
    {N s : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (d : Fin s → ℕ) (lam : Fin s → ℂ)
    (e : Fin N ≃ Σ l, Fin (d l)) (T : Matrix (Fin N) (Fin N) ℂ)
    (hs : 0 < s) (hd : ∀ l, 0 < d l) (hT : T.det ≠ 0)
    (hJ : C = T * (jordanBlockDiagonal lam d).submatrix e e * T⁻¹)
    (z : ℂ) (hz : ∀ l, z ≠ lam l) (δ kbar : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hdist : ∀ l, δ ≤ ‖z - lam l‖)
    (hκ : ‖T‖ * ‖T⁻¹‖ ≤ kbar) :
    ‖Qatlib.Papers.ResolventQPE24.MainResults.Prelude.resolvent C z‖ ≤
      kbar * (1 - δ ^ maxBlockSize d) / (δ ^ maxBlockSize d * (1 - δ)) := by
  by_cases _htriv : 1 ≤ maxBlockSize d
  swap
  · exact False.elim (_htriv ((hd ⟨0, hs⟩).trans_le (Finset.le_sup (Finset.mem_univ _))))
  let R := fun l => jordanInverse (z - lam l) (d l)
  let RB := Matrix.blockDiagonal' R
  let RJ := RB.submatrix e e
  let J := (jordanBlockDiagonal lam d).submatrix e e
  let B := ∑ k ∈ Finset.range (maxBlockSize d), δ⁻¹ ^ (k + 1)
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ => by positivity
  have hblock : (z • 1 - jordanBlockDiagonal lam d) * RB = 1 := by
    have hfactor : z • 1 - jordanBlockDiagonal lam d =
        Matrix.blockDiagonal' (fun l => z • 1 - jordanBlock (lam l) (d l)) := by
      change z • 1 - jordanBlockDiagonal lam d =
        Matrix.blockDiagonal' (z • (1 : ∀ l, Matrix (Fin (d l)) (Fin (d l)) ℂ) -
          (fun l => jordanBlock (lam l) (d l)))
      rw [Matrix.blockDiagonal'_sub, Matrix.blockDiagonal'_smul, Matrix.blockDiagonal'_one]
      rfl
    rw [hfactor, ← Matrix.blockDiagonal'_mul]
    have hh : (fun l => (z • 1 - jordanBlock (lam l) (d l)) * R l) = 1 := by
      funext l
      exact jordan_inverse_mul z (lam l) (sub_ne_zero.mpr (hz l))
    rw [hh, Matrix.blockDiagonal'_one]
  have hright : (z • 1 - J) * RJ = 1 := by
    have hfactor : z • 1 - J = (z • 1 - jordanBlockDiagonal lam d).submatrix e e := by
      simp only [J, Matrix.submatrix_sub, Matrix.submatrix_smul, Pi.sub_apply,
        Pi.smul_apply, Matrix.submatrix_one_equiv]
    change (z • 1 - J) * RB.submatrix e e = 1
    rw [hfactor, Matrix.submatrix_mul_equiv, hblock, Matrix.submatrix_one_equiv]
  have hleft : RJ * (z • 1 - J) = 1 := mul_eq_one_comm.mp hright
  have hsums := fun l => jordanInverse_sums (z - lam l) δ hδ0 (hdist l)
    (Finset.le_sup (Finset.mem_univ l) : d l ≤ maxBlockSize d)
  have hrow : ∀ i, ∑ j, ‖RJ i j‖ ≤ B := by
    intro i
    change (∑ j, ‖RB (e i) (e j)‖) ≤ B
    rw [e.sum_comp (fun v => ‖RB (e i) v‖)]
    generalize e i = v
    rcases v with ⟨l, r⟩
    change (∑ j, ‖Matrix.blockDiagonal' R ⟨l, r⟩ j‖) ≤ B
    rw [Fintype.sum_sigma]
    have hsum : (∑ l', ∑ j : Fin (d l'), ‖Matrix.blockDiagonal' R ⟨l, r⟩ ⟨l', j⟩‖) =
        ∑ j, ‖R l r j‖ := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hne
        simp [Matrix.blockDiagonal'_apply_ne R r _ (Ne.symm hne)]
      · simp
    rw [hsum]
    exact (hsums l).1 r
  have hcol : ∀ j, ∑ i, ‖RJ i j‖ ≤ B := by
    intro j
    change (∑ i, ‖RB (e i) (e j)‖) ≤ B
    rw [e.sum_comp (fun v => ‖RB v (e j)‖)]
    generalize e j = v
    rcases v with ⟨l, c⟩
    change (∑ i, ‖Matrix.blockDiagonal' R i ⟨l, c⟩‖) ≤ B
    rw [Fintype.sum_sigma]
    have hsum : (∑ l', ∑ i : Fin (d l'), ‖Matrix.blockDiagonal' R ⟨l', i⟩ ⟨l, c⟩‖) =
        ∑ i, ‖R l i c‖ := by
      rw [Finset.sum_eq_single l]
      · simp
      · intro l' _ hne
        simp [Matrix.blockDiagonal'_apply_ne R _ c hne]
      · simp
    rw [hsum]
    exact (hsums l).2 c
  have hnorm : ‖RJ‖ ≤ B := by
    simpa only [Real.mul_self_sqrt hB] using spectral_norm_le_rowCol_sums RJ B B hrow hcol hB hB
  have hTu : IsUnit T.det := isUnit_iff_ne_zero.mpr hT
  have hTT := Matrix.mul_nonsing_inv T hTu
  have hTiT := Matrix.nonsing_inv_mul T hTu
  have hsim : z • 1 - C = T * (z • 1 - J) * T⁻¹ := by
    rw [hJ]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, hTT, J]
  have hconj : (z • 1 - C) * (T * RJ * T⁻¹) = 1 := by
    rw [hsim]
    calc
      T * (z • 1 - J) * T⁻¹ * (T * RJ * T⁻¹) =
          T * ((z • 1 - J) * RJ) * T⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc T⁻¹ T, hTiT, Matrix.one_mul]
      _ = 1 := by rw [hright, Matrix.mul_one, hTT]
  have hconj' : (T * RJ * T⁻¹) * (z • 1 - C) = 1 := by
    rw [hsim]
    calc
      T * RJ * T⁻¹ * (T * (z • 1 - J) * T⁻¹) =
          T * (RJ * (z • 1 - J)) * T⁻¹ := by
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc T⁻¹ T, hTiT, Matrix.one_mul]
      _ = 1 := by rw [hleft, Matrix.mul_one, hTT]
  have hres : Qatlib.Papers.ResolventQPE24.MainResults.Prelude.resolvent C z = T * RJ * T⁻¹ := Matrix.inv_eq_left_inv hconj'
  rw [hres, mul_div_assoc, ← inverse_geom_sum δ hδ0 hδ1]
  calc
    ‖T * RJ * T⁻¹‖ ≤ (‖T‖ * ‖RJ‖) * ‖T⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ = (‖T‖ * ‖T⁻¹‖) * ‖RJ‖ := by ring
    _ ≤ kbar * B := mul_le_mul hκ hnorm (norm_nonneg _) (hκ.trans' (by positivity))
    _ = _ := rfl

private lemma kreiss_prefactor (δ kbar : ℝ) (D : ℕ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hD : 1 ≤ D) :
    δ * (kbar * (1 - δ ^ D) / (δ ^ D * (1 - δ))) =
      kbar * (1 / δ) ^ (D - 1) * ((1 - δ ^ D) / (1 - δ)) := by
  have hp : δ ^ D = δ ^ (D - 1) * δ := by
    conv_lhs => rw [show D = (D - 1) + 1 by omega]
    rw [pow_succ]
  rw [one_div, inv_pow, hp]
  field_simp [ne_of_gt hδ0, ne_of_gt (sub_pos.mpr hδ1)]

/-- **c006(1) — Lemma 2.11(1), p. 9, Eq. (27).**  If no Jordan eigenvalue has
real part in `(0, 2δ)`, then
`K_δ(C) ≤ κ̄ · (1/δ)^{d-1} · (1-δ^d)/(1-δ)`. -/
theorem kreiss_strip_bound
    {N s : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (d : Fin s → ℕ) (lam : Fin s → ℂ)
    (e : Fin N ≃ Σ l, Fin (d l)) (T : Matrix (Fin N) (Fin N) ℂ)
    (hs : 0 < s) (hd : ∀ l, 0 < d l) (hT : T.det ≠ 0)
    (hJ : C = T * (jordanBlockDiagonal lam d).submatrix e e * T⁻¹)
    (δ kbar : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hspec : ∀ l, ¬ (0 < (lam l).re ∧ (lam l).re < 2 * δ))
    (hκ : ‖T‖ * ‖T⁻¹‖ ≤ kbar) :
    kreissStrip C δ ≤
      kbar * (1 / δ) ^ (maxBlockSize d - 1) * ((1 - δ ^ maxBlockSize d) / (1 - δ)) := by
  have hD : 1 ≤ maxBlockSize d :=
    (hd ⟨0, hs⟩).trans_le (Finset.le_sup (Finset.mem_univ _))
  rw [kreissStrip, ← kreiss_prefactor δ kbar (maxBlockSize d) hδ0 hδ1 hD]
  apply mul_le_mul_of_nonneg_left _ hδ0.le
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨y, rfl⟩
  have hdist : ∀ l, δ ≤ ‖(δ : ℂ) + Complex.I * (y : ℂ) - lam l‖ := by
    intro l
    have hre : ((δ : ℂ) + Complex.I * (y : ℂ) - lam l).re =
        δ - (lam l).re := by simp
    have habs : δ ≤ |((δ : ℂ) + Complex.I * (y : ℂ) - lam l).re| := by
      rw [hre]
      by_cases h : (lam l).re ≤ 0
      · exact le_trans (by linarith) (le_abs_self _)
      · have hx : 2 * δ ≤ (lam l).re := by
          by_contra hx
          exact hspec l ⟨lt_of_not_ge h, lt_of_not_ge hx⟩
        exact le_trans (by linarith) (neg_le_abs _)
    exact habs.trans (Complex.abs_re_le_norm _)
  have hz : ∀ l, (δ : ℂ) + Complex.I * (y : ℂ) ≠ lam l := by
    intro l h
    have hh := hdist l
    rw [h, sub_self, norm_zero] at hh
    exact (not_le_of_gt hδ0) hh
  exact resolvent_norm_bound C d lam e T hs hd hT hJ _ hz δ kbar
    hδ0 hδ1 hdist hκ

/-- **c006(2) — Lemma 2.11(2), p. 9, Eq. (28).**  If no Jordan eigenvalue has
modulus in `(1, 1 + 2δ)`, then
`K_δ°(C) ≤ κ̄ · (1/δ)^{d-1} · (1-δ^d)/(1-δ)`. -/
theorem kreiss_circle_bound
    {N s : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (d : Fin s → ℕ) (lam : Fin s → ℂ)
    (e : Fin N ≃ Σ l, Fin (d l)) (T : Matrix (Fin N) (Fin N) ℂ)
    (hs : 0 < s) (hd : ∀ l, 0 < d l) (hT : T.det ≠ 0)
    (hJ : C = T * (jordanBlockDiagonal lam d).submatrix e e * T⁻¹)
    (δ kbar : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hspec : ∀ l, ¬ (1 < ‖lam l‖ ∧ ‖lam l‖ < 1 + 2 * δ))
    (hκ : ‖T‖ * ‖T⁻¹‖ ≤ kbar) :
    kreissCircle C δ ≤
      kbar * (1 / δ) ^ (maxBlockSize d - 1) * ((1 - δ ^ maxBlockSize d) / (1 - δ)) := by
  have hD : 1 ≤ maxBlockSize d :=
    (hd ⟨0, hs⟩).trans_le (Finset.le_sup (Finset.mem_univ _))
  rw [kreissCircle, ← kreiss_prefactor δ kbar (maxBlockSize d) hδ0 hδ1 hD]
  apply mul_le_mul_of_nonneg_left _ hδ0.le
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨θ, rfl⟩
  let z : ℂ := (1 + δ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))
  have hnorm : ‖z‖ = 1 + δ := by
    dsimp [z]
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
    have hcast : (1 + δ : ℂ) = ((1 + δ : ℝ) : ℂ) := by push_cast; rfl
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hdist : ∀ l, δ ≤ ‖z - lam l‖ := by
    intro l
    by_cases h : ‖lam l‖ ≤ 1
    · have hh := norm_sub_norm_le z (lam l)
      rw [hnorm] at hh
      linarith
    · have hx : 1 + 2 * δ ≤ ‖lam l‖ := by
        by_contra hx
        exact hspec l ⟨lt_of_not_ge h, lt_of_not_ge hx⟩
      have hh := norm_sub_norm_le (lam l) z
      rw [hnorm, norm_sub_rev] at hh
      linarith
  have hz : ∀ l, z ≠ lam l := by
    intro l h
    have hh := hdist l
    rw [h, sub_self, norm_zero] at hh
    exact (not_le_of_gt hδ0) hh
  exact resolvent_norm_bound C d lam e T hs hd hT hJ z hz δ kbar
    hδ0 hδ1 hdist hκ

end Qatlib.Papers.ResolventQPE24.MainResults.SpectralTheory
