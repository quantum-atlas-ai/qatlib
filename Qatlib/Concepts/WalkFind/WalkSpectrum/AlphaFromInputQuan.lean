/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.WalkSpectrum.AlphaFromInputStat
import Qatlib.Concepts.WalkFind.WalkSpectrum.BlockUnitary
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Basic
set_option warningAsError false
open Qatlib.Concepts.WalkFind.UniqueCollision

set_option autoImplicit false

namespace Qatlib.Concepts.WalkFind.WalkSpectrum

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

private theorem vandermonde_types (k N r : ℕ) (hkr : k ≤ r) (hkN : k ≤ N) :
    (∑ j ∈ Finset.range (k + 1), Nat.choose k j * Nat.choose (N - k) (r - j)) =
      Nat.choose N r := by
  have h := Nat.add_choose_eq k (N - k) r
  rw [Nat.add_sub_of_le hkN, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  change Nat.choose N r = ∑ j ∈ Finset.range (r + 1), Nat.choose k j * Nat.choose (N - k)
      (r - j) at h
  have hr : r + 1 = (k + 1) + (r - k) := by omega
  rw [hr, Finset.sum_range_add] at h
  have hz : (∑ j ∈ Finset.range (r - k),
      Nat.choose k (k + 1 + j) * Nat.choose (N - k) (r - (k + 1 + j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [Nat.choose_eq_zero_of_lt (by omega), zero_mul]
  simpa [hz] using h.symm

theorem jwStartNormSq_eq (k N r : ℕ) (hkr : k ≤ r) (hkNr : k ≤ N - r) (hrN : r ≤ N) :
    jwStartNormSq k N r = ((Nat.choose N r) * (N - r) : ℝ) := by
  have hjN : k ≤ N := le_trans hkNr (Nat.sub_le _ _)
  have hpair (j : Fin k) :
      jwCnt k N r j false + jwCnt k N r j true =
        Nat.choose k j * Nat.choose (N - k) (r - j) * (N - r) := by
    have hj := j.isLt
    have he : N - r - (k - j.val) + (k - j.val) = N - r := by omega
    simp only [jwCnt, Bool.false_eq_true, ite_false, ite_true]
    rw [← Nat.mul_add, he]
  have htotal :
      (∑ j : Fin k, (jwCnt k N r j false + jwCnt k N r j true)) + jwCnt k N r k false =
      Nat.choose N r * (N - r) := by
    simp_rw [hpair]
    simp only [jwCnt, Nat.choose_self, one_mul, Bool.false_eq_true, ite_false, Nat.sub_self,
        Nat.sub_zero]
    rw [← Finset.sum_mul, ← add_mul]
    congr 1
    have hg : (∑ j : Fin (k + 1), Nat.choose k j.val * Nat.choose (N - k) (r - j.val)) =
        Nat.choose N r := by
      exact (Fin.sum_univ_eq_sum_range
        (fun j => Nat.choose k j * Nat.choose (N - k) (r - j)) (k + 1)).trans
          (vandermonde_types k N r hkr hjN)
    rw [Fin.sum_univ_castSucc] at hg
    simpa using hg
  unfold jwStartNormSq
  rw [jwTypeSum k (fun j l => (jwCnt k N r j l : ℝ)), ← Nat.cast_sub hrN]
  exact_mod_cast htotal

theorem jwGoodTilde_overlap (k N r : ℕ) :
    (∑ i : Fin (2 * k + 1), star (jwGoodTilde k i) * jwStart k N r i) =
      (Real.sqrt (jwCnt k N r k false) : ℂ) := by
  have hcoord (i : Fin (2 * k + 1)) :
      jwPsiCoord k i = (k, false) ↔ i = Fin.last (2 * k) := by
    simp only [jwPsiCoord, Prod.mk.injEq, Fin.ext_iff, Fin.val_last]
    have hi := i.isLt
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : i.val % 2 ≠ 1 := by simpa using h2
      omega
    · intro h
      rw [h]
      simp
  simp_rw [jwGoodTilde, hcoord]
  simp [jwStart, jwPsiCoord]

theorem alphaFromInput : AlphaFromInput := by
  intro k N r hk hkr hkNr
  have hNr : 0 < N - r := by omega
  have hrN : r ≤ N := by omega
  have hknr := le_of_lt hkNr
  have ht := jwStartNormSq_eq k N r hkr hknr hrN
  have hcm : 0 < Nat.choose (N - k) (r - k) := Nat.choose_pos (by omega)
  have hct : 0 < Nat.choose N r := Nat.choose_pos hrN
  have hm : 0 < (jwCnt k N r k false : ℝ) := by
    simp only [jwCnt, Nat.choose_self, one_mul, Bool.false_eq_true, ite_false, Nat.sub_self,
        Nat.sub_zero]
    exact_mod_cast Nat.mul_pos hcm hNr
  have hNrRpos : (0 : ℝ) < N - r := by
    have hc : (r : ℝ) < N := by exact_mod_cast (by omega : r < N)
    linarith
  have hp : 0 < jwStartNormSq k N r := by
    rw [ht]
    exact mul_pos (Nat.cast_pos.mpr hct) hNrRpos
  have hmle : (jwCnt k N r k false : ℝ) ≤ jwStartNormSq k N r := by
    unfold jwStartNormSq
    have hi : jwPsiCoord k (Fin.last (2 * k)) = (k, false) := by simp [jwPsiCoord]
    simpa only [hi] using Finset.single_le_sum
      (fun (i : Fin (2 * k + 1)) _ => Nat.cast_nonneg
        (jwCnt k N r (jwPsiCoord k i).1 (jwPsiCoord k i).2))
      (Finset.mem_univ (Fin.last (2 * k)))
  refine ⟨ht, jwGoodTilde_overlap k N r, ?_, ?_, ?_⟩
  · unfold jwAlpha
    rw [div_pow, Real.sq_sqrt (le_of_lt hm), Real.sq_sqrt (le_of_lt hp), ht]
    simp only [jwCnt, Nat.choose_self, one_mul, Bool.false_eq_true, ite_false, Nat.sub_self, Nat.sub_zero,
      Nat.cast_mul, Nat.cast_sub hrN]
    have hNrR : (N : ℝ) - r ≠ 0 := ne_of_gt hNrRpos
    rw [mul_div_mul_right _ _ hNrR]
  · exact div_pos (Real.sqrt_pos.mpr hm) (Real.sqrt_pos.mpr hp)
  · exact (div_le_one (Real.sqrt_pos.mpr hp)).mpr (Real.sqrt_le_sqrt hmle)

end Qatlib.Concepts.WalkFind.WalkSpectrum
