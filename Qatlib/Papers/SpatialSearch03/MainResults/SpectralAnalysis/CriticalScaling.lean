/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.SpectralAnalysis.Marginal
import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatticeSumBound
import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatticeSum2Bound
import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatSum1Log
import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatticeSum2Log
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults

open Finset
open ThetaSums

variable {d : ℕ}

theorem dispersion_le_four_mul (k : Fin d → ℝ) : dispersion k ≤ 4 * (d : ℝ) := by
  unfold dispersion
  have h : ∑ j : Fin d, (1 - Real.cos (k j)) ≤ ∑ _j : Fin d, (2 : ℝ) := by
    refine Finset.sum_le_sum ?_
    intro j _
    linarith [Real.neg_one_le_cos (k j)]
  calc 2 * ∑ j : Fin d, (1 - Real.cos (k j)) ≤ 2 * ∑ _j : Fin d, (2 : ℝ) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 4 * (d : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
        ring

theorem inv_dispersion_ge_four {n : ℕ} [NeZero n] (hn : 0 < n)
    {m : Fin d → ZMod n} (hm : m ≠ 0) :
    (4 * (d : ℝ))⁻¹ ≤ (dispersion (waveVector n m))⁻¹ :=
  inv_anti₀ (dispersion_waveVector_pos hn hm) (dispersion_le_four_mul _)

theorem latSum1_pos {n d : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d) :
    0 < latSum1 n d := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < ((n : ℝ) ^ d)⁻¹ := inv_pos.mpr (pow_pos hnR d)
  have hcard : 0 < ((Finset.univ : Finset (Fin d → ZMod n)).erase
      (0 : Fin d → ZMod n)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have h1 : Fintype.card (Fin d → ZMod n) = n ^ d := by simp
    rw [h1]
    have h2 : (1 : ℕ) < n ^ d := by
      calc (1 : ℕ) < n := hn
        _ = n ^ 1 := by rw [pow_one]
        _ ≤ n ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hne : ((Finset.univ : Finset (Fin d → ZMod n)).erase
      (0 : Fin d → ZMod n)).Nonempty := Finset.card_pos.mp hcard
  obtain ⟨m, hm⟩ := hne
  have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
  have hpos : 0 < (dispersion (waveVector n m))⁻¹ :=
    inv_pos.2 (dispersion_waveVector_pos hn0 hm0)
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n),
      0 ≤ (dispersion (waveVector n i))⁻¹ := by
    intro i _
    exact inv_nonneg.2 (dispersion_nonneg _)
  have hle : (dispersion (waveVector n m))⁻¹
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n),
          (dispersion (waveVector n i))⁻¹ :=
    Finset.single_le_sum hnn hm
  unfold latSum1
  exact mul_pos hNpos (lt_of_lt_of_le hpos hle)

theorem latSum2_pos {n d : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d) :
    0 < latSum2 n d := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < ((n : ℝ) ^ d)⁻¹ := inv_pos.mpr (pow_pos hnR d)
  have hcard : 0 < ((Finset.univ : Finset (Fin d → ZMod n)).erase
      (0 : Fin d → ZMod n)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have h1 : Fintype.card (Fin d → ZMod n) = n ^ d := by simp
    rw [h1]
    have h2 : (1 : ℕ) < n ^ d := by
      calc (1 : ℕ) < n := hn
        _ = n ^ 1 := by rw [pow_one]
        _ ≤ n ^ d := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hne : ((Finset.univ : Finset (Fin d → ZMod n)).erase
      (0 : Fin d → ZMod n)).Nonempty := Finset.card_pos.mp hcard
  obtain ⟨m, hm⟩ := hne
  have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
  have hpos : 0 < (dispersion (waveVector n m))⁻¹ ^ 2 :=
    pow_pos (inv_pos.2 (dispersion_waveVector_pos hn0 hm0)) 2
  have hnn : ∀ i ∈ (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n),
      0 ≤ (dispersion (waveVector n i))⁻¹ ^ 2 := by
    intro i _
    exact sq_nonneg _
  have hle : (dispersion (waveVector n m))⁻¹ ^ 2
      ≤ ∑ i ∈ (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n),
          (dispersion (waveVector n i))⁻¹ ^ 2 :=
    Finset.single_le_sum hnn hm
  unfold latSum2
  exact mul_pos hNpos (lt_of_lt_of_le hpos hle)

theorem latSum1_ge {n d : ℕ} [NeZero n] (hn : 0 < n) (_hd : 0 < d) :
    ((n : ℝ) ^ d - 1) / ((n : ℝ) ^ d * (4 * (d : ℝ))) ≤ latSum1 n d := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hNinv : (0 : ℝ) < ((n : ℝ) ^ d)⁻¹ := inv_pos.2 hNpos
  set S := (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n) with hS
  have hterm : ∀ m ∈ S, (4 * (d : ℝ))⁻¹ ≤ (dispersion (waveVector n m))⁻¹ := by
    intro m hm
    exact inv_dispersion_ge_four hn (Finset.mem_erase.mp hm).1
  have hsum : (S.card : ℝ) * (4 * (d : ℝ))⁻¹
      ≤ ∑ m ∈ S, (dispersion (waveVector n m))⁻¹ := by
    have h := Finset.sum_le_sum hterm
    have hc : ∑ _m ∈ S, (4 * (d : ℝ))⁻¹ = (S.card : ℝ) * (4 * (d : ℝ))⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rwa [hc] at h
  have hcardval : (S.card : ℝ) = (n : ℝ) ^ d - 1 := by
    have h1 : S.card = n ^ d - 1 := by
      rw [hS, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have hc : Fintype.card (Fin d → ZMod n) = n ^ d := by simp
      rw [hc]
    have hle : (1 : ℕ) ≤ n ^ d := Nat.one_le_pow d n hn
    rw [h1, Nat.cast_sub hle]
    push_cast
    ring
  have hstep : ((n : ℝ) ^ d - 1) / ((n : ℝ) ^ d * (4 * (d : ℝ)))
      ≤ ((n : ℝ) ^ d)⁻¹ * ∑ m ∈ S, (dispersion (waveVector n m))⁻¹ := by
    have heq : ((n : ℝ) ^ d - 1) / ((n : ℝ) ^ d * (4 * (d : ℝ)))
        = ((n : ℝ) ^ d)⁻¹ * ((S.card : ℝ) * (4 * (d : ℝ))⁻¹) := by
      rw [hcardval, div_eq_mul_inv, mul_inv]
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_left hsum hNinv.le
  unfold latSum1
  rw [hS] at hstep
  exact hstep

theorem latSum1_ge_eighth {n d : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d) :
    (8 * (d : ℝ))⁻¹ ≤ latSum1 n d := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hN2 : (2 : ℝ) ≤ (n : ℝ) ^ d := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    calc (2 : ℝ) ≤ (n : ℝ) := h2
      _ = (n : ℝ) ^ 1 := by rw [pow_one]
      _ ≤ (n : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
  have hhalf : ((n : ℝ) ^ d)⁻¹ ≤ 1 / 2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hN2
    simpa using h
  have hcomp : (1 - ((n : ℝ) ^ d)⁻¹) * (4 * (d : ℝ))⁻¹
      = ((n : ℝ) ^ d - 1) / ((n : ℝ) ^ d * (4 * (d : ℝ))) := by
    have hNne : ((n : ℝ) ^ d) ≠ 0 := ne_of_gt hNpos
    have h4dne : (4 * (d : ℝ)) ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 4 * (d : ℝ))
    field_simp [hNne, h4dne]
  have hprod : (8 * (d : ℝ))⁻¹ = (1 / 2) * (4 * (d : ℝ))⁻¹ := by
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    field_simp [hdne]
    ring
  have hhalf' : (1 : ℝ) / 2 ≤ 1 - ((n : ℝ) ^ d)⁻¹ := by linarith
  have hstep : (8 * (d : ℝ))⁻¹ ≤ (1 - ((n : ℝ) ^ d)⁻¹) * (4 * (d : ℝ))⁻¹ := by
    have h4dinv : (0 : ℝ) < (4 * (d : ℝ))⁻¹ :=
      inv_pos.mpr (mul_pos (by norm_num) hdR)
    calc (8 * (d : ℝ))⁻¹ = (1 / 2) * (4 * (d : ℝ))⁻¹ := hprod
      _ ≤ (1 - ((n : ℝ) ^ d)⁻¹) * (4 * (d : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hhalf' h4dinv.le
  rw [hcomp] at hstep
  exact le_trans hstep (latSum1_ge hn0 hd)

theorem secular_expansion_neg {γ : ℝ} {n : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    {δ : ℝ} (hδ : 0 < δ) :
    secular γ n d (-δ)
      = 1 / ((n : ℝ) ^ d * δ)
        + ((n : ℝ) ^ d)⁻¹ *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (γ * dispersion (waveVector n m))⁻¹)
        - δ * (((n : ℝ) ^ d)⁻¹ *
            ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (γ * dispersion (waveVector n m) *
                (γ * dispersion (waveVector n m) + δ))⁻¹) := by
  have hexp := secular_expansion (d := d) (γ := γ) hγ hn (E := -δ) (by linarith)
  have hthird : (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
        (-δ) / (γ * dispersion (waveVector n m) *
          (γ * dispersion (waveVector n m) - (-δ))))
      = -δ * (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (γ * dispersion (waveVector n m) *
            (γ * dispersion (waveVector n m) + δ))⁻¹) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [show γ * dispersion (waveVector n m) - (-δ)
        = γ * dispersion (waveVector n m) + δ by ring]
    rw [div_eq_mul_inv]
  have hneg : -1 / ((n : ℝ) ^ d * (-δ)) = 1 / ((n : ℝ) ^ d * δ) := by
    rw [show (n : ℝ) ^ d * (-δ) = -((n : ℝ) ^ d * δ) by ring]
    exact neg_div_neg_eq 1 ((n : ℝ) ^ d * δ)
  rw [hneg] at hexp
  rw [hexp, hthird]
  ring

theorem crit_root_identity {n : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ)
    (hF : secular (latSum1 n d) n d (-δ) = 1) :
    δ ^ 2 * (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m) *
        (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹) = 1 := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hγ : 0 < latSum1 n d := latSum1_pos hn hd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  set N : ℝ := (n : ℝ) ^ d with hNdef
  set S1 : ℝ := ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m))⁻¹ with hS1
  set S3 : ℝ := ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m) *
        (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹ with hS3
  have hexp : secular (latSum1 n d) n d (-δ) = 1 / (N * δ) + N⁻¹ * S1 - δ * (N⁻¹ * S3) := by
    rw [hNdef, hS1, hS3]
    exact secular_expansion_neg hγ hn0 hδ
  have hT : N⁻¹ * S1 = 1 := by
    have hsum : S1 = (latSum1 n d)⁻¹ *
        (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
          (dispersion (waveVector n m))⁻¹) := by
      rw [hS1, Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m _
      rw [mul_inv]
    calc N⁻¹ * S1 = N⁻¹ * ((latSum1 n d)⁻¹ *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (dispersion (waveVector n m))⁻¹)) := by rw [hsum]
      _ = (latSum1 n d)⁻¹ * (N⁻¹ *
            (∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
              (dispersion (waveVector n m))⁻¹)) := by ring
      _ = (latSum1 n d)⁻¹ * latSum1 n d := by
          congr 1
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hγ)
  rw [hexp, hT] at hF
  have hδX : δ * (N⁻¹ * S3) = 1 / (N * δ) := by linarith
  have hNX : N * (N⁻¹ * S3) = S3 := by
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
  have h3 : (N * δ) * (δ * (N⁻¹ * S3)) = 1 := by
    rw [hδX]
    exact mul_one_div_cancel (ne_of_gt (mul_pos hNpos hδ))
  have hL : (N * δ) * (δ * (N⁻¹ * S3)) = δ ^ 2 * S3 := by
    calc (N * δ) * (δ * (N⁻¹ * S3)) = δ ^ 2 * (N * (N⁻¹ * S3)) := by ring
      _ = δ ^ 2 * S3 := by rw [hNX]
  rw [hL] at h3
  exact h3

theorem crit_root_lower {n : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ)
    (hF : secular (latSum1 n d) n d (-δ) = 1) :
    latSum1 n d / Real.sqrt (latSum2 n d * (n : ℝ) ^ d) ≤ δ := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hγ : 0 < latSum1 n d := latSum1_pos hn hd
  have hI2 : 0 < latSum2 n d := latSum2_pos hn hd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hγpos : 0 < latSum1 n d ^ 2 := pow_pos hγ 2
  set S3 : ℝ := ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m) *
        (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹ with hS3
  have hid : δ ^ 2 * S3 = 1 := by
    rw [hS3]
    exact crit_root_identity hn hd hδ hF
  have hpt : ∀ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m) *
        (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹
        ≤ (latSum1 n d * dispersion (waveVector n m))⁻¹ ^ 2 := by
    intro m hm
    have hd0 : 0 < dispersion (waveVector n m) :=
      dispersion_waveVector_pos hn0 (Finset.mem_erase.mp hm).1
    have ha : (0 : ℝ) < latSum1 n d * dispersion (waveVector n m) := mul_pos hγ hd0
    have hle : (latSum1 n d * dispersion (waveVector n m)) ^ 2
        ≤ latSum1 n d * dispersion (waveVector n m) *
          (latSum1 n d * dispersion (waveVector n m) + δ) := by
      nlinarith [mul_pos ha hδ]
    calc (latSum1 n d * dispersion (waveVector n m) *
          (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹
        ≤ ((latSum1 n d * dispersion (waveVector n m)) ^ 2)⁻¹ :=
          inv_anti₀ (pow_pos ha 2) hle
      _ = (latSum1 n d * dispersion (waveVector n m))⁻¹ ^ 2 := (inv_pow _ 2).symm
  have hsum1 : S3 ≤ ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m))⁻¹ ^ 2 :=
    Finset.sum_le_sum hpt
  have hsum2 : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m))⁻¹ ^ 2
        = (latSum1 n d)⁻¹ ^ 2 *
          ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
            (dispersion (waveVector n m))⁻¹ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m _
    rw [mul_inv, mul_pow]
  have hT : ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (dispersion (waveVector n m))⁻¹ ^ 2 = (n : ℝ) ^ d * latSum2 n d := by
    unfold latSum2
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul]
  have hfin : S3 ≤ (n : ℝ) ^ d * latSum2 n d / latSum1 n d ^ 2 := by
    have h := le_trans hsum1 (le_of_eq hsum2)
    rw [hT] at h
    calc S3 ≤ (latSum1 n d)⁻¹ ^ 2 * ((n : ℝ) ^ d * latSum2 n d) := h
      _ = (n : ℝ) ^ d * latSum2 n d / latSum1 n d ^ 2 := by
          rw [inv_pow, div_eq_mul_inv]
          ring
  have hkey : 1 ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d / latSum1 n d ^ 2) := by
    calc (1 : ℝ) = δ ^ 2 * S3 := hid.symm
      _ ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d / latSum1 n d ^ 2) :=
          mul_le_mul_of_nonneg_left hfin (sq_nonneg δ)
  have hkey2 : latSum1 n d ^ 2 ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d) := by
    have h1 : 1 ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d) / latSum1 n d ^ 2 := by
      calc (1 : ℝ) ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d / latSum1 n d ^ 2) := hkey
        _ = δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d) / latSum1 n d ^ 2 := by ring
    have h2 := (le_div_iff₀ hγpos).mp h1
    simpa using h2
  have hNI : 0 < latSum2 n d * (n : ℝ) ^ d := mul_pos hI2 hNpos
  rw [div_le_iff₀ (Real.sqrt_pos.mpr hNI)]
  have hsq : latSum1 n d ^ 2 ≤ (δ * Real.sqrt (latSum2 n d * (n : ℝ) ^ d)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hNI.le]
    calc latSum1 n d ^ 2 ≤ δ ^ 2 * ((n : ℝ) ^ d * latSum2 n d) := hkey2
      _ = δ ^ 2 * (latSum2 n d * (n : ℝ) ^ d) := by ring
  have hmono := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hγ.le,
    Real.sqrt_sq (mul_nonneg hδ.le (Real.sqrt_nonneg _))] at hmono
  exact hmono

theorem crit_root_upper {n : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d)
    {δ : ℝ} (hδ : 0 < δ)
    (hF : secular (latSum1 n d) n d (-δ) = 1) :
    δ ≤ 8 * (d : ℝ) * latSum1 n d := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hγ : 0 < latSum1 n d := latSum1_pos hn hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  set S3 : ℝ := ∑ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (latSum1 n d * dispersion (waveVector n m) *
        (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹ with hS3
  have hid : δ ^ 2 * S3 = 1 := by
    rw [hS3]
    exact crit_root_identity hn hd hδ hF
  set A : ℝ := 4 * (d : ℝ) * latSum1 n d with hAdef
  have hA : 0 < A := by rw [hAdef]; exact mul_pos (mul_pos (by norm_num) hdR) hγ
  have hpt : ∀ m ∈ (Finset.univ.erase (0 : Fin d → ZMod n)),
      (A * (A + δ))⁻¹
        ≤ (latSum1 n d * dispersion (waveVector n m) *
            (latSum1 n d * dispersion (waveVector n m) + δ))⁻¹ := by
    intro m hm
    have hd0 : 0 < dispersion (waveVector n m) :=
      dispersion_waveVector_pos hn0 (Finset.mem_erase.mp hm).1
    have ha : (0 : ℝ) < latSum1 n d * dispersion (waveVector n m) := mul_pos hγ hd0
    have hale : latSum1 n d * dispersion (waveVector n m) ≤ A := by
      have h := dispersion_le_four_mul (waveVector n m)
      have h1 := mul_le_mul_of_nonneg_left h hγ.le
      calc latSum1 n d * dispersion (waveVector n m) ≤ latSum1 n d * (4 * (d : ℝ)) := h1
        _ = A := by rw [hAdef]; ring
    have hprod : latSum1 n d * dispersion (waveVector n m) *
          (latSum1 n d * dispersion (waveVector n m) + δ) ≤ A * (A + δ) :=
      mul_le_mul hale (by linarith) (by linarith) hA.le
    exact inv_anti₀ (mul_pos ha (by linarith)) hprod
  have hcard : ((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹ ≤ S3 := by
    have hsum : ((Finset.univ : Finset (Fin d → ZMod n)).erase
        (0 : Fin d → ZMod n)).card * (A * (A + δ))⁻¹ ≤ S3 := by
      have h := Finset.sum_le_sum hpt
      have hc : ∑ _m ∈ (Finset.univ : Finset (Fin d → ZMod n)).erase
          (0 : Fin d → ZMod n), (A * (A + δ))⁻¹
          = (((Finset.univ : Finset (Fin d → ZMod n)).erase
              (0 : Fin d → ZMod n)).card : ℝ) * (A * (A + δ))⁻¹ := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hc] at h
      simpa only [hS3] using h
    have hcardval : (((Finset.univ : Finset (Fin d → ZMod n)).erase
        (0 : Fin d → ZMod n)).card : ℝ) = (n : ℝ) ^ d - 1 := by
      have h1 : ((Finset.univ : Finset (Fin d → ZMod n)).erase
          (0 : Fin d → ZMod n)).card = n ^ d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        have hc : Fintype.card (Fin d → ZMod n) = n ^ d := by simp
        rw [hc]
      have hle : (1 : ℕ) ≤ n ^ d := Nat.one_le_pow d n hn0
      rw [h1, Nat.cast_sub hle]
      push_cast
      ring
    rw [hcardval] at hsum
    exact hsum
  have hmain : δ ^ 2 * ((n : ℝ) ^ d - 1) ≤ A * (A + δ) := by
    have h1 : δ ^ 2 * ((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹ ≤ 1 := by
      have h2 : δ ^ 2 * ((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹
          = δ ^ 2 * (((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹) := by ring
      rw [h2]
      calc δ ^ 2 * (((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹) ≤ δ ^ 2 * S3 :=
            mul_le_mul_of_nonneg_left hcard (sq_nonneg δ)
        _ = 1 := hid
    have hApos : 0 < A * (A + δ) := mul_pos hA (by linarith)
    calc δ ^ 2 * ((n : ℝ) ^ d - 1)
        = (δ ^ 2 * ((n : ℝ) ^ d - 1) * (A * (A + δ))⁻¹) * (A * (A + δ)) := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hApos), mul_one]
      _ ≤ 1 * (A * (A + δ)) := mul_le_mul_of_nonneg_right h1 hApos.le
      _ = A * (A + δ) := one_mul _
  have hNge : (1 : ℝ) ≤ (n : ℝ) ^ d - 1 := by
    have h2 : (2 : ℝ) ≤ (n : ℝ) ^ d := by
      have h2n : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      calc (2 : ℝ) ≤ (n : ℝ) := h2n
        _ = (n : ℝ) ^ 1 := by rw [pow_one]
        _ ≤ (n : ℝ) ^ d := pow_le_pow_right₀ (by linarith) hd
    linarith
  have hδsq : δ ^ 2 ≤ A * (A + δ) := by
    have h1 : δ ^ 2 ≤ δ ^ 2 * ((n : ℝ) ^ d - 1) := by
      nlinarith [hδ, hNge, sq_nonneg δ]
    linarith [hmain]
  have hgoal : 8 * (d : ℝ) * latSum1 n d = 2 * A := by rw [hAdef]; ring
  rw [hgoal]
  by_contra hcon
  rw [not_le] at hcon
  have h1 : 0 < δ - 2 * A := by linarith
  have h2 : 0 < (δ - 2 * A) * δ := mul_pos h1 hδ
  have h3 : 0 < A * (δ - 2 * A) := mul_pos hA h1
  have h4 : 0 < A * (δ - A) := mul_pos hA (by linarith)
  nlinarith [h2, h3, h4, hδsq]

theorem crit_time_upper {n d : ℕ} [NeZero n] (hn : 1 < n) (hd : 0 < d) {C δ : ℝ}
    (hδ : 0 < δ)
    (hF : secular (latSum1 n d) n d (-δ) = 1)
    (hI2 : latSum2 n d ≤ C) :
    Real.pi / (2 * δ) ≤ 4 * Real.pi * (d : ℝ) * Real.sqrt (C * (n : ℝ) ^ d) := by
  have hn0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have hγ : 0 < latSum1 n d := latSum1_pos hn hd
  have hI2pos : 0 < latSum2 n d := latSum2_pos hn hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hNpos : (0 : ℝ) < (n : ℝ) ^ d := pow_pos hnR d
  have hγlow : (8 * (d : ℝ))⁻¹ ≤ latSum1 n d := latSum1_ge_eighth hn hd
  have h8d : (0 : ℝ) < 8 * (d : ℝ) := by positivity
  have hsqrtpos : 0 < Real.sqrt (latSum2 n d * (n : ℝ) ^ d) :=
    Real.sqrt_pos.mpr (mul_pos hI2pos hNpos)
  have hlow := crit_root_lower (d := d) hn hd hδ hF
  have h1 : 1 / δ ≤ Real.sqrt (latSum2 n d * (n : ℝ) ^ d) / latSum1 n d := by
    have hpos : (0 : ℝ) < latSum1 n d / Real.sqrt (latSum2 n d * (n : ℝ) ^ d) :=
      div_pos hγ hsqrtpos
    have h := one_div_le_one_div_of_le hpos hlow
    simpa [one_div, inv_div] using h
  have hinv : (latSum1 n d)⁻¹ ≤ 8 * (d : ℝ) := by
    have h := inv_anti₀ (inv_pos.mpr h8d) hγlow
    simpa using h
  have h2 : Real.sqrt (latSum2 n d * (n : ℝ) ^ d) / latSum1 n d
      ≤ 8 * (d : ℝ) * Real.sqrt (latSum2 n d * (n : ℝ) ^ d) := by
    rw [div_eq_mul_inv]
    calc Real.sqrt (latSum2 n d * (n : ℝ) ^ d) * (latSum1 n d)⁻¹
        ≤ Real.sqrt (latSum2 n d * (n : ℝ) ^ d) * (8 * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left hinv (Real.sqrt_nonneg _)
      _ = 8 * (d : ℝ) * Real.sqrt (latSum2 n d * (n : ℝ) ^ d) := by ring
  have h3 : Real.sqrt (latSum2 n d * (n : ℝ) ^ d) ≤ Real.sqrt (C * (n : ℝ) ^ d) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_right hI2 hNpos.le
  have h4 : 8 * (d : ℝ) * Real.sqrt (latSum2 n d * (n : ℝ) ^ d)
      ≤ 8 * (d : ℝ) * Real.sqrt (C * (n : ℝ) ^ d) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h5 : 1 / δ ≤ 8 * (d : ℝ) * Real.sqrt (C * (n : ℝ) ^ d) :=
    le_trans h1 (le_trans h2 h4)
  have hpi : Real.pi / (2 * δ) = (Real.pi / 2) * (1 / δ) := by
    rw [div_eq_mul_inv, mul_inv]
    ring
  calc Real.pi / (2 * δ) = (Real.pi / 2) * (1 / δ) := hpi
    _ ≤ (Real.pi / 2) * (8 * (d : ℝ) * Real.sqrt (C * (n : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = 4 * Real.pi * (d : ℝ) * Real.sqrt (C * (n : ℝ) ^ d) := by ring_nf

theorem crit_time_upper_d5 {n : ℕ} [NeZero n] [NeZero d] (hn : 1 < n) (hd : 5 ≤ d)
    {δ : ℝ} (hδ : 0 < δ)
    (hF : secular (latSum1 n d) n d (-δ) = 1) :
    Real.pi / (2 * δ) ≤
      4 * Real.pi * (d : ℝ) * Real.sqrt (((4 * 3 ^ d + 1) / 256) * (n : ℝ) ^ d) :=
  crit_time_upper hn (by omega) hδ hF
    (latSum2_le (d := d) (Nat.lt_trans Nat.zero_lt_one hn) hd)

theorem crit_time_upper_d4 {n : ℕ} [NeZero n] (hn : 1 < n) {δ : ℝ} (hδ : 0 < δ)
    (hF : secular (latSum1 n 4) n 4 (-δ) = 1) :
    Real.pi / (2 * δ) ≤
      16 * Real.pi * Real.sqrt (((81 / 64) * (1 + Real.log (n : ℝ)) + 1 / 256) *
        (n : ℝ) ^ 4) := by
  have h := crit_time_upper (d := 4) hn (by norm_num) hδ hF
    (latSum2_le_log (Nat.lt_trans Nat.zero_lt_one hn))
  calc Real.pi / (2 * δ)
      ≤ 4 * Real.pi * ((4 : ℕ) : ℝ) *
          Real.sqrt (((81 / 64) * (1 + Real.log (n : ℝ)) + 1 / 256) * (n : ℝ) ^ 4) := h
    _ = 16 * Real.pi *
          Real.sqrt (((81 / 64) * (1 + Real.log (n : ℝ)) + 1 / 256) * (n : ℝ) ^ 4) := by
        push_cast
        ring

end Qatlib.Papers.SpatialSearch03.MainResults
