/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.SecularLowerBound
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

theorem latSum1_le {n d : ℕ} [NeZero n] [NeZero d] (hn : 0 < n) (hd : 3 ≤ d) :
    latSum1 n d ≤ (3 ^ (d + 1) + 1) / 16 := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set S := (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n) with hS

  have hinv : ∑ m ∈ S, (dispersion (waveVector n m))⁻¹
      ≤ ((n:ℝ)^2/16) * ∑ m ∈ S, gfun (maxNorm n m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hr : (0:ℝ) < (maxNorm n m : ℝ) := by
      have h1 : (1:ℕ) ≤ maxNorm n m := maxNorm_pos_of_ne_zero hm0
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have h := inv_dispersion_le (d := d) hn hm0
    have heq : (n:ℝ)^2/(16 * ((maxNorm n m:ℝ))^2) = ((n:ℝ)^2/16) * gfun (maxNorm n m) := by
      unfold gfun
      field_simp [hr.ne']
    rwa [heq] at h

  have hbase : ∀ m ∈ S, gfun (maxNorm n m)
      = (∑ s ∈ Finset.Icc 1 n, if maxNorm n m ≤ s then dfun s else 0) + gfun (n+1) := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hr1 : 1 ≤ maxNorm n m := maxNorm_pos_of_ne_zero hm0
    have hrn : maxNorm n m ≤ n := maxNorm_le_n m
    have htel := telescope (n := n) (r := maxNorm n m) hrn
    have hI : Finset.Icc (maxNorm n m) n
        = (Finset.Icc 1 n).filter (fun s => maxNorm n m ≤ s) := by
      ext s
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega
    rw [hI, Finset.sum_filter] at htel
    linarith
  have hlayer : ∑ m ∈ S, gfun (maxNorm n m)
      = (∑ s ∈ Finset.Icc 1 n,
          dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
        + (S.card : ℝ) * gfun (n+1) := by
    have hinner : ∀ s ∈ Finset.Icc 1 n,
        ∑ m ∈ S, (if maxNorm n m ≤ s then dfun s else 0)
          = dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) := by
      intro s _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    calc ∑ m ∈ S, gfun (maxNorm n m)
        = ∑ m ∈ S, ((∑ s ∈ Finset.Icc 1 n, if maxNorm n m ≤ s then dfun s else 0)
            + gfun (n+1)) := Finset.sum_congr rfl hbase
      _ = (∑ m ∈ S, ∑ s ∈ Finset.Icc 1 n,
            if maxNorm n m ≤ s then dfun s else 0) + ∑ m ∈ S, gfun (n+1) :=
          Finset.sum_add_distrib
      _ = (∑ s ∈ Finset.Icc 1 n, ∑ m ∈ S,
            if maxNorm n m ≤ s then dfun s else 0) + ∑ m ∈ S, gfun (n+1) := by
          rw [Finset.sum_comm]
      _ = (∑ s ∈ Finset.Icc 1 n,
            dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
          + (S.card : ℝ) * gfun (n+1) := by
          rw [Finset.sum_congr rfl hinner, Finset.sum_const, nsmul_eq_mul]

  have hcard_bound : ∀ s ∈ Finset.Icc 1 n,
      ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) ≤ 3^d * (s:ℝ)^d := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsub : S.filter (fun m => maxNorm n m ≤ s)
        ⊆ Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ] at hm ⊢
      exact ⟨trivial, hm.2⟩
    have hc : (S.filter (fun m => maxNorm n m ≤ s)).card
        ≤ (Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s)).card :=
      Finset.card_le_card hsub
    have hbox := card_le_box (d := d) (n := n) s
    have hcast : (((2 * s + 1) ^ d : ℕ) : ℝ) = (2 * (s:ℝ) + 1)^d := by
      push_cast
      ring
    have hsle : (2:ℝ) * (s:ℝ) + 1 ≤ 3 * (s:ℝ) := by
      have hs1R : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
      linarith
    have hbase2 : (2 * (s:ℝ) + 1)^d ≤ (3 * (s:ℝ))^d := pow_le_pow_left₀ (by positivity) hsle d
    have hmul : (3 * (s:ℝ))^d = 3^d * (s:ℝ)^d := by rw [mul_pow]
    calc ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ ((Finset.univ.filter (fun m : Fin d → ZMod n => maxNorm n m ≤ s)).card : ℝ) := by
          exact_mod_cast hc
      _ ≤ (((2 * s + 1) ^ d : ℕ) : ℝ) := by exact_mod_cast hbox
      _ = (2 * (s:ℝ) + 1)^d := hcast
      _ ≤ (3 * (s:ℝ))^d := hbase2
      _ = 3^d * (s:ℝ)^d := hmul
  have hterm : ∀ s ∈ Finset.Icc 1 n,
      dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ 3^(d+1) * (n:ℝ)^(d-3) := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsn : s ≤ n := (Finset.mem_Icc.mp hs).2
    have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs1
    have hdle : dfun s ≤ 3 / (s:ℝ)^3 := dfun_le s hs1
    have hcoe : (0:ℝ) ≤ 3 / (s:ℝ)^3 := by positivity
    have hcard := hcard_bound s hs
    have hcardnn : (0:ℝ) ≤ ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) := by positivity
    have hstep1 : dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (3 / (s:ℝ)^3) * (3^d * (s:ℝ)^d) := mul_le_mul hdle hcard hcardnn hcoe
    have heq : (3 / (s:ℝ)^3) * (3^d * (s:ℝ)^d) = 3^(d+1) * (s:ℝ)^(d-3) := by
      have hsub : (s:ℝ)^(d-3) = (s:ℝ)^d * ((s:ℝ)^3)⁻¹ := pow_sub₀ (s:ℝ) hsR.ne' hd
      calc (3 / (s:ℝ)^3) * (3^d * (s:ℝ)^d)
          = 3 * ((s:ℝ)^3)⁻¹ * (3^d * (s:ℝ)^d) := by rw [div_eq_mul_inv]
        _ = (3 * 3^d) * ((s:ℝ)^d * ((s:ℝ)^3)⁻¹) := by ring
        _ = 3^(d+1) * (s:ℝ)^(d-3) := by
            rw [← hsub, mul_comm 3 (3^d), ← pow_succ]
    have hsle : (s:ℝ) ≤ (n:ℝ) := by exact_mod_cast hsn
    have hpowle : (s:ℝ)^(d-3) ≤ (n:ℝ)^(d-3) := pow_le_pow_left₀ (by positivity) hsle (d-3)
    have hfin : 3^(d+1) * (s:ℝ)^(d-3) ≤ 3^(d+1) * (n:ℝ)^(d-3) :=
      mul_le_mul_of_nonneg_left hpowle (by positivity)
    calc dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (3 / (s:ℝ)^3) * (3^d * (s:ℝ)^d) := hstep1
      _ = 3^(d+1) * (s:ℝ)^(d-3) := heq
      _ ≤ 3^(d+1) * (n:ℝ)^(d-3) := hfin
  have hsumterm : ∑ s ∈ Finset.Icc 1 n,
      dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (n:ℝ) * (3^(d+1) * (n:ℝ)^(d-3)) := by
    calc ∑ s ∈ Finset.Icc 1 n,
        dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ ∑ _s ∈ Finset.Icc 1 n, (3^(d+1) * (n:ℝ)^(d-3)) := Finset.sum_le_sum hterm
      _ = (n:ℝ) * (3^(d+1) * (n:ℝ)^(d-3)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          have hsub : n + 1 - 1 = n := by omega
          rw [hsub]

  have htail : (S.card : ℝ) * gfun (n + 1) ≤ (n:ℝ)^(d-2) := by
    have hScard : (S.card : ℝ) ≤ (n:ℝ)^d := by
      have h1 : S.card ≤ (Finset.univ : Finset (Fin d → ZMod n)).card := Finset.card_erase_le
      have h2 : (Finset.univ : Finset (Fin d → ZMod n)).card = n^d := by simp
      have h3 : S.card ≤ n^d := by rw [← h2]; exact h1
      exact_mod_cast h3
    have hgfun : gfun (n + 1) ≤ 1 / (n:ℝ)^2 := by
      unfold gfun
      have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hinv : ((n:ℝ)+1)⁻¹ ≤ (n:ℝ)⁻¹ := inv_anti₀ hnR (by linarith)
      have hnn : (0:ℝ) ≤ ((n:ℝ)+1)⁻¹ := by positivity
      have h2 : ((n:ℝ)+1)⁻¹ ^ 2 ≤ ((n:ℝ)⁻¹)^2 := pow_le_pow_left₀ hnn hinv 2
      have heq : ((n:ℝ)⁻¹)^2 = 1/(n:ℝ)^2 := by field_simp
      rwa [heq] at h2
    have hnn : (0:ℝ) ≤ 1/(n:ℝ)^2 := by positivity
    calc (S.card : ℝ) * gfun (n+1) ≤ (n:ℝ)^d * (1/(n:ℝ)^2) :=
          mul_le_mul hScard hgfun (gfun_nonneg (n+1)) (by positivity)
      _ = (n:ℝ)^(d-2) := by
          rw [pow_sub₀ (n:ℝ) hnR.ne' (by omega : 2 ≤ d), one_div]
  have hmain : ∑ m ∈ S, gfun (maxNorm n m) ≤ (3^(d+1) + 1) * (n:ℝ)^(d-2) := by
    rw [hlayer]
    have h1 : (n:ℝ) * (3^(d+1) * (n:ℝ)^(d-3)) = 3^(d+1) * (n:ℝ)^(d-2) := by
      have hd2 : d - 2 = (d - 3) + 1 := by omega
      rw [hd2, pow_succ']
      ring
    calc (∑ s ∈ Finset.Icc 1 n,
          dfun s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
          + (S.card : ℝ) * gfun (n+1)
        ≤ (n:ℝ) * (3^(d+1) * (n:ℝ)^(d-3)) + (n:ℝ)^(d-2) := add_le_add hsumterm htail
      _ = 3^(d+1) * (n:ℝ)^(d-2) + (n:ℝ)^(d-2) := by rw [h1]
      _ = (3^(d+1) + 1) * (n:ℝ)^(d-2) := by ring

  have hid : ((n:ℝ)^d)⁻¹ * (((n:ℝ)^2/16) * ((3^(d+1)+1) * (n:ℝ)^(d-2))) = (3^(d+1)+1)/16 := by
    have hpow : ((n:ℝ)^d) = ((n:ℝ)^2) * ((n:ℝ)^(d-2)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    field_simp
  calc latSum1 n d
      = ((n:ℝ)^d)⁻¹ * ∑ m ∈ S, (dispersion (waveVector n m))⁻¹ := by rw [latSum1, ← hS]
    _ ≤ ((n:ℝ)^d)⁻¹ * (((n:ℝ)^2/16) * ∑ m ∈ S, gfun (maxNorm n m)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ ((n:ℝ)^d)⁻¹ * (((n:ℝ)^2/16) * ((3^(d+1)+1) * (n:ℝ)^(d-2))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity)
    _ = (3^(d+1)+1)/16 := hid

theorem ground_energy_bound_d3 {n d : ℕ} [NeZero n] [NeZero d] (hn : 0 < n) (hd : 3 ≤ d)
    {E₀ : ℝ} (hE₀ : E₀ < 0)
    (hF : secular ((3 ^ (d + 1) + 1) / 16 + 1) n d E₀ = 1) :
    |E₀| ≤ ((3 ^ (d + 1) + 1) / 16 + 1) /
      ((n : ℝ) ^ d * (((3 ^ (d + 1) + 1) / 16 + 1) - latSum1 n d)) := by
  have hγ : (0:ℝ) < (3 ^ (d + 1) + 1) / 16 + 1 := by positivity
  have hL : latSum1 n d < (3 ^ (d + 1) + 1) / 16 + 1 := by
    have := latSum1_le (d := d) hn hd
    linarith
  exact ground_energy_bound hγ hn hL hE₀ hF

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
