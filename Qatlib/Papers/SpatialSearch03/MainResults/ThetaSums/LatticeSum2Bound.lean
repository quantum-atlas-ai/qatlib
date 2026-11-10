/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatticeSumBound
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

def gfour (s : ℕ) : ℝ := ((s : ℝ))⁻¹ ^ 4

def dfour (s : ℕ) : ℝ := gfour s - gfour (s + 1)

theorem gfour_nonneg (s : ℕ) : 0 ≤ gfour s := by unfold gfour; positivity

theorem telescope4 {r n : ℕ} (hrn : r ≤ n) :
    ∑ s ∈ Finset.Icc r n, dfour s = gfour r - gfour (n + 1) := by
  have h := Finset.sum_Icc_sub (f := gfour) hrn
  calc ∑ s ∈ Finset.Icc r n, dfour s
      = ∑ s ∈ Finset.Icc r n, (-(gfour (s + 1) - gfour s)) := by
        refine Finset.sum_congr rfl ?_
        intro s _
        unfold dfour
        ring
    _ = -(∑ s ∈ Finset.Icc r n, (gfour (s + 1) - gfour s)) := by
        rw [Finset.sum_neg_distrib]
    _ = -(gfour (n + 1) - gfour r) := by rw [h]
    _ = gfour r - gfour (n + 1) := by ring

theorem dfour_le (s : ℕ) (hs : 1 ≤ s) : dfour s ≤ 4 / (s : ℝ) ^ 5 := by
  have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs
  have h1 : (0:ℝ) < (s:ℝ) + 1 := by linarith
  have hcast : ((s + 1 : ℕ) : ℝ) = (s:ℝ) + 1 := by push_cast; ring
  have hpoly : (s:ℝ) * (4 * (s:ℝ)^3 + 6 * (s:ℝ)^2 + 4 * (s:ℝ) + 1)
      ≤ 4 * ((s:ℝ) + 1)^4 := by
    nlinarith [sq_nonneg ((s:ℝ) - 1), sq_nonneg (s:ℝ), sq_nonneg ((s:ℝ) + 1),
      sq_nonneg ((s:ℝ)^2 - 1), sq_nonneg ((s:ℝ)^2 + (s:ℝ))]
  have hnum : ((s:ℝ) + 1)^4 - (s:ℝ)^4 = 4 * (s:ℝ)^3 + 6 * (s:ℝ)^2 + 4 * (s:ℝ) + 1 := by ring
  have hsne : (s:ℝ) ≠ 0 := ne_of_gt hsR
  have h1ne : ((s:ℝ) + 1) ≠ 0 := ne_of_gt h1
  have hval : (((s:ℝ)^4)⁻¹ - (((s:ℝ)+1)^4)⁻¹) * (s:ℝ)^5
      = (s:ℝ) * (4 * (s:ℝ)^3 + 6 * (s:ℝ)^2 + 4 * (s:ℝ) + 1) / ((s:ℝ)+1)^4 := by
    have hnum' : ((s:ℝ)+1)^4 - (s:ℝ)^4 = 4 * (s:ℝ)^3 + 6 * (s:ℝ)^2 + 4 * (s:ℝ) + 1 := hnum
    field_simp
    ring
  unfold dfour gfour
  rw [hcast, inv_pow, inv_pow, le_div_iff₀ (by positivity : (0:ℝ) < (s:ℝ)^5)]
  rw [hval]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((s:ℝ)+1)^4)]
  calc (s:ℝ) * (4 * (s:ℝ)^3 + 6 * (s:ℝ)^2 + 4 * (s:ℝ) + 1)
      ≤ 4 * ((s:ℝ) + 1)^4 := hpoly
    _ = 4 * ((s:ℝ) + 1)^4 := rfl

theorem latSum2_le {n d : ℕ} [NeZero n] [NeZero d] (hn : 0 < n) (hd : 5 ≤ d) :
    latSum2 n d ≤ (4 * 3 ^ d + 1) / 256 := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set S := (Finset.univ : Finset (Fin d → ZMod n)).erase (0 : Fin d → ZMod n) with hS
  have hinv : ∑ m ∈ S, (dispersion (waveVector n m))⁻¹ ^ 2
      ≤ ((n:ℝ)^4/256) * ∑ m ∈ S, gfour (maxNorm n m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hr : (0:ℝ) < (maxNorm n m : ℝ) := by
      have h1 : (1:ℕ) ≤ maxNorm n m := maxNorm_pos_of_ne_zero hm0
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have h := inv_dispersion_le (d := d) hn hm0
    have hnn : (0:ℝ) ≤ (dispersion (waveVector n m))⁻¹ := inv_nonneg.2 (dispersion_nonneg _)
    have hsq : (dispersion (waveVector n m))⁻¹ ^ 2
        ≤ ((n:ℝ)^2/(16 * ((maxNorm n m:ℝ))^2))^2 := pow_le_pow_left₀ hnn h 2
    have heq : ((n:ℝ)^2/(16 * ((maxNorm n m:ℝ))^2))^2
        = ((n:ℝ)^4/256) * gfour (maxNorm n m) := by
      unfold gfour
      field_simp [hr.ne']
      ring
    rwa [heq] at hsq
  have hbase : ∀ m ∈ S, gfour (maxNorm n m)
      = (∑ s ∈ Finset.Icc 1 n, if maxNorm n m ≤ s then dfour s else 0) + gfour (n+1) := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hr1 : 1 ≤ maxNorm n m := maxNorm_pos_of_ne_zero hm0
    have hrn : maxNorm n m ≤ n := maxNorm_le_n m
    have htel := telescope4 (n := n) (r := maxNorm n m) hrn
    have hI : Finset.Icc (maxNorm n m) n
        = (Finset.Icc 1 n).filter (fun s => maxNorm n m ≤ s) := by
      ext s
      simp only [Finset.mem_Icc, Finset.mem_filter]
      omega
    rw [hI, Finset.sum_filter] at htel
    linarith
  have hlayer : ∑ m ∈ S, gfour (maxNorm n m)
      = (∑ s ∈ Finset.Icc 1 n,
          dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
        + (S.card : ℝ) * gfour (n+1) := by
    have hinner : ∀ s ∈ Finset.Icc 1 n,
        ∑ m ∈ S, (if maxNorm n m ≤ s then dfour s else 0)
          = dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) := by
      intro s _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      ring
    calc ∑ m ∈ S, gfour (maxNorm n m)
        = ∑ m ∈ S, ((∑ s ∈ Finset.Icc 1 n, if maxNorm n m ≤ s then dfour s else 0)
            + gfour (n+1)) := Finset.sum_congr rfl hbase
      _ = (∑ m ∈ S, ∑ s ∈ Finset.Icc 1 n,
            if maxNorm n m ≤ s then dfour s else 0) + ∑ m ∈ S, gfour (n+1) :=
          Finset.sum_add_distrib
      _ = (∑ s ∈ Finset.Icc 1 n, ∑ m ∈ S,
            if maxNorm n m ≤ s then dfour s else 0) + ∑ m ∈ S, gfour (n+1) := by
          rw [Finset.sum_comm]
      _ = (∑ s ∈ Finset.Icc 1 n,
            dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
          + (S.card : ℝ) * gfour (n+1) := by
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
      dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ 4 * 3^d * (n:ℝ)^(d-5) := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsn : s ≤ n := (Finset.mem_Icc.mp hs).2
    have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs1
    have hdle : dfour s ≤ 4 / (s:ℝ)^5 := dfour_le s hs1
    have hcoe : (0:ℝ) ≤ 4 / (s:ℝ)^5 := by positivity
    have hcard := hcard_bound s hs
    have hcardnn : (0:ℝ) ≤ ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) := by positivity
    have hstep1 : dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (4 / (s:ℝ)^5) * (3^d * (s:ℝ)^d) := mul_le_mul hdle hcard hcardnn hcoe
    have heq : (4 / (s:ℝ)^5) * (3^d * (s:ℝ)^d) = 4 * 3^d * (s:ℝ)^(d-5) := by
      have hsub : (s:ℝ)^(d-5) = (s:ℝ)^d * ((s:ℝ)^5)⁻¹ := pow_sub₀ (s:ℝ) hsR.ne' hd
      calc (4 / (s:ℝ)^5) * (3^d * (s:ℝ)^d)
          = 4 * ((s:ℝ)^5)⁻¹ * (3^d * (s:ℝ)^d) := by rw [div_eq_mul_inv]
        _ = (4 * 3^d) * ((s:ℝ)^d * ((s:ℝ)^5)⁻¹) := by ring
        _ = 4 * 3^d * (s:ℝ)^(d-5) := by rw [← hsub]
    have hsle : (s:ℝ) ≤ (n:ℝ) := by exact_mod_cast hsn
    have hpowle : (s:ℝ)^(d-5) ≤ (n:ℝ)^(d-5) := pow_le_pow_left₀ (by positivity) hsle (d-5)
    have hfin : 4 * 3^d * (s:ℝ)^(d-5) ≤ 4 * 3^d * (n:ℝ)^(d-5) :=
      mul_le_mul_of_nonneg_left hpowle (by positivity)
    calc dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (4 / (s:ℝ)^5) * (3^d * (s:ℝ)^d) := hstep1
      _ = 4 * 3^d * (s:ℝ)^(d-5) := heq
      _ ≤ 4 * 3^d * (n:ℝ)^(d-5) := hfin
  have hsumterm : ∑ s ∈ Finset.Icc 1 n,
      dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (n:ℝ) * (4 * 3^d * (n:ℝ)^(d-5)) := by
    calc ∑ s ∈ Finset.Icc 1 n,
        dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ ∑ _s ∈ Finset.Icc 1 n, (4 * 3^d * (n:ℝ)^(d-5)) := Finset.sum_le_sum hterm
      _ = (n:ℝ) * (4 * 3^d * (n:ℝ)^(d-5)) := by
          rw [Finset.sum_const, nsmul_eq_mul, Nat.card_Icc]
          have hsub : n + 1 - 1 = n := by omega
          rw [hsub]
  have htail : (S.card : ℝ) * gfour (n + 1) ≤ (n:ℝ)^(d-4) := by
    have hScard : (S.card : ℝ) ≤ (n:ℝ)^d := by
      have h1 : S.card ≤ (Finset.univ : Finset (Fin d → ZMod n)).card := Finset.card_erase_le
      have h2 : (Finset.univ : Finset (Fin d → ZMod n)).card = n^d := by simp
      have h3 : S.card ≤ n^d := by rw [← h2]; exact h1
      exact_mod_cast h3
    have hgfour : gfour (n + 1) ≤ 1 / (n:ℝ)^4 := by
      unfold gfour
      have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
      rw [hcast]
      have hinv : ((n:ℝ)+1)⁻¹ ≤ (n:ℝ)⁻¹ := inv_anti₀ hnR (by linarith)
      have hnn : (0:ℝ) ≤ ((n:ℝ)+1)⁻¹ := by positivity
      have h2 : ((n:ℝ)+1)⁻¹ ^ 4 ≤ ((n:ℝ)⁻¹)^4 := pow_le_pow_left₀ hnn hinv 4
      have heq : ((n:ℝ)⁻¹)^4 = 1/(n:ℝ)^4 := by field_simp
      rwa [heq] at h2
    calc (S.card : ℝ) * gfour (n+1) ≤ (n:ℝ)^d * (1/(n:ℝ)^4) :=
          mul_le_mul hScard hgfour (gfour_nonneg (n+1)) (by positivity)
      _ = (n:ℝ)^(d-4) := by
          rw [pow_sub₀ (n:ℝ) hnR.ne' (by omega : 4 ≤ d), one_div]
  have hmain : ∑ m ∈ S, gfour (maxNorm n m) ≤ (4 * 3^d + 1) * (n:ℝ)^(d-4) := by
    rw [hlayer]
    have h1 : (n:ℝ) * (4 * 3^d * (n:ℝ)^(d-5)) = 4 * 3^d * (n:ℝ)^(d-4) := by
      have hd2 : d - 4 = (d - 5) + 1 := by omega
      rw [hd2, pow_succ']
      ring
    calc (∑ s ∈ Finset.Icc 1 n,
          dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ))
          + (S.card : ℝ) * gfour (n+1)
        ≤ (n:ℝ) * (4 * 3^d * (n:ℝ)^(d-5)) + (n:ℝ)^(d-4) := add_le_add hsumterm htail
      _ = 4 * 3^d * (n:ℝ)^(d-4) + (n:ℝ)^(d-4) := by rw [h1]
      _ = (4 * 3^d + 1) * (n:ℝ)^(d-4) := by ring
  have hid : ((n:ℝ)^d)⁻¹ * (((n:ℝ)^4/256) * ((4 * 3^d + 1) * (n:ℝ)^(d-4)))
      = (4 * 3^d + 1)/256 := by
    have hpow : ((n:ℝ)^d) = ((n:ℝ)^4) * ((n:ℝ)^(d-4)) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow]
    field_simp
  calc latSum2 n d
      = ((n:ℝ)^d)⁻¹ * ∑ m ∈ S, (dispersion (waveVector n m))⁻¹ ^ 2 := by rw [latSum2, ← hS]
    _ ≤ ((n:ℝ)^d)⁻¹ * (((n:ℝ)^4/256) * ∑ m ∈ S, gfour (maxNorm n m)) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
    _ ≤ ((n:ℝ)^d)⁻¹ * (((n:ℝ)^4/256) * ((4 * 3^d + 1) * (n:ℝ)^(d-4))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity)
    _ = (4 * 3^d + 1)/256 := hid

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
