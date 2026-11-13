/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.LatSum1Log
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Logarithmic second lattice-sum bound

This module proves an explicit logarithmic upper bound for `latSum2 n 4`. It supplies the
lattice-sum estimate at the marginal dimension four in [ChildsGoldstone2004].

## Main statements

* `latSum2_le_log`: bounds the sum by `(81 / 64) * (1 + Real.log n) + 1 / 256`.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

/-- For positive side length, the second lattice sum in dimension four is at most `(81 / 64) *
(1 + Real.log n) + 1 / 256` [ChildsGoldstone2004]. -/
theorem latSum2_le_log {n : ℕ} [NeZero n] (hn : 0 < n) :
    latSum2 n 4 ≤ (81/64) * (1 + Real.log n) + 1/256 := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  set S := (Finset.univ : Finset (Fin 4 → ZMod n)).erase (0 : Fin 4 → ZMod n) with hS
  have hinv : ∑ m ∈ S, ((dispersion (waveVector n m))⁻¹) ^ 2
      ≤ ((n:ℝ)^4/256) * ∑ m ∈ S, gfour (maxNorm n m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hr : (0:ℝ) < (maxNorm n m : ℝ) := by
      have h1 : (1:ℕ) ≤ maxNorm n m := maxNorm_pos_of_ne_zero hm0
      exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one h1
    have h := inv_dispersion_le (d := 4) hn hm0
    have hnn : (0:ℝ) ≤ (dispersion (waveVector n m))⁻¹ :=
      inv_nonneg.2 (dispersion_nonneg _)
    have hsq := pow_le_pow_left₀ hnn h 2
    have heq : ((n:ℝ)^2/(16 * ((maxNorm n m:ℝ))^2)) ^ 2
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
      ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) ≤ 81 * (s:ℝ)^4 := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsub : S.filter (fun m => maxNorm n m ≤ s)
        ⊆ Finset.univ.filter (fun m : Fin 4 → ZMod n => maxNorm n m ≤ s) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ] at hm ⊢
      exact ⟨trivial, hm.2⟩
    have hc : (S.filter (fun m => maxNorm n m ≤ s)).card
        ≤ (Finset.univ.filter (fun m : Fin 4 → ZMod n => maxNorm n m ≤ s)).card :=
      Finset.card_le_card hsub
    have hbox := card_le_box (d := 4) (n := n) s
    have hcast : (((2 * s + 1) ^ 4 : ℕ) : ℝ) = (2 * (s:ℝ) + 1)^4 := by push_cast; ring
    have hsle : (2:ℝ) * (s:ℝ) + 1 ≤ 3 * (s:ℝ) := by
      have hs1R : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs1
      linarith
    have hbase2 : (2 * (s:ℝ) + 1)^4 ≤ (3 * (s:ℝ))^4 := pow_le_pow_left₀ (by positivity) hsle 4
    have hmul : (3 * (s:ℝ))^4 = 81 * (s:ℝ)^4 := by ring
    calc ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ ((Finset.univ.filter (fun m : Fin 4 → ZMod n => maxNorm n m ≤ s)).card : ℝ) := by
          exact_mod_cast hc
      _ ≤ (((2 * s + 1) ^ 4 : ℕ) : ℝ) := by exact_mod_cast hbox
      _ = (2 * (s:ℝ) + 1)^4 := hcast
      _ ≤ (3 * (s:ℝ))^4 := hbase2
      _ = 81 * (s:ℝ)^4 := hmul
  have hterm : ∀ s ∈ Finset.Icc 1 n,
      dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) ≤ 324 / (s:ℝ) := by
    intro s hs
    have hs1 : 1 ≤ s := (Finset.mem_Icc.mp hs).1
    have hsR : (0:ℝ) < (s:ℝ) := by exact_mod_cast hs1
    have hdle : dfour s ≤ 4 / (s:ℝ)^5 := dfour_le s hs1
    have hcoe : (0:ℝ) ≤ 4 / (s:ℝ)^5 := by positivity
    have hcard := hcard_bound s hs
    have hcardnn : (0:ℝ) ≤ ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ) := by positivity
    have hstep1 : dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (4 / (s:ℝ)^5) * (81 * (s:ℝ)^4) := mul_le_mul hdle hcard hcardnn hcoe
    have heq : (4 / (s:ℝ)^5) * (81 * (s:ℝ)^4) = 324 / (s:ℝ) := by
      field_simp [hsR.ne']
      ring
    calc dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ (4 / (s:ℝ)^5) * (81 * (s:ℝ)^4) := hstep1
      _ = 324 / (s:ℝ) := heq
  have hharm : ∑ s ∈ Finset.Icc 1 n, (s:ℝ)⁻¹ ≤ 1 + Real.log n := by
    have heq : (harmonic n : ℝ) = ∑ s ∈ Finset.Icc 1 n, (s:ℝ)⁻¹ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rfl
    rw [← heq]
    exact harmonic_le_one_add_log n
  have hsumterm : ∑ s ∈ Finset.Icc 1 n,
      dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ 324 * (1 + Real.log n) := by
    calc ∑ s ∈ Finset.Icc 1 n,
        dfour s * ((S.filter (fun m => maxNorm n m ≤ s)).card : ℝ)
        ≤ ∑ s ∈ Finset.Icc 1 n, 324 / (s:ℝ) := Finset.sum_le_sum hterm
      _ = 324 * ∑ s ∈ Finset.Icc 1 n, (s:ℝ)⁻¹ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro s _
          rw [div_eq_mul_inv]
      _ ≤ 324 * (1 + Real.log n) := mul_le_mul_of_nonneg_left hharm (by norm_num)
  have htail : (S.card : ℝ) * gfour (n + 1) ≤ 1 := by
    have hScard : (S.card : ℝ) ≤ (n:ℝ)^4 := by
      have h1 : S.card ≤ (Finset.univ : Finset (Fin 4 → ZMod n)).card := Finset.card_erase_le
      have h2 : (Finset.univ : Finset (Fin 4 → ZMod n)).card = n^4 := by simp
      have h3 : S.card ≤ n^4 := by rw [← h2]; exact h1
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
    have hone : (n:ℝ)^4 * (1/(n:ℝ)^4) = 1 := by field_simp
    calc (S.card : ℝ) * gfour (n+1) ≤ (n:ℝ)^4 * (1/(n:ℝ)^4) :=
          mul_le_mul hScard hgfour (gfour_nonneg (n+1)) (by positivity)
      _ = 1 := hone
  have hmain : ∑ m ∈ S, gfour (maxNorm n m) ≤ (324 * (1 + Real.log n) + 1) := by
    rw [hlayer]
    exact add_le_add hsumterm htail
  have h1 : latSum2 n 4 = ((n:ℝ)^4)⁻¹ * ∑ m ∈ S, ((dispersion (waveVector n m))⁻¹)^2 := by
    rw [latSum2, ← hS]
  have h2 : ((n:ℝ)^4)⁻¹ * ∑ m ∈ S, ((dispersion (waveVector n m))⁻¹)^2
      ≤ ((n:ℝ)^4)⁻¹ * (((n:ℝ)^4/256) * ∑ m ∈ S, gfour (maxNorm n m)) :=
    mul_le_mul_of_nonneg_left hinv (by positivity)
  have h3 : ((n:ℝ)^4)⁻¹ * (((n:ℝ)^4/256) * ∑ m ∈ S, gfour (maxNorm n m))
      ≤ ((n:ℝ)^4)⁻¹ * (((n:ℝ)^4/256) * (324 * (1 + Real.log n) + 1)) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmain (by positivity)) (by positivity)
  have h4 : ((n:ℝ)^4)⁻¹ * (((n:ℝ)^4/256) * (324 * (1 + Real.log n) + 1))
      = (81/64) * (1 + Real.log n) + 1/256 := by
    field_simp
    ring
  linarith [h1, h2, h3, h4]

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
