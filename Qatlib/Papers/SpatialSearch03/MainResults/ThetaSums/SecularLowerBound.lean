/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.SecularBound
set_option warningAsError false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

theorem inv_add_ge (x ε : ℝ) (hx : 0 < x) (hε : 0 ≤ ε) :
    x⁻¹ - ε * (x⁻¹) ^ 2 ≤ (x + ε)⁻¹ := by
  have hxe : 0 < x + ε := by linarith
  have hx2 : 0 < x ^ 2 := by positivity
  have key : (x + ε)⁻¹ - (x⁻¹ - ε * (x⁻¹) ^ 2) = ε ^ 2 / (x ^ 2 * (x + ε)) := by
    field_simp
    ring
  have hnn : 0 ≤ ε ^ 2 / (x ^ 2 * (x + ε)) := by positivity
  linarith [key]

theorem secular_lower_bound {γ : ℝ} {n d : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    {E : ℝ} (hE : E < 0) :
    latSum1 n d / γ - |E| * latSum2 n d / γ ^ 2 ≤ secular γ n d E := by
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hNpos : (0:ℝ) < (n:ℝ) ^ d := by positivity
  have hNinv : (0:ℝ) ≤ ((n:ℝ) ^ d)⁻¹ := by positivity
  have habs : |E| = -E := abs_of_neg hE
  have hsplit := (Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin d → ZMod n)))
    (f := fun m => (γ * dispersion (waveVector n m) - E)⁻¹)
    (Finset.mem_univ (0 : Fin d → ZMod n))).symm
  have hzero : (0:ℝ) ≤ (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ := by
    have h1 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by simp
    rw [h1, zero_sub]
    exact inv_nonneg.2 (by linarith)
  have hterm : ∀ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      γ⁻¹ * (dispersion (waveVector n m))⁻¹
        - |E| * (γ⁻¹) ^ 2 * ((dispersion (waveVector n m))⁻¹) ^ 2
      ≤ (γ * dispersion (waveVector n m) - E)⁻¹ := by
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hpos := dispersion_waveVector_pos hn hm0
    have hx : 0 < γ * dispersion (waveVector n m) := mul_pos hγ hpos
    have h := inv_add_ge (γ * dispersion (waveVector n m)) |E| hx (abs_nonneg E)
    have hxe : γ * dispersion (waveVector n m) + |E| = γ * dispersion (waveVector n m) - E := by
      rw [habs]; ring
    rw [hxe] at h
    have e1 : (γ * dispersion (waveVector n m))⁻¹
        = γ⁻¹ * (dispersion (waveVector n m))⁻¹ := by rw [mul_inv]
    rw [e1] at h
    have e2 : (γ⁻¹ * (dispersion (waveVector n m))⁻¹) ^ 2
        = (γ⁻¹) ^ 2 * ((dispersion (waveVector n m))⁻¹) ^ 2 := by ring
    rw [e2] at h
    ring_nf at h ⊢
    exact h
  have hsum : ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      (γ⁻¹ * (dispersion (waveVector n m))⁻¹
        - |E| * (γ⁻¹) ^ 2 * ((dispersion (waveVector n m))⁻¹) ^ 2)
      ≤ ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
        (γ * dispersion (waveVector n m) - E)⁻¹ :=
    Finset.sum_le_sum hterm
  have hfac : ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      (γ⁻¹ * (dispersion (waveVector n m))⁻¹
        - |E| * (γ⁻¹) ^ 2 * ((dispersion (waveVector n m))⁻¹) ^ 2)
      = γ⁻¹ * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          (dispersion (waveVector n m))⁻¹)
        - |E| * (γ⁻¹) ^ 2 * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          ((dispersion (waveVector n m))⁻¹) ^ 2) := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  have hNs : ((n:ℝ) ^ d)⁻¹ * (γ⁻¹ * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          (dispersion (waveVector n m))⁻¹)
        - |E| * (γ⁻¹) ^ 2 * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          ((dispersion (waveVector n m))⁻¹) ^ 2))
      = γ⁻¹ * latSum1 n d - |E| * (γ⁻¹) ^ 2 * latSum2 n d := by
    unfold latSum1 latSum2
    ring
  calc latSum1 n d / γ - |E| * latSum2 n d / γ ^ 2
      = ((n:ℝ) ^ d)⁻¹ * (γ⁻¹ * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
            (dispersion (waveVector n m))⁻¹)
          - |E| * (γ⁻¹) ^ 2 * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
            ((dispersion (waveVector n m))⁻¹) ^ 2)) := by
        rw [hNs, div_eq_mul_inv, div_eq_mul_inv, inv_pow]
        ring
    _ ≤ ((n:ℝ) ^ d)⁻¹ * (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          (γ * dispersion (waveVector n m) - E)⁻¹) := by
        rw [← hfac]
        exact mul_le_mul_of_nonneg_left hsum hNinv
    _ ≤ ((n:ℝ) ^ d)⁻¹ * ((∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
            (γ * dispersion (waveVector n m) - E)⁻¹)
          + (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹) := by
        have hle : (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
            (γ * dispersion (waveVector n m) - E)⁻¹)
            ≤ (∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
              (γ * dispersion (waveVector n m) - E)⁻¹)
              + (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E)⁻¹ :=
          le_add_of_nonneg_right hzero
        exact mul_le_mul_of_nonneg_left hle hNinv
    _ = secular γ n d E := by
        rw [← hsplit, secular]

theorem ground_energy_lower_bound {γ : ℝ} {n d : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    (hI2 : 0 < latSum2 n d) (_hL : γ < latSum1 n d) {E₀ : ℝ} (hE₀ : E₀ < 0)
    (hF : secular γ n d E₀ = 1) :
    γ * (latSum1 n d - γ) / latSum2 n d ≤ |E₀| := by
  have h := secular_lower_bound (d := d) hγ hn hE₀
  rw [hF] at h
  have hγ2 : (0:ℝ) < γ ^ 2 := by positivity
  have hkey : latSum1 n d / γ - 1 ≤ |E₀| * latSum2 n d / γ ^ 2 := by linarith
  have hmul : γ ^ 2 * (latSum1 n d / γ - 1) ≤ |E₀| * latSum2 n d := by
    have := mul_le_mul_of_nonneg_left hkey hγ2.le
    calc γ ^ 2 * (latSum1 n d / γ - 1) ≤ γ ^ 2 * (|E₀| * latSum2 n d / γ ^ 2) := this
      _ = |E₀| * latSum2 n d := by field_simp
  have hval : γ ^ 2 * (latSum1 n d / γ - 1) = γ * (latSum1 n d - γ) := by
    field_simp
  rw [hval] at hmul
  rw [div_le_iff₀ hI2]
  calc γ * (latSum1 n d - γ) = γ * (latSum1 n d - γ) := rfl
    _ ≤ |E₀| * latSum2 n d := hmul

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
