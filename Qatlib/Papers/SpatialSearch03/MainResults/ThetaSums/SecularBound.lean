/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums.Lattice

/-!
# Dispersion positivity and secular-root upper bounds

This module identifies the zero mode of the periodic lattice dispersion and proves positivity at
every nonzero lattice index. These facts give nonnegativity of the first lattice sum and an
upper bound on a negative secular root when the coupling exceeds that sum, as in
[ChildsGoldstone2004].

## Main statements

* `dispersion_waveVector_eq_zero_iff`: the dispersion vanishes exactly at the zero lattice
  index.
* `latSum1_nonneg`: nonnegativity of the first lattice sum.
* `ground_energy_bound`: explicit upper bound on the negative root magnitude above the first
  lattice sum.

## References

* [Childs and Goldstone, 2004][ChildsGoldstone2004]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums

open Finset

variable {d : ℕ}

/-- For positive side length, every wave-vector coordinate has absolute value strictly less than
`2 * Real.pi`. -/
theorem abs_waveVector_lt_two_pi {n : ℕ} (hn : 0 < n) (m : Fin d → ZMod n) (j : Fin d) :
    |waveVector n m j| < 2 * Real.pi := by
  have h := abs_waveVector_le_pi hn m j
  linarith [Real.pi_pos]

/-- For positive side length, the cosine of a wave-vector coordinate is one exactly when that
coordinate is zero. -/
theorem cos_waveVector_eq_one_iff {n : ℕ} (hn : 0 < n) (m : Fin d → ZMod n) (j : Fin d) :
    Real.cos (waveVector n m j) = 1 ↔ waveVector n m j = 0 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp (abs_waveVector_lt_two_pi hn m j)
  exact Real.cos_eq_one_iff_of_lt_of_lt h1 h2

/-- For positive side length, a wave-vector coordinate vanishes exactly when the corresponding
periodic lattice coordinate is zero. -/
theorem waveVector_eq_zero_iff {n : ℕ} [NeZero n] (hn : 0 < n) (m : Fin d → ZMod n)
    (j : Fin d) : waveVector n m j = 0 ↔ m j = 0 := by
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  constructor
  · intro h
    have h2 : 2 * Real.pi * ((m j).valMinAbs : ℝ) / (n:ℝ) = 0 := h
    have h3 : ((m j).valMinAbs : ℝ) = 0 := by
      have hpa : (2:ℝ) * Real.pi ≠ 0 := by positivity
      rw [div_eq_zero_iff] at h2
      rcases h2 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h2 | h2
        · exact absurd h2 hpa
        · exact h2
      · exact absurd h2 hnR.ne'
    have h4 : (m j).valMinAbs = 0 := by exact_mod_cast h3
    exact (ZMod.valMinAbs_eq_zero (m j)).mp h4
  · intro h
    simp [waveVector, h]

/-- For positive side length, the dispersion of a lattice wave vector vanishes exactly at the
zero lattice index. -/
theorem dispersion_waveVector_eq_zero_iff {n : ℕ} [NeZero n] (hn : 0 < n)
    (m : Fin d → ZMod n) : dispersion (waveVector n m) = 0 ↔ m = 0 := by
  rw [dispersion_eq_zero_iff]
  constructor
  · intro h
    funext j
    exact (waveVector_eq_zero_iff hn m j).mp ((cos_waveVector_eq_one_iff hn m j).mp (h j))
  · intro h
    rw [h]
    intro j
    simp [waveVector]

/-- For positive side length, every nonzero lattice index has strictly positive dispersion. -/
theorem dispersion_waveVector_pos {n : ℕ} [NeZero n] (hn : 0 < n) {m : Fin d → ZMod n}
    (hm : m ≠ 0) : 0 < dispersion (waveVector n m) := by
  rcases (dispersion_nonneg (waveVector n m)).eq_or_lt with h | h
  · exact absurd ((dispersion_waveVector_eq_zero_iff hn m).mp h.symm) hm
  · exact h

/-- The first lattice sum is nonnegative for positive side length in every dimension. -/
theorem latSum1_nonneg {n : ℕ} [NeZero n] (hn : 0 < n) (d : ℕ) : 0 ≤ latSum1 n d := by
  unfold latSum1
  refine mul_nonneg (by positivity) ?_
  refine Finset.sum_nonneg ?_
  intro m _
  exact inv_nonneg.2 (dispersion_nonneg _)

/-- For positive coupling and side length, if the coupling exceeds the first lattice sum, every
negative secular root has magnitude at most `γ / (n ^ d * (γ - latSum1 n d))`
[ChildsGoldstone2004]. -/
theorem ground_energy_bound {γ : ℝ} {n d : ℕ} [NeZero n] (hγ : 0 < γ) (hn : 0 < n)
    (hL : latSum1 n d < γ) {E₀ : ℝ} (hE₀ : E₀ < 0) (hF : secular γ n d E₀ = 1) :
    |E₀| ≤ γ / ((n : ℝ) ^ d * (γ - latSum1 n d)) := by
  set N : ℝ := (n : ℝ) ^ d with hN
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hNpos : 0 < N := by simpa [hN] using pow_pos hnR d
  have habs : 0 < |E₀| := abs_pos.2 (ne_of_lt hE₀)
  have hsec : N⁻¹ * ∑ m : Fin d → ZMod n, (γ * dispersion (waveVector n m) - E₀)⁻¹ = 1 := by
    rw [hN]
    simpa [secular] using hF
  have hsplit := (Finset.sum_erase_add
    (s := (Finset.univ : Finset (Fin d → ZMod n)))
    (f := fun m => (γ * dispersion (waveVector n m) - E₀)⁻¹)
    (Finset.mem_univ (0 : Fin d → ZMod n))).symm
  have hzero : (γ * dispersion (waveVector n (0 : Fin d → ZMod n)) - E₀)⁻¹ = |E₀|⁻¹ := by
    have h1 : γ * dispersion (waveVector n (0 : Fin d → ZMod n)) = 0 := by simp
    rw [h1, zero_sub, abs_of_neg hE₀]
  rw [hzero] at hsplit
  rw [hsplit, mul_add] at hsec
  have hA : N⁻¹ * |E₀|⁻¹ = 1 - N⁻¹ * ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      (γ * dispersion (waveVector n m) - E₀)⁻¹ := by linarith
  have hS : ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      (γ * dispersion (waveVector n m) - E₀)⁻¹
      ≤ γ⁻¹ * ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
          (dispersion (waveVector n m))⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum ?_
    intro m hm
    have hm0 : m ≠ 0 := (Finset.mem_erase.mp hm).1
    have hpos := dispersion_waveVector_pos hn hm0
    have hga : 0 < γ * dispersion (waveVector n m) := mul_pos hγ hpos
    have hle : γ * dispersion (waveVector n m) ≤ γ * dispersion (waveVector n m) - E₀ := by
      linarith
    have h := inv_anti₀ hga hle
    have heq : (γ * dispersion (waveVector n m))⁻¹
        = γ⁻¹ * (dispersion (waveVector n m))⁻¹ := by rw [mul_inv]
    rwa [heq] at h
  have hlat : N⁻¹ * ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
      (γ * dispersion (waveVector n m) - E₀)⁻¹ ≤ γ⁻¹ * latSum1 n d := by
    have h := mul_le_mul_of_nonneg_left hS (by positivity : (0:ℝ) ≤ N⁻¹)
    have hL2 : N⁻¹ * (γ⁻¹ * ∑ m ∈ Finset.univ.erase (0 : Fin d → ZMod n),
        (dispersion (waveVector n m))⁻¹) = γ⁻¹ * latSum1 n d := by
      rw [latSum1, ← hN]
      ring
    linarith [hL2]
  have h1 : 1 - γ⁻¹ * latSum1 n d ≤ N⁻¹ * |E₀|⁻¹ := by linarith
  have hpos1 : 0 < 1 - γ⁻¹ * latSum1 n d := by
    have heq : γ⁻¹ * latSum1 n d = latSum1 n d / γ := by field_simp
    rw [heq]
    have hlt : latSum1 n d / γ < 1 := by rwa [div_lt_one hγ]
    linarith
  have hAineq : N * (1 - γ⁻¹ * latSum1 n d) ≤ |E₀|⁻¹ := by
    calc N * (1 - γ⁻¹ * latSum1 n d) ≤ N * (N⁻¹ * |E₀|⁻¹) :=
          mul_le_mul_of_nonneg_left h1 hNpos.le
      _ = |E₀|⁻¹ := by field_simp
  have hcoef : 0 < N * (1 - γ⁻¹ * latSum1 n d) := mul_pos hNpos hpos1
  have hmul : N * (1 - γ⁻¹ * latSum1 n d) * |E₀| ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hAineq habs.le
    rwa [inv_mul_cancel₀ (ne_of_gt habs)] at h
  have hfin : |E₀| ≤ (N * (1 - γ⁻¹ * latSum1 n d))⁻¹ := by
    rw [← one_div, le_div_iff₀ hcoef]
    calc |E₀| * (N * (1 - γ⁻¹ * latSum1 n d))
          = N * (1 - γ⁻¹ * latSum1 n d) * |E₀| := by ring
      _ ≤ 1 := hmul
  have hgoal : (N * (1 - γ⁻¹ * latSum1 n d))⁻¹ = γ / (N * (γ - latSum1 n d)) := by
    have hne : γ - latSum1 n d ≠ 0 := by linarith
    have h1ne : 1 - γ⁻¹ * latSum1 n d ≠ 0 := ne_of_gt hpos1
    field_simp [hγ.ne', hNpos.ne', hne, h1ne]
  rw [hgoal, hN] at hfin
  exact hfin

end Qatlib.Papers.SpatialSearch03.MainResults.ThetaSums
