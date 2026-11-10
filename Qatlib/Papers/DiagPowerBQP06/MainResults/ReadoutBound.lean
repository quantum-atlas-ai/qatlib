/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.DiagPowerBQP06.MainResults.ReadoutBound

theorem abs_pow_sub_pow_le_of_abs_le_one (z lam : ℝ) (m : ℕ)
    (hz : |z| ≤ 1) (hlam : |lam| ≤ 1) :
    |z ^ m - lam ^ m| ≤ (m : ℝ) * |z - lam| := by
  rcases m with _ | n
  · simp
  · have h := abs_pow_sub_pow_le z lam (n + 1)
    have hmax : max |z| |lam| ^ n ≤ 1 := by
      apply pow_le_one₀ (le_trans (abs_nonneg _) (le_max_left _ _))
      exact max_le hz hlam
    calc |z ^ (n + 1) - lam ^ (n + 1)|
        ≤ |z - lam| * ((n + 1 : ℕ) : ℝ) * max |z| |lam| ^ n := h
      _ ≤ |z - lam| * ((n + 1 : ℕ) : ℝ) * 1 := by
          gcongr
      _ = ((n + 1 : ℕ) : ℝ) * |z - lam| := by ring

theorem readout_moment_error
    {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (Z : Ω → ℝ) (lam θ η : ℝ) (m : ℕ)
    (hw : ∀ ω, 0 ≤ w ω) (hsum : ∑ ω, w ω = 1)
    (hZ : ∀ ω, |Z ω| ≤ 1) (hlam : |lam| ≤ 1)
    (hθ : 0 ≤ θ) (hη : 0 ≤ η)
    (hevent : ∑ ω ∈ univ.filter (fun ω => 2 * Real.pi * η ≤ |Z ω - lam|), w ω ≤ θ) :
    |(∑ ω, w ω * (Z ω) ^ m) - lam ^ m| ≤ 2 * θ + (m : ℝ) * (2 * Real.pi * η) := by
  classical
  have hmoment : (∑ ω, w ω * (Z ω) ^ m) - lam ^ m
      = ∑ ω, w ω * ((Z ω) ^ m - lam ^ m) := by
    have hcongr : (∑ ω, w ω * ((Z ω) ^ m - lam ^ m))
        = ∑ ω, (w ω * (Z ω) ^ m - w ω * lam ^ m) := by
      apply Finset.sum_congr rfl
      intro ω _
      ring
    rw [hcongr, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hmoment]

  set Bad : Finset Ω := univ.filter (fun ω => 2 * Real.pi * η ≤ |Z ω - lam|) with hBad
  have hsplit : ∑ ω, w ω * ((Z ω) ^ m - lam ^ m)
      = (∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m))
        + (∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m)) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ Bad), add_comm]
  rw [hsplit]
  have hbad : |∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m)| ≤ 2 * θ := by
    have h1 : |∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
        ≤ ∑ ω ∈ Bad, w ω * |(Z ω) ^ m - lam ^ m| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (hw ω)]
    have h2 : ∀ ω, |(Z ω) ^ m - lam ^ m| ≤ 2 := by
      intro ω
      have hz : |(Z ω) ^ m| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hZ ω)
      have hl : |lam ^ m| ≤ 1 := by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hlam
      calc |(Z ω) ^ m - lam ^ m|
          ≤ |(Z ω) ^ m| + |lam ^ m| := abs_sub _ _
        _ ≤ 1 + 1 := add_le_add hz hl
        _ = 2 := by norm_num
    calc |∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
        ≤ ∑ ω ∈ Bad, w ω * |(Z ω) ^ m - lam ^ m| := h1
      _ ≤ ∑ ω ∈ Bad, w ω * 2 := by
          apply Finset.sum_le_sum
          intro ω _
          exact mul_le_mul_of_nonneg_left (h2 ω) (hw ω)
      _ = 2 * (∑ ω ∈ Bad, w ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring
      _ ≤ 2 * θ := by
          apply mul_le_mul_of_nonneg_left hevent
          norm_num
  have hgood : |∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
      ≤ (m : ℝ) * (2 * Real.pi * η) := by
    have h1 : |∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
        ≤ ∑ ω ∈ univ \ Bad, w ω * |(Z ω) ^ m - lam ^ m| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro ω _
      rw [abs_mul, abs_of_nonneg (hw ω)]
    have h2 : ∀ ω ∈ univ \ Bad, |(Z ω) ^ m - lam ^ m| ≤ (m : ℝ) * (2 * Real.pi * η) := by
      intro ω hω
      have hnot : ¬ (2 * Real.pi * η ≤ |Z ω - lam|) := by
        have : ω ∉ Bad := (Finset.mem_sdiff.mp hω).2
        simpa [hBad] using this
      have hlt : |Z ω - lam| ≤ 2 * Real.pi * η := le_of_lt (lt_of_not_ge hnot)
      calc |(Z ω) ^ m - lam ^ m|
          ≤ (m : ℝ) * |Z ω - lam| := abs_pow_sub_pow_le_of_abs_le_one _ _ m (hZ ω) hlam
        _ ≤ (m : ℝ) * (2 * Real.pi * η) := by
            gcongr
    calc |∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
        ≤ ∑ ω ∈ univ \ Bad, w ω * |(Z ω) ^ m - lam ^ m| := h1
      _ ≤ ∑ ω ∈ univ \ Bad, w ω * ((m : ℝ) * (2 * Real.pi * η)) := by
          apply Finset.sum_le_sum
          intro ω hω
          exact mul_le_mul_of_nonneg_left (h2 ω hω) (hw ω)
      _ = ((m : ℝ) * (2 * Real.pi * η)) * (∑ ω ∈ univ \ Bad, w ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro ω _
          ring
      _ ≤ ((m : ℝ) * (2 * Real.pi * η)) * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc ∑ ω ∈ univ \ Bad, w ω ≤ ∑ ω, w ω :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hw x)
            _ = 1 := hsum
      _ = (m : ℝ) * (2 * Real.pi * η) := by ring
  calc |(∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m))
        + (∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m))|
      ≤ |∑ ω ∈ Bad, w ω * ((Z ω) ^ m - lam ^ m)|
        + |∑ ω ∈ univ \ Bad, w ω * ((Z ω) ^ m - lam ^ m)| := abs_add_le _ _
    _ ≤ 2 * θ + (m : ℝ) * (2 * Real.pi * η) := add_le_add hbad hgood

theorem spectral_triangle_error
    {ι : Type*} [Fintype ι]
    (w E lam : ι → ℝ) (ε : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) (hε : 0 ≤ ε)
    (h : ∀ i, |E i - lam i| ≤ ε / 3) :
    |(∑ i, w i * E i) - (∑ i, w i * lam i)| ≤ ε / 3 := by
  have hdiff : (∑ i, w i * E i) - (∑ i, w i * lam i) = ∑ i, w i * (E i - lam i) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiff]
  calc |∑ i, w i * (E i - lam i)|
      ≤ ∑ i, w i * |E i - lam i| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * (ε / 3) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (h i) (hw i)
    _ = (ε / 3) * (∑ i, w i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = ε / 3 := by rw [hsum, mul_one]

theorem total_error_budget {a b c ε : ℝ}
    (ha : a ≤ ε / 3) (hb : b ≤ ε / 3) (hc : c ≤ ε / 3) (hε : 0 ≤ ε) :
    a + b + c ≤ ε := by
  linarith

end Qatlib.Papers.DiagPowerBQP06.MainResults.ReadoutBound
