/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ContDiscWalk08.SchemeAlgebra.BoseMesnerUnitary
import Mathlib.Analysis.Real.Pi.Bounds
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Qatlib.Papers.ContDiscWalk08.PaleySearch

open Qatlib.Papers.ContDiscWalk08.SchemeAlgebra (phase)

theorem exists_phase_sum_eq_sum_abs {m : ℕ} (a : Fin m → ℝ) :
    ∃ φ : Fin m → ℝ, ‖∑ j, phase (φ j) * (a j : ℂ)‖ = ∑ j, (|a j| : ℝ) := by
  refine ⟨fun j => if 0 ≤ a j then 0 else Real.pi, ?_⟩
  have hterm : ∀ j, phase ((if 0 ≤ a j then 0 else Real.pi : ℝ)) * (a j : ℂ)
      = ((|a j| : ℝ) : ℂ) := by
    intro j
    by_cases h : 0 ≤ a j
    · rw [if_pos h]
      have hphase : phase (0 : ℝ) = 1 := by
        unfold phase
        simp
      rw [hphase]
      rw [abs_of_nonneg h]
      ring
    · rw [if_neg h]
      have hneg : a j < 0 := lt_of_not_ge h
      have hphase : phase Real.pi = -1 := by
        unfold phase
        rw [mul_comm]
        exact Complex.exp_pi_mul_I
      rw [hphase]
      rw [abs_of_neg hneg]
      push_cast
      ring
  calc ‖∑ j, phase ((if 0 ≤ a j then 0 else Real.pi : ℝ)) * (a j : ℂ)‖
      = ‖∑ j, ((|a j| : ℝ) : ℂ)‖ := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => hterm j)
    _ = ∑ j, (|a j| : ℝ) := by
          rw [← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg (a j))]

theorem exists_phases_success {m : ℕ} (qji : Fin m → ℝ) (Ni N : ℝ) :
    ∃ φ : Fin m → ℝ,
      Ni / N ^ 2 * ‖∑ j, phase (φ j) * (qji j : ℂ)‖ ^ 2
        = Ni / N ^ 2 * (∑ j, (|qji j| : ℝ)) ^ 2 := by
  obtain ⟨φ, hφ⟩ := exists_phase_sum_eq_sum_abs qji
  exact ⟨φ, by rw [hφ]⟩

theorem quarter_le_paley_bound {q : ℝ} (hq : 4 ≤ q) :
    (1 / 4 : ℝ) ≤ (Real.sqrt q + 1) ^ 2 * (q - 1) ^ 2 / (4 * q ^ 3) := by
  have hq0 : 0 < q := by linarith
  set s := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hsq : s ^ 2 = q := by
    rw [hsdef]
    exact Real.sq_sqrt hq0.le
  have hs2 : 2 ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) hq0.le]
    nlinarith [hq]
  rw [← hsq]
  have hkey : s ^ 3 ≤ (s - 1) * (s + 1) ^ 2 := by
    nlinarith [hs2]
  have hq1 : s ^ 2 - 1 = (s - 1) * (s + 1) := by ring
  have hmain : (s ^ 2) ^ 3 ≤ (s + 1) ^ 2 * (s ^ 2 - 1) ^ 2 := by
    rw [hq1]
    nlinarith [hkey, hs0, sq_nonneg (s ^ 3), sq_nonneg ((s - 1) * (s + 1) ^ 2)]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (s ^ 2) ^ 3)]
  nlinarith [hmain]

theorem paley_success_ge_quarter {q : ℝ} (hq : 4 ≤ q) :
    (1 / 4 : ℝ) ≤ ((q - 1) / 2) ^ 2 * (Real.sqrt q + 1) ^ 2 / q ^ 3 := by
  have hq0 : 0 < q := by linarith
  have h := quarter_le_paley_bound hq
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * q ^ 3)] at h
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < q ^ 3)]
  nlinarith [h]

theorem paley_norm_ratio_bounds {q : ℝ} (hq : 4 ≤ q) :
    Real.sqrt q / 4 ≤ (Real.sqrt q + 1) * (q - 1) / (2 * q) ∧
      (Real.sqrt q + 1) * (q - 1) / (2 * q) ≤ Real.sqrt q := by
  have hq0 : 0 < q := by linarith
  set s := Real.sqrt q with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hsq : s ^ 2 = q := by
    rw [hsdef]
    exact Real.sq_sqrt hq0.le
  have hs2 : 2 ≤ s := by
    rw [hsdef, Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 2) hq0.le]
    nlinarith [hq]
  have hs3 : 0 < s := by linarith
  rw [← hsq]
  constructor
  · rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s ^ 2)]
    nlinarith [hs2, sq_nonneg (s - 1)]
  · rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * s ^ 2)]
    nlinarith [hs2]

end Qatlib.Papers.ContDiscWalk08.PaleySearch
