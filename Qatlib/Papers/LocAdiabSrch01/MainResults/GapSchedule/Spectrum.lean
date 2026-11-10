/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Real
open Matrix

namespace Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule

def reducedHam (N s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 - s) * ((N - 1) / N), -((1 - s) * Real.sqrt (N - 1) / N);
     -((1 - s) * Real.sqrt (N - 1) / N), 1 - (1 - s) * ((N - 1) / N)]

theorem reducedHam_trace (N s : ℝ) : (reducedHam N s).trace = 1 := by
  simp [reducedHam, Matrix.trace, Fin.sum_univ_two]

theorem reducedHam_det {N s : ℝ} (hN : 1 ≤ N) :
    (reducedHam N s).det = s * (1 - s) * ((N - 1) / N) := by
  have hN0 : N ≠ 0 := by linarith
  have hsq : (Real.sqrt (N - 1)) ^ 2 = N - 1 := Real.sq_sqrt (by linarith)
  simp only [reducedHam, Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one]
  field_simp
  rw [hsq]
  ring

theorem reducedHam_discriminant {N s : ℝ} (hN : 1 ≤ N) :
    (reducedHam N s).trace ^ 2 - 4 * (reducedHam N s).det = gapSq N s := by
  rw [reducedHam_trace, reducedHam_det hN]
  unfold gapSq
  ring

def lamMinus (N s : ℝ) : ℝ := (1 - Real.sqrt (gapSq N s)) / 2

def lamPlus (N s : ℝ) : ℝ := (1 + Real.sqrt (gapSq N s)) / 2

theorem lam_sum (N s : ℝ) : lamPlus N s + lamMinus N s = 1 := by
  unfold lamPlus lamMinus
  ring

theorem lam_prod {N s : ℝ} (hN : 1 ≤ N) :
    lamPlus N s * lamMinus N s = (reducedHam N s).det := by
  have hnn : 0 ≤ gapSq N s := by
    rcases lt_or_eq_of_le hN with h | h
    · exact (gapSq_pos h (s := s)).le
    · subst h; unfold gapSq; norm_num
  have hdisc := reducedHam_discriminant (N := N) (s := s) hN
  have htr := reducedHam_trace N s
  unfold lamPlus lamMinus
  rw [show ((1 + Real.sqrt (gapSq N s)) / 2) * ((1 - Real.sqrt (gapSq N s)) / 2)
        = (1 - (Real.sqrt (gapSq N s)) ^ 2) / 4 by ring,
      Real.sq_sqrt hnn]

  have : gapSq N s = 1 - 4 * (reducedHam N s).det := by
    rw [← hdisc, htr]; ring
  rw [this]
  ring

theorem lam_charpoly_plus {N s : ℝ} (hN : 1 ≤ N) :
    (lamPlus N s) ^ 2 - (reducedHam N s).trace * lamPlus N s
      + (reducedHam N s).det = 0 := by
  have hsum := lam_sum N s
  have hprod := lam_prod (N := N) (s := s) hN
  have htr := reducedHam_trace N s
  have hm : lamMinus N s = 1 - lamPlus N s := by linarith
  rw [hm] at hprod
  rw [htr]
  nlinarith [hprod]

theorem lam_charpoly_minus {N s : ℝ} (hN : 1 ≤ N) :
    (lamMinus N s) ^ 2 - (reducedHam N s).trace * lamMinus N s
      + (reducedHam N s).det = 0 := by
  have hsum := lam_sum N s
  have hprod := lam_prod (N := N) (s := s) hN
  have htr := reducedHam_trace N s
  have hm : lamPlus N s = 1 - lamMinus N s := by linarith
  rw [hm] at hprod
  rw [htr]
  nlinarith [hprod]

theorem reducedHam_gap (N s : ℝ) :
    lamPlus N s - lamMinus N s = Real.sqrt (gapSq N s) := by
  unfold lamPlus lamMinus
  ring

theorem lambda_nonneg {N s : ℝ} (hN : 1 < N) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ lamMinus N s := by
  have hpos := gapSq_pos (N := N) (s := s) hN
  have hNN : 0 ≤ (N - 1) / N := by
    have : 0 < (N - 1) / N := div_pos (by linarith) (by linarith)
    linarith
  have hfac : 0 ≤ 4 * ((N - 1) / N) * (s * (1 - s)) := by
    have : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    positivity
  have hle : gapSq N s ≤ 1 := by
    unfold gapSq
    nlinarith [hfac]
  have hsq : Real.sqrt (gapSq N s) ≤ 1 := by
    have := Real.sqrt_le_sqrt hle
    simpa using this
  unfold lamMinus
  linarith

theorem lambda_le_one {N s : ℝ} (hN : 1 < N) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    lamPlus N s ≤ 1 := by
  have hpos := gapSq_pos (N := N) (s := s) hN
  have hNN : 0 ≤ (N - 1) / N := by
    have : 0 < (N - 1) / N := div_pos (by linarith) (by linarith)
    linarith
  have hfac : 0 ≤ 4 * ((N - 1) / N) * (s * (1 - s)) := by
    have : 0 ≤ s * (1 - s) := mul_nonneg hs0 (by linarith)
    positivity
  have hle : gapSq N s ≤ 1 := by
    unfold gapSq
    nlinarith [hfac]
  have hsq : Real.sqrt (gapSq N s) ≤ 1 := by
    have := Real.sqrt_le_sqrt hle
    simpa using this
  unfold lamPlus
  linarith

theorem lambda_le (N s : ℝ) : lamMinus N s ≤ lamPlus N s := by
  unfold lamMinus lamPlus
  have := Real.sqrt_nonneg (gapSq N s)
  linarith

theorem reduced_spectrum {N s : ℝ} (hN : 1 < N) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ lamMinus N s ∧ lamMinus N s ≤ lamPlus N s ∧ lamPlus N s ≤ 1 ∧
      lamPlus N s - lamMinus N s = Real.sqrt (gapSq N s) :=
  ⟨lambda_nonneg hN hs0 hs1, lambda_le N s, lambda_le_one hN hs0 hs1,
    reducedHam_gap N s⟩

end Qatlib.Papers.LocAdiabSrch01.MainResults.GapSchedule
