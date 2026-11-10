/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAAmplify09.MainResults.Defs
import Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Qatlib.Papers.QMAAmplify09.MainResults.Defs
open Qatlib.Papers.QMAAmplify09.MainResults.MedianLemma

namespace Qatlib.Papers.QMAAmplify09.MainResults.ExactAmplification

def IsExactTBitPhase (t : ℕ) (φ : ℝ) : Prop :=
  ∃ k : ℤ, φ = (k : ℝ) / (2 : ℝ) ^ t

theorem tbit_estimation_exact {t : ℕ} {φ : ℝ} (h : IsExactTBitPhase t φ) :
    ∃ k : ℤ, φ = (k : ℝ) / (2 : ℝ) ^ t ∧ φ - (k : ℝ) / (2 : ℝ) ^ t = 0 := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k, hk, by rw [hk]; ring⟩

theorem exact_phase_probability {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    probabilityOfPhase (phaseOfProbability p) = p :=
  probabilityOfPhase_phaseOfProbability hp0 hp1

theorem badMass_zero (r : ℕ) : badMass 0 r = 0 := by
  unfold badMass binomialTerm
  refine Finset.sum_eq_zero ?_
  intro k hk
  have hk1 : 0 < k := by
    have := (Finset.mem_Icc.mp hk).1
    omega
  simp [zero_pow (Nat.pos_iff_ne_zero.mp hk1)]

theorem medianFailureBound_zero {r : ℕ} (hr : 1 ≤ r) : medianFailureBound 0 r = 0 := by
  unfold medianFailureBound
  have h0 : (2 : ℝ) * Real.sqrt (0 * (1 - 0)) = 0 := by norm_num
  have hz : (0 : ℝ) ^ r = 0 := zero_pow (by omega : r ≠ 0)
  rw [h0, hz, mul_zero]

theorem theorem2_exact_amplification (t : ℕ) (p_max : ℝ) (hp0 : 0 ≤ p_max)
    (hp1 : p_max ≤ 1) (hbit : IsExactTBitPhase t (phaseOfProbability p_max))
    (r : ℕ) :
    (∃ k : ℤ, phaseOfProbability p_max = (k : ℝ) / (2 : ℝ) ^ t) ∧
      probabilityOfPhase (phaseOfProbability p_max) = p_max ∧
      1 - badMass 0 r = 1 := by
  refine ⟨hbit, exact_phase_probability hp0 hp1, ?_⟩
  rw [badMass_zero]
  ring

end Qatlib.Papers.QMAAmplify09.MainResults.ExactAmplification
