/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Two-Sided Linear Cross-Entropy Benchmark Bounds for Noisy Random Circuits

This module formalizes Theorem 4 (p. 15, Equations (58)--(60)) of Aharonov et al.,
deriving both the `(1 - γ)^{d + 1} W_{d + 1}` lower bound and the `C_0 e^{-γ d}`
exponential decay upper bound on the linear cross-entropy benchmark `XEB` of a
noisy random circuit with depolarizing rate `γ ∈ [0, 1]`.

## Main statements

* `source_theorem4_noisy_xeb`: Theorem 4, two-sided `XEB` sandwich for noisy
  random circuits under zero low-degree Fourier weight and bounded tail weight.

## References

* [Aharonov et al., 2022][AharonovEtAl2022Noisy], Theorem 4, p. 15.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.XEB

open BigOperators

/-- Fixed arXiv:2211.03999v1, Theorem 4, p.15, Eq. (59): the two-sided XEB bound.  The
hypotheses encode Eq. (58) and the output of Lemmas 4 and 6 (see the file docstring). -/
theorem source_theorem4_noisy_xeb
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (n d N : ℕ) (hd : 1 ≤ d) (hdN : d + 1 ≤ N)
    (W : ℕ → ℝ) (C0 XEB : ℝ) (hC0 : 0 ≤ C0)
    (hWnonneg : ∀ k, 0 ≤ W k)
    (hXEB : XEB = ∑ k ∈ Finset.Ico 1 (N + 1), (1 - γ) ^ k * W k)
    (hzero : ∀ k, 0 < k → k ≤ d → W k = 0)
    (hWd : W (d + 1) = (n : ℝ) * (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * (1 / 15) ^ d)
    (htail : ∑ k ∈ Finset.Ico (d + 1) (N + 1), W k ≤ C0) :
    (1 - γ) ^ (d + 1) * ((n : ℝ) * (2 : ℝ) ^ d * (3 : ℝ) ^ (d - 1) * (1 / 15) ^ d) ≤ XEB ∧
      XEB ≤ C0 * Real.exp (-(γ * d)) := by
  classical
  by_cases _htriv : (hd = hd ∧ hC0 = hC0)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  have hlow : ∑ k ∈ Finset.Ico 1 (d + 1), (1 - γ) ^ k * W k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rcases Finset.mem_Ico.mp hk with ⟨hk1, hkd⟩
    rw [hzero k (by omega) (by omega), mul_zero]
  have hXEBtail : XEB = ∑ k ∈ Finset.Ico (d + 1) (N + 1), (1 - γ) ^ k * W k := by
    rw [hXEB, ← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ d + 1)
      (by omega : d + 1 ≤ N + 1), hlow, zero_add]
  have hbase0 : 0 ≤ 1 - γ := by linarith
  have hbase1 : 1 - γ ≤ 1 := by linarith
  constructor
  · rw [hXEBtail, ← hWd]
    exact Finset.single_le_sum
      (fun k _ => mul_nonneg (pow_nonneg hbase0 k) (hWnonneg k))
      (show d + 1 ∈ Finset.Ico (d + 1) (N + 1) from
        Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩)
  · have hexp : (1 - γ) ^ d ≤ Real.exp (-(γ * (d : ℝ))) := by
      calc
        (1 - γ) ^ d ≤ (Real.exp (-γ)) ^ d :=
          pow_le_pow_left₀ hbase0 (by linarith [Real.add_one_le_exp (-γ)]) d
        _ = Real.exp (-(γ * (d : ℝ))) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
    calc
      XEB = ∑ k ∈ Finset.Ico (d + 1) (N + 1), (1 - γ) ^ k * W k := hXEBtail
      _ ≤ ∑ k ∈ Finset.Ico (d + 1) (N + 1), Real.exp (-(γ * (d : ℝ))) * W k := by
        apply Finset.sum_le_sum
        intro k hk
        have hdk : d ≤ k := by
          have := (Finset.mem_Ico.mp hk).1
          omega
        exact mul_le_mul_of_nonneg_right
          ((pow_le_pow_of_le_one hbase0 hbase1 hdk).trans hexp) (hWnonneg k)
      _ = (∑ k ∈ Finset.Ico (d + 1) (N + 1), W k) * Real.exp (-(γ * d)) := by
        rw [← Finset.mul_sum, mul_comm]
      _ ≤ C0 * Real.exp (-(γ * d)) :=
        mul_le_mul_of_nonneg_right htail (Real.exp_nonneg _)

end Qatlib.Papers.NoisyCircuit22.MainResults.XEB
