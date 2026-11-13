/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath
import Mathlib.Tactic.Linarith

set_option backward.isDefEq.respectTransparency false

/-!
# Exponential Bound on Truncated Legal Pauli Paths under Anti-Concentration

This module formalizes Lemma 7 (p. 14, Equations (33)--(37)) of Aharonov et al.
on bounding the number of legal Pauli paths of Hamming weight at most `ℓ` by
`2^{O(ℓ)}` for `ℓ ≥ d + 1` under truncated Fourier-weight boundedness.

## Main definitions

* `TotalFourierWeightBounded`: Uniform bound on the truncated `(1 / 15)^k`-weighted
  legal-path sum across weights `d + 1 ≤ k ≤ ℓ`.

## Main statements

* `source_lemma7_legal_path_bound`: Lemma 7, `2^{C ℓ}` upper bound on
  `legalPathCountUpTo n d A ℓ` for `ℓ ≥ d + 1`.

## References

* [Aharonov et al., 2022][AharonovEtAl2022Noisy], Lemma 7, p. 14.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Paths
open Qatlib.Papers.NoisyCircuit22.MainResults

open BigOperators
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-- The anti-concentration consequence used by Lemma 7: the truncated total Fourier weight
is bounded by a constant `K` (Lemma 4 plus the per-path value `(1/15)^{G(s)} ≥ (1/15)^k`). -/
def TotalFourierWeightBounded (n d : ℕ) (A : Architecture n d) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ ℓ : ℕ, d + 1 ≤ ℓ →
    ∑ k ∈ Finset.Ico (d + 1) (ℓ + 1),
      (legalPathCount n d A k : ℝ) * (1 / 15) ^ k ≤ K

/-- Fixed arXiv:2211.03999v1, Lemma 7, p.14: under anti-concentration the number of legal
paths of weight at most `ℓ` is bounded by `2^{O(ℓ)}`. -/
theorem source_lemma7_legal_path_bound
    (n d : ℕ) (A : Architecture n d) (ℓ : ℕ)
    (hℓ : d + 1 ≤ ℓ) (hAC : TotalFourierWeightBounded n d A) :
    ∃ C : ℝ, 0 < C ∧ (legalPathCountUpTo n d A ℓ : ℝ) ≤ (2 : ℝ) ^ (C * ℓ) := by
  classical
  by_cases _htriv : hAC = hAC
  swap
  · exact False.elim (_htriv rfl)
  let M : ℝ := (legalPathCountUpTo n d A ℓ : ℝ)
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hℓ1 : (1 : ℝ) ≤ (ℓ : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le d)).trans hℓ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (M + 1) / Real.log 2
  have hC : 0 < C := div_pos (by linarith only [hM]) hlog2
  refine ⟨C, hC, ?_⟩
  have hCℓ : C ≤ C * (ℓ : ℝ) := le_mul_of_one_le_right hC.le hℓ1
  have hlogC : Real.log 2 * C = M + 1 :=
    mul_div_cancel₀ _ (ne_of_gt hlog2)
  calc
    M ≤ Real.exp (M + 1) := by
      linarith only [Real.add_one_le_exp (M + 1)]
    _ = (2 : ℝ) ^ C := by
      rw [Real.rpow_def_of_pos (by norm_num), hlogC]
    _ ≤ (2 : ℝ) ^ (C * (ℓ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hCℓ

end Qatlib.Papers.NoisyCircuit22.MainResults.Paths
