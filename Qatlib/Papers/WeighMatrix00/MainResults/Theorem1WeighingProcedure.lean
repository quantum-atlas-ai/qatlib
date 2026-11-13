/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.WeighMatrix00.MainResults.WeighingMatrix
import Qatlib.Papers.WeighMatrix00.MainResults.Lemma1StateConstruction

/-!
# Weighing-matrix source-state procedures

Normalized rows of a positive-weight weighing matrix have unit self-pairing and zero pairing for
distinct rows. The record `WeighingProcedure` packages these amplitudes with the
state-preparation query count and yields the numerical bound of
`source_theorem1_weighingProcedure`.

This development forms part of the formalization of [VanDam2002].

## Main statements

* `WeighingProcedure`: A record of a query count and normalized weighing-matrix row amplitudes,
  with normalization and orthogonality proofs.
* `source_theorem1_weighingProcedure`: A positive-weight weighing matrix with `k ≤ n` possesses
  a procedure with at most `ceil (π / 4 * sqrt (n / k)) + 1` calls, and at most one call when `k
  = n`.

## References

* [van Dam, 2002][VanDam2002]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.WeighMatrix00.MainResults

open scoped BigOperators

/-- A record of a query count and normalized weighing-matrix row amplitudes, with normalization
and orthogonality proofs. -/
structure WeighingProcedure {n k : ℕ} (M : WeighingMatrix n k) where

  oracleCalls : ℕ

  amplitude : Fin n → Fin n → ℂ

  isSourceState : ∀ s i, amplitude s i = (M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)

  orthogonal : ∀ s r, s ≠ r → ∑ i : Fin n, amplitude s i * amplitude r i = 0

  norm : ∀ s, ∑ i : Fin n, amplitude s i * amplitude s i = 1

namespace WeighingProcedure

variable {n k : ℕ} {M : WeighingMatrix n k}

/-- For positive weight, distinct rows scaled by `sqrt k` have zero bilinear amplitude pairing. -/
theorem sourceStates_orthogonal (hk : 0 < k) (s r : Fin n) (hsr : s ≠ r) :
    ∑ i : Fin n, ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) *
      ((M.mat r i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) = 0 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hc : ((Real.sqrt (k : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hk0))
  have hterm : ∀ i : Fin n,
      ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) *
        ((M.mat r i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) =
      ((M.mat s i : ℂ) * (M.mat r i : ℂ)) / ((Real.sqrt (k : ℝ) : ℂ)) ^ 2 := by
    intro i
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  have hz : ∑ i : Fin n, ((M.mat s i : ℂ) * (M.mat r i : ℂ)) = 0 := by
    have h := M.gram_apply s r
    rw [if_neg hsr] at h
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at hcast
    simpa using hcast
  rw [hz]
  simp

/-- For positive weight, each row scaled by `sqrt k` has bilinear self-pairing one. -/
theorem sourceStates_norm (hk : 0 < k) (s : Fin n) :
    ∑ i : Fin n, ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) *
      ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) = 1 := by
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hterm : ∀ i : Fin n,
      ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) *
        ((M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)) =
      ((M.mat s i : ℂ) * (M.mat s i : ℂ)) / ((Real.sqrt (k : ℝ) : ℂ)) ^ 2 := by
    intro i
    field_simp
  simp_rw [hterm]
  rw [← Finset.sum_div]
  have hd : ∑ i : Fin n, ((M.mat s i : ℂ) * (M.mat s i : ℂ)) = (k : ℂ) := by
    have h := M.gram_apply s s
    rw [if_pos rfl] at h
    have hcast := congrArg (fun z : ℤ => (z : ℂ)) h
    push_cast at hcast
    simpa using hcast
  rw [hd]
  have hsq : ((Real.sqrt (k : ℝ) : ℂ)) ^ 2 = (k : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hk0.le]
    simp
  rw [hsq]
  exact div_self (by exact_mod_cast hk.ne')

/-- The weighing procedure using normalized rows and `statePreparationCalls n k` oracle calls. -/
def sourceProcedure (hk : 0 < k) : WeighingProcedure M where
  oracleCalls := statePreparationCalls n k
  amplitude := fun s i => (M.mat s i : ℂ) / (Real.sqrt (k : ℝ) : ℂ)
  isSourceState := fun _ _ => rfl
  orthogonal := fun s r hsr => sourceStates_orthogonal hk s r hsr
  norm := fun s => sourceStates_norm hk s

end WeighingProcedure

/-- A positive-weight weighing matrix with `k ≤ n` possesses a procedure with at most `ceil (π /
4 * sqrt (n / k)) + 1` calls, and at most one call when `k = n`. See [VanDam2002]. -/
theorem source_theorem1_weighingProcedure {n k : ℕ} (M : WeighingMatrix n k)
    (hk : 0 < k) (hkn : k ≤ n) :
    ∃ P : WeighingProcedure M,
      P.oracleCalls ≤ Nat.ceil (Real.pi / 4 * Real.sqrt ((n : ℝ) / (k : ℝ))) + 1 ∧
      (k = n → P.oracleCalls ≤ 1) := by
  refine ⟨WeighingProcedure.sourceProcedure (M := M) hk, ?_, ?_⟩
  · exact (source_lemma1_stateConstruction hk hkn).1
  · intro hkn_eq
    simpa [WeighingProcedure.sourceProcedure, hkn_eq] using
      (source_lemma1_stateConstruction hk hkn).2.1

end Qatlib.Papers.WeighMatrix00.MainResults
