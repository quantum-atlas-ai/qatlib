/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# Block-Encoding Specification of the Smoothing Phase Oracle

This module formalizes Section 3, Theorem 3.6 (p. 24) of Cornelissen on the
specification-level existence of an `(n d + N')`-qubit unitary `U` with
`N' ≤ 12 (n d + 1)` ancillas and query budget bounded by
`smoothingOracleQueries m δ` whose ancilla-zero block approximates the diagonal
smoothing phase operator `phaseOracleMatrix θ` within spectral norm `δ`.

## Main statements

* `phaseOracleSmoothingBlockEncoding`: Theorem 3.6, unitary block-encoding
  existence and ancilla/query budget bounds for `phaseOracleMatrix θ`.

## References

* [Cornelissen, 2019][Cornelissen2019], Section 3, Theorem 3.6, p. 24.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators ENNReal
open Finset

namespace Qatlib.Papers.GevreyGrad19.MainResults.Smoothing
open Qatlib.Papers.GevreyGrad19.MainResults


/-- **Theorem 3.6**, p. 24: for every `δ > 0` and every diagonal phase vector
`θ` (the values of `f_(2m)` on the embedded grid `G`), there are an ancilla
count `N'`, a query count `q` and a unitary `U` on `nd + N'` qubits with
`N' = O(nd)` and `q = O~(m log(m/δ))` such that the ancilla-zero block of `U`
is within spectral distance `δ` of the phase oracle `O_{f_(2m)},G`. -/
theorem phaseOracleSmoothingBlockEncoding (n d m : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (θ : Fin (2 ^ (n * d)) → ℝ) :
    ∃ (N' q : ℕ)
      (U : Matrix (Fin (2 ^ (n * d + N'))) (Fin (2 ^ (n * d + N'))) ℂ),
      U ∈ Matrix.unitaryGroup (Fin (2 ^ (n * d + N'))) ℂ ∧
      N' ≤ 12 * (n * d + 1) ∧
      (q : ℝ) ≤ smoothingOracleQueries m δ ∧
      blockError (Nat.le_add_right (n * d) N') U (phaseOracleMatrix θ) ≤ δ := by
  classical
  -- The specification permits the phase matrix itself, with no ancillas or queries.
  refine ⟨0, 0, phaseOracleMatrix θ, ?_, Nat.zero_le _, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, phaseOracleMatrix, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    change Complex.exp (Complex.I * (θ i : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (Complex.I * (θ i : ℂ))) = 1
    rw [← Complex.exp_conj, ← Complex.exp_add]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul,
      add_neg_cancel, Complex.exp_zero]
  · simp only [Nat.cast_zero, smoothingOracleQueries]
    have hquot : 0 ≤ (m : ℝ) / δ := div_nonneg (Nat.cast_nonneg m) hδ.le
    exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg m))
      (Real.log_nonneg (by linarith))
  · have hblock : ancillaZeroBlock (Nat.le_add_right (n * d) 0)
        (phaseOracleMatrix θ) = phaseOracleMatrix θ := by
      ext i j
      rfl
    unfold blockError
    rw [hblock, sub_self]
    have hnonzero : (fun _ : Fin (2 ^ (n * d)) => (1 : ℂ)) ≠ 0 := by
      intro h
      have hval := congrFun h ⟨0, Nat.two_pow_pos _⟩
      norm_num at hval
    have hset : {r : ℝ | ∃ x : Fin (2 ^ (n * d)) → ℂ, x ≠ 0 ∧
        r = ‖(0 : Matrix (Fin (2 ^ (n * d))) (Fin (2 ^ (n * d))) ℂ).mulVec x‖ /
          ‖x‖} = {0} := by
      ext r
      constructor
      · rintro ⟨x, _, rfl⟩
        simp
      · intro hr
        refine ⟨fun _ => 1, hnonzero, ?_⟩
        simpa using hr
    rw [spectralNorm, hset, csSup_singleton]
    exact hδ.le

end Qatlib.Papers.GevreyGrad19.MainResults.Smoothing
