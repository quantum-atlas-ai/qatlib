/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DoubleBracket25.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# DoubleBracket25 — supporting lemmas (fully proved)

Source: arXiv:2504.01077, accepted-Quantum version 2025-12-16.

This file collects elementary facts used by the claim files and proved here in
full:

* `pureDM_idem` — `Ψ² = Ψ` for `Ψ = |ψ⟩⟨ψ|` (Eq. (66));
* `pureDM_hermitian` — `Ψ` is Hermitian (used implicitly throughout);
* `unbiasedCorrection` — the bias-correction identity of Eq. (260)-(261):
  `N/(N-1)(p² + (1-p²)/N - 1/N) = p²`.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.DoubleBracket25.MainResults

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **Eq. (66)**, arXiv:2504.01077, App. B.2.1, p. 22: a pure density matrix is
idempotent, `Ψ² = Ψ`, for a normalized state (`⟨ψ|ψ⟩ = 1`). -/
theorem pureDM_idem (ψ : ι → ℂ) (hψ : vecInner ψ ψ = 1) :
    pureDM ψ * pureDM ψ = pureDM ψ := by
  ext i j
  simp only [pureDM, Matrix.mul_apply, Matrix.of_apply]
  rw [show (∑ k, ψ i * star (ψ k) * (ψ k * star (ψ j))) =
      (ψ i * star (ψ j)) * ∑ k, star (ψ k) * ψ k by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring]
  rw [show (∑ k, star (ψ k) * ψ k) = vecInner ψ ψ from rfl, hψ]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- `Ψ = |ψ⟩⟨ψ|` is Hermitian. -/
theorem pureDM_hermitian (ψ : ι → ℂ) : (pureDM ψ).IsHermitian := by
  ext i j
  simp only [pureDM, Matrix.conjTranspose_apply, Matrix.of_apply, star_mul, star_star]

/-- **Eq. (260)-(261)**, arXiv:2504.01077, App. F.2, p. 45: the bias-correction
identity underlying the unbiased variance estimator.  For `N ≥ 2`,

`N/(N-1) · (p² + (1-p²)/N - 1/N) = p²`. -/
theorem unbiasedCorrection (p : ℝ) (N : ℕ) (hN : 1 < N) :
    ((N : ℝ) / ((N : ℝ) - 1)) * (p ^ 2 + (1 - p ^ 2) / (N : ℝ) - 1 / (N : ℝ)) =
      p ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hN))
  have hN1pos : (0 : ℝ) < (N : ℝ) - 1 := by
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    linarith
  field_simp
  ring

end Qatlib.Papers.DoubleBracket25.MainResults
