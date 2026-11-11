/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Convergence of classical simulated annealing: the norm bound

Source: R. D. Somma, S. Boixo, H. Barnum, *Quantum Simulated Annealing*,
fixed arXiv:0712.1008v1 (6 Dec 2007). Local PDF `local archive
tmp/prove/assets/0712.1008.pdf`, text twin `0712.1008.txt`.

This file covers Appendix A, Eqs. (A7) and (A16)–(A18), pp.5–6.

The paper's annealing-rate condition Eq. (A7), `Δβ E_M ≤ τδ` with `τ = O(1)`,
is used to absorb the `O(δ²)` terms of the Taylor expansions (A10)–(A15) and
obtain the one-step inequality (A16),

  `Δ‖h(βk)‖₂² ≤ −δ ‖h(βk)‖₂² + 2δ`.

Iterating (A16) from `‖h(0)‖₂ = 1` gives Eq. (A18),
`‖h(βk)‖₂² ≤ 2 − (1−δ)^k ≤ 2`, hence `‖h(βf)‖₂ ≤ √2`.

Boundary of the formalization: the `O(δ²)` bookkeeping of (A10)–(A15) is not
reconstructed (it needs the explicit eigenvectors of `H(βk)`); its displayed
output is Eq. (A16), taken as the one-step hypothesis.  Everything from (A16)
to `‖h‖₂ ≤ √2` is proved.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.SourceNormConvergence

/-- Fixed arXiv:0712.1008v1, Eq. (A17)–(A18), pp.5–6: iterating
`b(k+1) ≤ (1−δ) b(k) + 2δ` from `b(0) = 1` gives
`b(k) ≤ 2 − (1−δ)^k`. -/
theorem eqA18_norm_sq_bound
    (δ : ℝ) (b : ℕ → ℝ) (hδ1 : δ ≤ 1)
    (hb0 : b 0 = 1) (hrec : ∀ k, b (k + 1) ≤ (1 - δ) * b k + 2 * δ) :
    ∀ k, b k ≤ 2 - (1 - δ) ^ k := by
  intro k
  induction k with
  | zero => rw [hb0]; norm_num
  | succ k ih =>
      have h1δ : 0 ≤ 1 - δ := by linarith
      have hstep := hrec k
      have hpow : (1 - δ) ^ (k + 1) = (1 - δ) ^ k * (1 - δ) := pow_succ _ k
      have hmul : (1 - δ) * b k ≤ (1 - δ) * (2 - (1 - δ) ^ k) :=
        mul_le_mul_of_nonneg_left ih h1δ
      rw [hpow]
      nlinarith [hmul]

/-- Fixed arXiv:0712.1008v1, Eqs. (A7), (A16)–(A18), pp.5–6: under the
annealing-rate condition Eq. (A7) (whose role is to produce the one-step
inequality (A16) after absorbing `O(δ²)`), the squared norm obeys
`‖h(βk)‖₂² ≤ 2 − (1−δ)^k ≤ 2`, and therefore `‖h(βf)‖₂ ≤ √2`. -/
theorem a7_implies_norm_le_sqrt_two
    (δ Δβ EM τ : ℝ) (b : ℕ → ℝ)
    (hδ1 : δ ≤ 1) (_hA7 : Δβ * EM ≤ τ * δ)
    (hb0 : b 0 = 1)
    (hA16 : ∀ k, b (k + 1) - b k ≤ -δ * b k + 2 * δ) :
    (∀ k, b k ≤ 2) ∧ (∀ k, Real.sqrt (b k) ≤ Real.sqrt 2) := by
  have hrec : ∀ k, b (k + 1) ≤ (1 - δ) * b k + 2 * δ := by
    intro k
    linarith [hA16 k]
  have hb := eqA18_norm_sq_bound δ b hδ1 hb0 hrec
  have h1δ : 0 ≤ 1 - δ := by linarith
  refine ⟨fun k => ?_, fun k => ?_⟩
  · have hpow : 0 ≤ (1 - δ) ^ k := pow_nonneg h1δ k
    linarith [hb k, hpow]
  · exact Real.sqrt_le_sqrt (by
      have hpow : 0 ≤ (1 - δ) ^ k := pow_nonneg h1δ k
      linarith [hb k, hpow])

end Qatlib.Papers.QAnnealing07.MainResults.SourceNormConvergence
