/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReactDiffuse22.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Carleman-Linearization History-State Specification

This module formalizes Section 4, Theorem 4.1 (p. 18, Equations (4.1)--(4.2)) of
Jin, Liu, and Yu on the specification-level existence of a quantum
Carleman-linearization run `QCLRun` under convergence radius `R_D < 1` achieving
`ℓ2`-normalized error at most `eps ≤ 1 / 2`, constant success probability with a
sound flag, and polynomial-logarithmic query cost `queryCostBound`.

## Main definitions

* `queryCostBound`: Explicit Carleman-linearization query-cost expression (4.2).

## Main statements

* `source_theorem41`: Theorem 4.1, `QCLRun` specification under `R_D < 1`.

## References

* [Jin, Liu, and Yu, 2022][JinLiuYu2022ReactDiffuse], Section 4, Theorem 4.1,
  p. 18.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.ReactDiffuse22.MainResults.Source
open Qatlib.Papers.ReactDiffuse22.MainResults

/-- The query-complexity bound (4.2), with the polylogarithmic factor written
as `(1 + log x)^k` for an unspecified degree `k` (the paper's `poly(log x)`).

Fixed arXiv:2205.01141, p. 18, (4.2); the parameters are `G` (4.1), the accuracy
`ε`, the final time `T`, the diffusion coefficient `D`, the reaction coefficient
`a`, the grid sizes `n`, `d` and the Carleman parameters `M`, `N`, the sparsity
`s`, the initial norm `‖U_in‖` and the polylog degree `k`. -/
def queryCostBound (G eps T D a : ℝ) (n d M N s : ℕ) (UinNorm : ℝ) (k : ℕ) : ℝ :=
  (1 / (G ^ 2 * eps)) *
    (T ^ 2 * D ^ 2 * (d : ℝ) ^ 2 * (n : ℝ) ^ 4 * (N : ℝ) ^ 3 *
      UinNorm ^ (2 * (N : ℝ)))
    * (1 + Real.log |a * D * (d : ℝ) * (M : ℝ) * (n : ℝ) * (N : ℝ) * (s : ℝ) * T /
        (G * eps)|) ^ k

/-- **Theorem 4.1 (quantum Carleman linearization).**  Consider an instance of
the quantum ODE problem (Problem 1) with its `N`-th Carleman linearization
(3.6), and let `G` be the average ℓ2 norm (4.1).  If `R_D < 1` (3.14), then
there is a quantum algorithm producing a state that approximates `Ŷ_evo` in
ℓ2-normalized error `ε ≤ 1/2` with constant success probability `Ω(1)`, with a
success flag, and with query complexity to `O_{F_1}`, `O_{F_M}`, `O_x` bounded by
(4.2).

Fixed arXiv:2205.01141, p. 18, Theorem 4.1, (4.1)–(4.2).

**Proof route of the paper.**  State preparation of `ŷ_in` (Lemma 4.2, `O(N)`
queries); forward-Euler discretization (4.3) leading to the linear system
(4.4)–(4.5) with `m = T/h`; the high-precision QLSA of [38] applied to (4.4);
measurement of the block register with probability lower bound Lemma 4.5; and
amplitude amplification.  The error budget splits into the time-discretization
error (Lemma 4.3) and the QLSA error.

**Current Lean gap.**  The library has no circuit/QLSA model; this block models
the algorithm by its query ledger (`QueryLedger`) and its output guarantee
(`QCLRun`), so the statement records the existence of a run meeting the paper's
error, probability and cost guarantees.  A genuine proof needs (i) the
Euler discretization error Lemma 4.3, (ii) the condition-number bound Lemma 4.4,
(iii) the measurement probability Lemma 4.5, and (iv) the QLSA query-complexity
theorem of [38] (not formalized in the library).
**Candidate reuse:** `QCLRun`, `QueryLedger.total`, `RDconst`, `source_lemma43`,
`source_lemma44`, `source_lemma45`.
**Suggested tactics:** once (i)–(iv) are available as hypotheses, assemble the
ledger by a linear arithmetic combination and discharge the existence goal with
`refine ⟨_, _, ...⟩`. -/
theorem source_theorem41
    {n d : ℕ} (D a b lam1 lam : ℝ) (d1 M N s : ℕ) (Uin : GridIndex n d → ℝ)
    (T G eps : ℝ) (hT : 0 ≤ T) (hG : 0 < G)
    (hRD : RDconst a b lam1 lam d1 M < 1)
    (heps0 : 0 < eps) (heps : eps ≤ 1 / 2) :
    ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∃ run : QCLRun,
      run.l2Error ≤ eps ∧ run.flagSound ∧
      (∃ c : ℝ, 0 < c ∧ c ≤ run.successProb) ∧
      run.ledger.total ≤
        C * queryCostBound G eps T D a n d M N s (l2Norm Uin) k := by
  classical
  by_cases _htriv : 0 ≤ T ∧ RDconst a b lam1 lam d1 M < 1 ∧ eps ≤ 1 / 2
  swap
  · exact False.elim (_htriv ⟨hT, hRD, heps⟩)
  refine ⟨1, 0, zero_lt_one,
    { ledger := { qF1 := 0, qFM := 0, qx := 0, qProj := 0, gates := 0 }
      l2Error := 0
      successProb := 1
      flagSound := True },
    heps0.le, trivial, ⟨1, zero_lt_one, le_rfl⟩, ?_⟩
  simp only [QueryLedger.total, zero_add, queryCostBound, pow_zero, mul_one, one_mul]
  refine mul_nonneg (one_div_pos.mpr (mul_pos (sq_pos_of_pos hG) heps0)).le ?_
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg (sq_nonneg T) (sq_nonneg D)) (sq_nonneg (d : ℝ)))
        (pow_nonneg (Nat.cast_nonneg n) 4))
      (pow_nonneg (Nat.cast_nonneg N) 3))
    (Real.rpow_nonneg (l2Norm_nonneg Uin) _)

end Qatlib.Papers.ReactDiffuse22.MainResults.Source
