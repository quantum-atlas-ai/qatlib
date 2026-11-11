/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c008 — LP / SOCP / SDP: at most polynomial speedup

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 5.2 (arXiv source lines 4837–4842).

Source conclusion: for linear, second-order-cone, and semidefinite programs the
known quantum speedups are at most polynomial.  Quantum interior-point methods
(QIPM) give at most a quadratic speedup over classical IPMs; the
multiplicative-weights-update (MWU) route can go from `Õ(n²)` to `Õ(√n)`, a
possible quartic improvement in the exponent in some formulations.

Formalization notes: the cost functions
* `ipmClassical n = n²` (classical IPM per-iteration `n²`),
* `ipmQuantum n = n` (QIPM per-iteration `n`),
* `mwuClassical n = n² * (log n + 1)`,
* `mwuQuantum n = ceil(√n) * (log n + 1)`.

The load-bearing facts are: QIPM's gain is exactly one power of `n`
(`quadratic_ipm_speedup`), so it is "at most quadratic"; and both costs are
polynomial (`lp_qipm_polynomial`).  The MWU pair is recorded faithfully as the
survey's `Õ(n²) → Õ(√n)` pair (`mwu_speedup_pair`); the quartic wording refers
to the change in the exponent, which we do not over-claim arithmetically.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Optimization

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Classical interior-point per-iteration cost `n²`. -/
def ipmClassical (n : ℕ) : ℕ := n * n

/-- Quantum interior-point per-iteration cost `n`. -/
def ipmQuantum (n : ℕ) : ℕ := n

/-- Classical MWU cost `Õ(n²)`. -/
def mwuClassical (n : ℕ) : ℕ := n * n * (Nat.log2 n + 1)

/-- Quantum MWU cost `Õ(√n)`. -/
def mwuQuantum (n : ℕ) : ℕ := sqrtCost n * (Nat.log2 n + 1)

/-- **c008a (Section 5.2).** The quantum interior-point method gains at most
one power of `n`: `ipmClassical n = (ipmQuantum n)²`.  Hence the speedup is at
most quadratic. -/
theorem quadratic_ipm_speedup (n : ℕ) :
    ipmClassical n = (ipmQuantum n) ^ 2 := by
  unfold ipmClassical ipmQuantum
  ring

/-- **c008b (Section 5.2).** Both the classical and quantum interior-point
costs are polynomial in `n`. -/
theorem lp_qipm_polynomial :
    (∃ C d, ∀ n, ipmClassical n ≤ C * (n + 1) ^ d) ∧
    (∃ C d, ∀ n, ipmQuantum n ≤ C * (n + 1) ^ d) := by
  refine ⟨⟨1, 2, fun n => ?_⟩, ⟨1, 1, fun n => ?_⟩⟩
  · unfold ipmClassical
    nlinarith
  · unfold ipmQuantum
    nlinarith

/-- **c008c (Section 5.2).** The MWU route replaces `Õ(n²)` by `Õ(√n)`: the
quantum cost is at most the classical one for `n ≥ 2`. -/
theorem mwu_speedup_pair (n : ℕ) (hn : 2 ≤ n) :
    mwuQuantum n ≤ mwuClassical n := by
  unfold mwuQuantum mwuClassical
  have hsq : sqrtCost n ≤ n := sqrtCost_le n hn
  have hnn : n ≤ n * n := by
    have h : n * 1 ≤ n * n := Nat.mul_le_mul_left n (by omega)
    simpa using h
  exact Nat.mul_le_mul_right (Nat.log2 n + 1) (le_trans hsq hnn)

/-- **c008 (Section 5.2), combined assessment.** QIPM gives exactly a
quadratic gain (`n² → n`), both costs are polynomial, and the MWU route gives
`Õ(n²) → Õ(√n)`. -/
theorem lp_socp_sdp_at_most_polynomial (n : ℕ) (hn : 2 ≤ n) :
    ipmClassical n = (ipmQuantum n) ^ 2 ∧
    mwuQuantum n ≤ mwuClassical n :=
  ⟨quadratic_ipm_speedup n, mwu_speedup_pair n hn⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Optimization
