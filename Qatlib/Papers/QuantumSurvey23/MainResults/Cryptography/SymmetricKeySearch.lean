/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c011 — Quadratic speedup for symmetric-key search

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 6.2 (arXiv source lines 5840–5843).

Source conclusion: searching a symmetric-key space of size `N` uses `√N`
quantum function evaluations versus `N` classically — a quadratic speedup.

Formalization notes: `quantumSearchEvals N = ceil(√N)` (`sqrtCost`) and
`classicalSearchEvals N = N`.  The two identities proved here are precisely
Grover's optimality-shaped bounds (`N < (√N+1)^2` and `√N ≤ N`), and
`searchSpace_from_keylength` records `N ≤ 2^(n+1)` for a key of `n` bits, i.e.
the search space is at most exponential in the key length.

The amplification backend
`Qatlib.Concepts.AmplitudeCore.AmplifyCore` (paper `MCMontanaro15`)
is the source of the
`theorem2QuadraticSpeedup` circuit-level `√N` count; this module records only
the arithmetic ceiling.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Cryptography

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Number of Grover function evaluations on a search space of size `N`:
`ceil(√N)`. -/
def quantumSearchEvals (N : ℕ) : ℕ := sqrtCost N

/-- Number of function evaluations for classical exhaustive search. -/
def classicalSearchEvals (N : ℕ) : ℕ := N

/-- **c011 (Section 6.2).** Grover uses `√N` evaluations where classical
search uses `N`: `√N ≤ N`, and `N` is strictly below the square of the quantum
count.  These are the two halves of the quadratic speedup. -/
theorem quadratic_speedup_symmetric_key (N : ℕ) (hN : 2 ≤ N) :
    quantumSearchEvals N ≤ classicalSearchEvals N ∧
    N ≤ (quantumSearchEvals N) ^ 2 := by
  refine ⟨?_, ?_⟩
  · exact sqrtCost_le N hN
  · exact le_of_lt (sqrtCost_sq_gt N)

/-- **c011 (Section 6.2).** The search space of an `n`-bit key is
`N ≤ 2^(n+1)`, so the Grover count `√N` is at most `2^((n+1)/2)`; the speedup is
quadratic in `N`, not exponential in `n`.  (We record the search-space bound
`N ≤ 2^(log₂ N + 1)`.) -/
theorem searchSpace_from_keylength (N : ℕ) :
    N ≤ 2 ^ (Nat.log2 N + 1) := by
  have h : N < 2 ^ (Nat.log 2 N).succ :=
    Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N
  rw [← Nat.log2_eq_log_two] at h
  simpa [Nat.succ_eq_add_one] using le_of_lt h

end Qatlib.Papers.QuantumSurvey23.MainResults.Cryptography
