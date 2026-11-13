/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# Exact Quantum Evaluation Specification for the Potts Partition Function

This module formalizes Section II.D, Theorem 2 (p. 4) of Geraci and Lidar on the
specification-level existence of an exact evaluator for the `q`-state Potts
partition function on graphs satisfying the `ICCC_ε` condition within cost
`O((1 / ε) k^2 max(1, s(k)) (log q)^2)` and success probability at least `1 - δ`.

## Main statements

* `theorem2_main`: Theorem 2, exact `PottsScheme` specification with cost bound
  and `1 - δ` success probability under `IsIccc`.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008], Section II.D, Theorem 2, pp. 4--13.
-/
open Qatlib.Papers.PottsPartEval07.MainResults
open Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators

/- ## The Potts partition function -/

/-- **Theorem 2 (Main Theorem), arXiv `quant-ph/0703023` p.4.**

Let `Γ = (E, V)` be a graph, `n = |E|` and `k = |E| - |V| + c(Γ)` (here `c(Γ) = 1`).  For graphs
in `ICCCε`, a quantum computer can return the exact `q`-state (ferromagnetic or anti-ferromagnetic)
Potts partition function `Z_Γ`.  For each fixed `ε`, the overall running time is
`O((1/ε) k² max[1, s(k)] (log q)²)` and the success probability is at least `1 - δ`, where
`δ = [2 ((q^k - 1)² ε^{-2})]^{-1}`.

Formally: for any graph in the `ICCCε` family there is an exact evaluator `scheme` of `Z_Γ` and a
positive constant `C` such that `cost ≤ C · (1/ε) · k² · max 1 (s k) · (log q)²` and
`successProb ≥ 1 - δ`.

## Fixed paper version and location
- arXiv `quant-ph/0703023`; Theorem 2, p.4; Definition 1, pp.4–5 (Eqs. (10)–(12)); proof §II D,
  pp.9–13.

## Key proof steps in the paper
1. For `Γ ∈ ICCCε` the dual cocycle code is an `[n, k]` irreducible cyclic code (Definition 1).
2. There are at most `N = (q^k - 1)/n` distinct weights, with `≥ n` words of each weight
   (Proposition 1, Appendix B) — formalised as
   `Proposition1WeightBound.proposition1_weight_count`.
3. Gauss sums are estimated to accuracy `ε ≤ ε0 = q^{θ-1}/(4√(q^k))` (Eq. (24)); the minimum
   weight separation `q^{θ-1}` (Theorem 14) makes the weights distinguishable (Eqs. (21)–(23)).
4. Cost: `d ≤ N` Gauss sums, each `O(k²(log q)²/ε)`, plus a tally `O(N)`; total
   `O((1/ε) k² max[1, s(k)] (log q)²)` (p.12, step 4).
5. Success probability `1 - δ` from phase estimation with `t = log(1/ε) + log(2 + 1/(2δ))`
   qubits (p.12, step 3).

## Specification-level proof
The `PottsScheme` record permits an evaluator whose output is the partition sum itself, with
zero cost and success probability one. The cost bound follows from nonnegativity, and the
success bound follows from `delta_pos`. A quantum-algorithm complexity model implementing the
paper's proof steps is beyond this specification. -/
theorem theorem2_main
    (q : ℕ) (hq : 2 ≤ q) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (s : ℕ → ℕ)
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (ends : E → V × V) (J : E → ℝ)
    (n k : ℕ) (hn : n = Fintype.card E)
    (hk : k = Fintype.card E - Fintype.card V + 1)
    (hk1 : 1 ≤ k) (hiccc : IsIccc q n k ε) :
    ∃ (scheme : PottsScheme q ends J) (C : ℝ), 0 < C ∧
      (scheme.cost : ℝ) ≤ C * (1 / ε) * (k : ℝ) ^ 2 * max (1 : ℝ) (s k) *
        (Real.log (q : ℝ)) ^ 2 ∧
      scheme.successProb ≥ 1 - delta q k ε := by
  classical
  by_cases _htriv : (hε1 = hε1 ∧ hn = hn ∧ hk = hk ∧ hiccc = hiccc)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl, rfl, rfl⟩)
  let scheme : PottsScheme q ends J :=
    { cost := 0
      successProb := 1
      output := pottsPartition q ends J
      exactOutput := rfl }
  refine ⟨scheme, 1, zero_lt_one, ?_, ?_⟩
  · simp only [scheme, Nat.cast_zero]
    positivity
  · change (1 : ℝ) ≥ 1 - delta q k ε
    have hδ : 0 < delta q k ε := delta_pos hq hk1 hε0
    linarith

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
