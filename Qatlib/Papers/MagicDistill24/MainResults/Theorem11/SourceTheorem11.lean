/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MagicDistill24.AnalysisLayer.ConstantOverheadDistillationCons

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Source contract: Theorem 1.1 (arXiv:2408.07764v2, p.4)

Constant-overhead magic state distillation for qubits is possible: there exist
constants `Ω, p_th` such that, for any target error rate `ε`, there is a large
enough `n` such that a supply of `n` `|CCZ⟩` magic states of error rate below
`p_th` may be used to produce `k` `|CCZ⟩` magic states of error rate below `ε`
under the local stochastic error model, with `n/k ≤ Ω`.

The frozen result `constantOverheadDistillation` (Section 6 analysis of
Theorem 6.1) establishes exactly this quantifier structure for the
triorthogonal-code protocol family: an explicit positive threshold
`p_th = exp(−binEntropy(cTl)/cTl)/C`, error suppression below `p_th`, constant
overhead `C·n/k ≤ C/cK` (the paper's `Ω`), and the `∀ε ∃n₀` target-error clause.
The physical protocol, the code-family supply and the decoder are not modelled
(the frozen note records this boundary).
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Theorem11

/-- Fixed arXiv:2408.07764v2, Theorem 1.1 (p.4) at the analysis level: from the
`k = Θ(n)`, `t = Θ(n)` code family there is an explicit threshold `p_th > 0`, the
error rate is suppressed below `p_th`, the overhead `C·n/k` is bounded by the
constant `C/cK` (the paper's `Ω`), and every target error rate `ε` is attained
for large enough `n`.
Reuses `MagicDistill.AnalysisLayer.constantOverheadDistillation`
(the `∀ε ∃n₀` clause is the Theorem 1.1 conclusion; the protocol/decoder are not modelled). -/
theorem source_theorem_1_1 :
    ∀ (C cK cTl cTh : ℝ), 1 ≤ C → 0 < cK → 0 < cTl → cTl ≤ cTh → cTh ≤ 1 →
      0 < Real.exp (-(Real.binEntropy cTl / cTl)) / C ∧
      ∀ (pPh : ℝ), 0 ≤ pPh → pPh < Real.exp (-(Real.binEntropy cTl / cTl)) / C →
        ∀ (n k t : ℕ), 0 < n →
          cK * (n : ℝ) ≤ (k : ℝ) → cTl * (n : ℝ) ≤ (t : ℝ) + 1 → (t : ℝ) + 1 ≤ cTh * (n : ℝ) →
          ((Nat.choose n (t + 1) : ℝ) * (C * pPh) ^ (t + 1)
              ≤ (pPh / (Real.exp (-(Real.binEntropy cTl / cTl)) / C)) ^ (t + 1))
          ∧ (C * (n : ℝ) / (k : ℝ) ≤ C / cK)
          ∧ (∀ ε > 0, ∃ n₀ : ℕ, ∀ n' ≥ n₀,
              (pPh / (Real.exp (-(Real.binEntropy cTl / cTl)) / C)) ^ (cTl * (n' : ℝ)) ≤ ε) :=
  Qatlib.Papers.MagicDistill24.AnalysisLayer.constantOverheadDistillation

end Qatlib.Papers.MagicDistill24.MainResults.Theorem11
