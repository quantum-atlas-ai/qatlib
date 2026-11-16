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
# Source contract: Theorem 6.1 (arXiv:2408.07764v2, p.47, Eqs (297)–(306))

Consider a family of magic state distillation protocols using `[[n, k, d]]` codes
for `q`-dimensional qudits with decoding radius `t`, starting with `ζ = C n`
noisy `|CCZ⟩` states at physical error rate `p_ph`, distilling `k` magic states
`|M⟩` without post-selection, and converting them into at least `ξ(ζ) = k`
`|CCZ⟩` states. Under the local stochastic error model, if `k = Θ(n)` (Eq (297))
and `t = Θ(n)` (Eq (298)), then the protocol has a constant threshold
`p_th > 0` such that for `p_ph < p_th` the target error is suppressed as
`ε = (p_ph/p_th)^{O(ζ)} = exp(−O(ζ))` (Eq (299)) within constant overhead
`ζ/ξ(ζ) = O(1)` (Eq (300)).

The frozen result `constantOverheadDistillation` proves the analysis layer of
this theorem: the explicit threshold `p_th = exp(−binEntropy(cTl)/cTl)/C`, the
per-round tail bound of Eq (301)–(302), constant overhead `C·n/k ≤ C/cK`, and the
`∀ε ∃n₀` form of Eq (299). The protocol and decoder are not modelled.
-/

set_option autoImplicit false

namespace Qatlib.Papers.MagicDistill24.MainResults.Theorem61

/-- Fixed arXiv:2408.07764v2, Theorem 6.1 (p.47, Eqs (297)–(306)): under
`k = Θ(n)` and `t = Θ(n)` there is an explicit constant threshold `p_th > 0`
below which the error is suppressed as `C(n,t+1)(C p_ph)^(t+1) ≤ (p_ph/p_th)^(t+1)`,
the overhead `C·n/k` is bounded, and every `ε > 0` is attained for large `n`.
Reuses `MagicDistill.AnalysisLayer.constantOverheadDistillation`. -/
theorem source_theorem_6_1 :
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

end Qatlib.Papers.MagicDistill24.MainResults.Theorem61
