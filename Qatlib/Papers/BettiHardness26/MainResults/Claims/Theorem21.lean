/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Copyright (c) 2026. All rights reserved.
-/
import Qatlib.Papers.BettiHardness26.MainResults.Model.BettiProblem

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 2.1 (Average-case hardness of Betti number estimation)

Strelchuk, Subramanian, Wesołowski, "Average-case hardness of Betti number estimation",
fixed arXiv:2609.12777v1 (2026-09-11). Source: Theorem 2.1, §4, p.10.

Let `k = k(n)` satisfy `(2+ε) log n < k < n^{1/2−ε}` and `d = k − 2`. Under Assumption 1
(classical planted-clique conjecture) no randomized polynomial-time algorithm estimates
`β_d(skel_d X(G))` to additive error `< ½` with success probability `≥ ½ + δ` over
`G ∼ D_k = ½G(n,1/2) + ½G(n,1/2,k)`. Under Assumption 2 (quantum planted-clique conjecture) the
same holds for quantum polynomial-time algorithms with classical output.

Both statements are the two halves proved in `Model/BettiProblem.lean`
(`theorem_2_1_classical`, `theorem_2_1_quantum`); this file records them at the paper-layer
with the paper's `D_k`-mixture interpretation: `AdditiveSuccess` is the success probability over
the balanced mixture, `ClassicalPCConjecture`/`QuantumPCConjecture` are Assumptions 1/2, and the
planted lower value `β ≥ 1` is Lemma 4.2.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BettiHardness26.MainResults.Claims

open Qatlib.Papers.BettiHardness26.MainResults.Model

variable {Γ : Type*} [Fintype Γ]

/-- **Theorem 2.1 (classical half), §4, p.10.** Under Assumption 1, for every `δ ≥ 0`, no
efficient algorithm estimates `β_{k−2}(skel_{k−2} X(G))` to additive error `< ½` with success
probability `≥ ½ + δ` over the balanced mixture `D_k`, provided the planted value satisfies
`β ≥ 1` (Lemma 4.2). -/
theorem theorem_2_1_classical (M : EffModel Γ) (s : Setup Γ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : ClassicalPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est (1/2) ≥ 1/2 + δ :=
  Model.theorem_2_1_classical M s hδ hPlanted hpc

/-- **Theorem 2.1 (quantum half), §4, p.10.** Under Assumption 2, for every `δ ≥ 0`, no
efficient quantum algorithm with a classical output estimates `β_{k−2}(skel_{k−2} X(G))` to
additive error `< ½` with success probability `≥ ½ + δ` over `D_k`, provided `β ≥ 1` in the
planted case. -/
theorem theorem_2_1_quantum (M : EffModel Γ) (s : Setup Γ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hPlanted : ∀ g, s.mu1 g ≠ 0 → 1 ≤ s.beta g)
    (hpc : QuantumPCConjecture M s δ) :
    ¬ ∃ est : Γ → ℝ, M.EffEst est ∧ AdditiveSuccess s est (1/2) ≥ 1/2 + δ :=
  Model.theorem_2_1_quantum M s hδ hPlanted hpc

end Qatlib.Papers.BettiHardness26.MainResults.Claims
