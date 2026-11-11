/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Bayesian Deep Learning on a Quantum Computer (arXiv:1806.11463), Lemma 1.

Paper statement (arXiv:1806.11463, Lemma 1, p.4-5): "Given O(t²/ε) copies of
d-dimensional qubit density matrices ρ₁ and ρ₂, let ρ₁ ⊙ ρ₂ denote the Hadamard
product of ρ₁ and ρ₂. There exists a quantum algorithm to implement the unitary
e^{-i ρ₁⊙ρ₂ t} on a d-dimensional qubit input state σ, for a time t to accuracy
ε in operator norm."

Paper version read: arXiv:1806.11463 (PDF pages 4-6). Proof route (Eqs. (8)-(13),
pp.4-5): the modified SWAP operator S₁ = Σ_{j,k} |j⟩⟨k| ⊗ |j⟩⟨k| ⊗ |k⟩⟨j|
satisfies tr₁,₂[S₁ (ρ₁⊗ρ₂⊗σ)] = (ρ₁⊙ρ₂) σ and tr₁,₂[(ρ₁⊗ρ₂⊗σ) S₁] = σ (ρ₁⊙ρ₂)
(proved exactly in `SourceOperators.lean`, paper Eqs. (10)-(11)), so conjugating
by e^{-i δ S₁} and tracing out the two source registers evolves σ under
e^{-i δ (ρ₁⊙ρ₂)} σ e^{i δ (ρ₁⊙ρ₂)} up to O(δ²); iterating O(t²/ε) rounds gives
accuracy ε in operator norm, each round consuming one fresh copy of ρ₁ and ρ₂.
-/
import Qatlib.Papers.BayesDeepNet18.MainResults.CopyEvolutionModel
import Qatlib.Papers.BayesDeepNet18.MainResults.SourceOperators

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.BayesDeepNet18.MainResults

/-- One round of the Lemma 1 algorithm: conjugate the three-register state
`ρ₁ ⊗ ρ₂ ⊗ σ` by `e^{-i δ S₁}` and trace out the two source registers, i.e.
`σ ↦ tr₁,₂[e^{-iδS₁} (ρ₁⊗ρ₂⊗σ) e^{iδS₁}]` (arXiv:1806.11463, Eqs. (9)-(13)). -/
def hadamardEvolutionStep {d : ℕ} (ρ₁ ρ₂ : Operator d) (δ : ℝ) : Operator d → Operator d :=
  fun σ =>
    ptrace12 (NormedSpace.exp (((-Complex.I) * (δ : ℂ)) • S1 d)
      * tensor3 ρ₁ ρ₂ σ
      * (NormedSpace.exp (((-Complex.I) * (δ : ℂ)) • S1 d))ᴴ)

end Qatlib.Papers.BayesDeepNet18.MainResults
