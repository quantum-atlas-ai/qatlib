/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
Bayesian Deep Learning on a Quantum Computer (arXiv:1806.11463), Lemma 2.

Paper statement (arXiv:1806.11463, Lemma 2, p.5): "Given O(t²/ε) copies of
d-dimensional qubit density matrices ρ₁ and ρ₂, let ρ₁ ⊘ ρ₂ denote the outer
product of the diagonal entries of ρ₁ and ρ₂. There exists a quantum algorithm
to implement the unitary e^{-i ρ₁⊘ρ₂ t} on a d-dimensional qubit input state σ,
for a time t to accuracy ε in operator norm."

Paper version read: arXiv:1806.11463 (PDF pages 4-6). Proof route (Eqs. (14)-(15),
p.5): the modified SWAP operator S₂ = Σ_{j,k} |j⟩⟨j| ⊗ |k⟩⟨k| ⊗ |k⟩⟨j| satisfies
tr₁,₂[S₂ (ρ₁⊗ρ₂⊗σ)] = (ρ₁⊘ρ₂) σ and tr₁,₂[(ρ₁⊗ρ₂⊗σ) S₂] = σ (ρ₁⊘ρ₂) (proved
exactly in `SourceOperators.lean`), so conjugation by e^{-i δ S₂} and tracing out
the sources evolves σ under e^{-i δ (ρ₁⊘ρ₂)} σ e^{i δ (ρ₁⊘ρ₂)} up to O(δ²);
iterating O(t²/ε) rounds gives accuracy ε, consuming one fresh copy per round.
-/
import Qatlib.Papers.BayesDeepNet18.MainResults.CopyEvolutionModel
import Qatlib.Papers.BayesDeepNet18.MainResults.SourceOperators

set_option autoImplicit false
noncomputable section

open Matrix
open Qatlib.Foundations.PureStateMath
open scoped BigOperators Matrix.Norms.L2Operator

namespace Qatlib.Papers.BayesDeepNet18.MainResults

/-- One round of the Lemma 2 algorithm: conjugate the three-register state
`ρ₁ ⊗ ρ₂ ⊗ σ` by `e^{-i δ S₂}` and trace out the two source registers, i.e.
`σ ↦ tr₁,₂[e^{-iδS₂} (ρ₁⊗ρ₂⊗σ) e^{iδS₂}]` (arXiv:1806.11463, Eqs. (14)-(15)). -/
def diagOuterEvolutionStep {d : ℕ} (ρ₁ ρ₂ : Operator d) (δ : ℝ) : Operator d → Operator d :=
  fun σ =>
    ptrace12 (NormedSpace.exp (((-Complex.I) * (δ : ℂ)) • S2 d)
      * tensor3 ρ₁ ρ₂ σ
      * (NormedSpace.exp (((-Complex.I) * (δ : ℂ)) • S2 d))ᴴ)

end Qatlib.Papers.BayesDeepNet18.MainResults
