/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Quasi-optimal sampling from Gibbs states (claim c006)

Theorem C.3 of arXiv:2412.01732v1 (p.45), which yields the main algorithmic
result Theorem 2.1: a quantum circuit that prepares an `ε`-approximation (in
normalized `W¹` distance) of a Gibbs state satisfying uniform MCMI decay, with
`O(polylog N, quasi-poly(1/ε²))` ancillas and
`O(N · quasi-poly(1/ε²) · polylog(N/ε²))` two-qubit gates.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Sampling

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-- **Theorem C.3 (Quasi-optimal sampling)**, arXiv:2412.01732v1 p.45, and the
main theorem Theorem 2.1 (p.2). Let `σ` be the Gibbs state of a `(κ,r)`-local,
commuting, `J`-bounded Hamiltonian on `Λ ⊂ ℤ^D` which satisfies uniform MCMI
decay. Then there is a quantum circuit that outputs a state `out` with
`‖out − σ‖_{W¹} ≤ ε` (normalized `W¹` distance) and uses

* `O(polylog N, quasi-poly(1/ε²), polylog(N/ε²))` ancilla qubits;
* `O(N · quasi-poly(1/ε²) · polylog(N/ε²))` two-qubit gates.

Formally, `N` is the lattice size, `normW1` is the normalized `W¹` distance and
the quasi-polynomial factors are written as `exp(a · (log(1/ε²)+1)^b)`. -/
def quasi_optimal_sampling {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {I : Type} [Fintype I] [DecidableEq I]
    (dist : Λ → Λ → ℝ) (mcmi : McmiNorm Λ) (σ : Density I)
    (normW1 : Density I → Density I → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hUniform : ∃ K ξ : ℝ, 0 < K ∧ 0 < ξ ∧ ∀ A C Dd : Finset Λ,
      mcmi A C Dd ≤ K * (Fintype.card Λ : ℝ) * Real.exp (- setDistOf dist A C / ξ))  : Prop :=
    ∃ (a : ℝ) (b : ℕ) (C₁ C₂ ancillas gates : ℝ) (out : Density I),
      0 < C₁ ∧ 0 < C₂ ∧ 0 ≤ ancillas ∧ 0 ≤ gates ∧
      ancillas ≤ C₁ * (Real.log ((Fintype.card Λ : ℝ)) + 1) ^ b
        * Real.exp (a * (Real.log (1 / ε ^ 2) + 1) ^ b)
        * (Real.log ((Fintype.card Λ : ℝ) / ε ^ 2) + 1) ^ b ∧
      gates ≤ C₂ * (Fintype.card Λ : ℝ)
        * Real.exp (a * (Real.log (1 / ε ^ 2) + 1) ^ b)
        * (Real.log ((Fintype.card Λ : ℝ) / ε ^ 2) + 1) ^ b ∧
      normW1 out σ ≤ ε
  -- Source: arXiv:2412.01732v1, Theorem C.3 (p.45) and Theorem 2.1 (p.2).
  -- Proof route: simulate the Davies semigroup `e^{t_mix^{W1}(ε) L_Λ}` with a
  -- Lindblad-simulation circuit (e.g. [CKBG23, Theorem III.2]); the diamond-norm
  -- simulation error `≤ ε` implies `W¹` closeness of the outputs, so that
  --   (1/N)‖ρ − σ‖_{W¹} ≤ (1/N)‖ρ − e^{t L_Λ}ρ‖_{W¹}
  --                     + (1/N)‖e^{t L_Λ}ρ − σ‖_{W¹} ≤ ε + ε,
  -- and the ancilla/gate counts follow from Theorem C.1's mixing time plus the
  -- `O(polylog)` overhead of the simulation.
  -- Lean gap: no circuit/gate model, no diamond-norm simulation theorem, and no
  -- concrete Lindblad-simulation construction is available in the imported API;
  -- the output state and the resource counts are existentially quantified
  -- interface data, with the *quantitative shape* of the paper's bound retained.
  -- Candidate reusable dependencies: `quasi_rapid_wasserstein_mixing`
  -- (Theorem 2.9), `WOneDist`, `Real.exp_le_exp`.
  -- Suggested continuation: model the circuit family concretely (gate count and
  -- ancilla count as functions of `(N, ε)`), formalise the Lindblad simulation
  -- theorem [CKBG23, Theorem III.2], and instantiate with the mixing time of
  -- Theorem C.1.

end Qatlib.Papers.GibbsSampling25.MainResults.Sampling
