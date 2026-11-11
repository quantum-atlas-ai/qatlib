/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GibbsSampling25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Weak transport cost inequality (claim c009)

Theorem 2.10 of arXiv:2412.01732v1 (p.7, eq. (13)); general form in
Theorem B.5 (p.35, eq. (55)).
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder Kronecker

namespace Qatlib.Papers.GibbsSampling25.MainResults.Mixing

open Qatlib.Papers.GibbsSampling25.MainResults.Model
open Qatlib.Concepts.QuantumEntropy.EntropyCalculus

/-- **Theorem 2.10 (Weak transport cost inequality)**,
arXiv:2412.01732v1 p.7, eq. (13). Let `σ` be a Gibbs state of a local
commuting Hamiltonian on `Λ` satisfying a `(1, c₂)`-weak AT with respect to a
coarse-graining `{A_i}_{i=1}^{n_A}` (eq. (7)). Then it satisfies a
`(b₁,b₂)`-weak transport cost inequality with
`b₁ = 2√2 max_i √|A_i^∂|` and `b₂ = |Λ|√(2c₂)`:

`‖ρ − σ‖_{W¹} ≤ max_i 2√(2|A_i^∂|) √(n_A D(ρ‖σ)) + |Λ|√(2c₂)`.

`W1` is the normalized Wasserstein-1 distance (Definition 2.8, eqs. 9–10),
`shell i` is `|A_i^∂|`, `maxShell` bounds `2√(2|A_i^∂|)` over the
coarse-graining, and `hAT` records the weak AT hypothesis (54). -/
def weak_transport_cost_inequality {I : Type} [Fintype I] [DecidableEq I]
    (ρ σ : Density I) (W1 : WOneDist I) (nA : ℕ) (shell : ℕ → ℝ)
    (maxShell c₂ : ℝ) (hmax : ∀ i : ℕ, i < nA → 2 * Real.sqrt (2 * shell i) ≤ maxShell)
    (hmax_nonneg : 0 ≤ maxShell) (hc₂ : 0 ≤ c₂)
    (hAT : ∃ davies : ℕ → Density I → Density I,
      relEnt ρ σ ≤ (∑ i ∈ Finset.range nA, relEnt ρ (davies i ρ)) + c₂)  : Prop :=
    W1 ρ σ ≤ maxShell * Real.sqrt ((nA : ℝ) * relEnt ρ σ)
      + (Fintype.card I : ℝ) * Real.sqrt (2 * c₂)
  -- Source: arXiv:2412.01732v1, Theorem 2.10 (p.7, eq. (13)); proved as
  -- Theorem B.5 (p.35, eq. (55)).
  -- Proof route: by the dual formulation of the W1 distance
  -- (Definition 2.8, eqs. (9)–(10)),
  --   ‖ρ − σ‖_{W1} = sup_{‖∇f‖∞ ≤ 1} tr[f(ρ − σ)],
  -- and for each local observable `f` the weak AT (54) plus the
  -- Cauchy–Schwarz/Pinsker relation between `D(ρ‖E_{A_i}(ρ))` and the local
  -- gradient gives the bound; the `√(2|A_i^∂|)` factor comes from the number
  -- of boundary sites in `A_i`, and `|Λ|√(2c₂)` from the additive weak-AT
  -- error `c₂`.
  -- Lean gap: the W1 distance of Definition 2.8 (sup over gradients of
  -- Lipschitz observables, eqs. (9)–(10)), its dual formulation, and the
  -- interrelations between `D(ρ‖E_A(ρ))` and local gradients are not
  -- formalised. `W1` is an interface datum here; the weak AT enters through
  -- the hypothesis `hAT` with abstract channels `davies`.
  -- Candidate reusable dependencies: `relEnt`, `Real.sqrt_le_sqrt`,
  -- `Real.sqrt_mul`, `Finset.sum_le_sum`, `relEnt_nonneg`.
  -- Suggested continuation: first formalise the W1 distance and its dual
  -- `‖ρ − σ‖_W1 = sup_{Lip f ≤ 1} tr[f(ρ−σ)]` (Definition 2.8), then bound
  -- `tr[f(ρ−E_A ρ)]` by `√(2|A^∂|) √(D(ρ‖E_A ρ))` (Pinsker + local
  -- Lipschitz constant), sum over `i`, and apply Cauchy–Schwarz with `hAT`.

end Qatlib.Papers.GibbsSampling25.MainResults.Mixing
