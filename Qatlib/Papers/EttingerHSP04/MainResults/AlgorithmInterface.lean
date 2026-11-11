/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.EttingerHSP04.MainResults.EttingerHSP04MainResults
import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-!
# Additional hidden-subgroup algorithm interfaces

Source: Ettinger–Høyer–Knill, *The quantum query complexity of the hidden subgroup
problem is polynomial*, arXiv:quant-ph/0401083v1 (2004).

The promoted state model supplies the periodicity and projector definitions.
This module adds the Lemma 3 identity and Lemma 6 probability formulation, plus
an abstract query/output interface and its query-count reduction. The interface
does not assert existence of the paper's complete algorithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.EttingerHSP04.MainResults

open Qatlib.Papers.EttingerHSP04.MainResults

open Qatlib.Foundations.PureStateMath
open scoped BigOperators Classical

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
variable {β : Type*} [Fintype β] [DecidableEq β]

/-! ## §1. Periodicity (paper §1, p.1) -/

/-- **Lemma 3** (paper p.4).  If `f` is `K_μ`-periodic then
`Test_μ |Ψ_init⟩ = |μ⟩|1⟩ ⊗ (N^{-1/2} ∑_g |g⟩|f(g)⟩)^{⊗s}`.  In the model here
`Test_μ = Q_μ ⊗ P_{s,μ} + I ⊗ P^⊥_{s,μ}` (`testFun`), the initial state is the
product `|μ⟩ ⊗ (initial couplet)^{⊗s}` (`prodState` with `multisetState`), and
the `K_μ`-periodicity makes the `s`-fold projector `P_{s,μ}` fix the couplet
factor (`projS_fixes_multisetState_of_periodic`).  The control register is
`σ` with `Q_μ q = q`, i.e. `|μ⟩` is the `+1`-eigenvector of `Q_μ`. -/
theorem lemma3_test_identity
    {σ : Type*} (Q : QState σ →ₗ[ℂ] QState σ) {K : Subgroup G} {f : G → β}
    (hf : IsHPeriodic f K) (s : ℕ) (q : QState σ) (hQ : Q q = q) :
    testFun Q (projSLM K s) (prodState q (multisetState (initialCouplet f) s)) =
      prodState q (multisetState (initialCouplet f) s) := by
  have hP : projSLM K s (multisetState (initialCouplet f) s) =
      multisetState (initialCouplet f) s :=
    projS_fixes_multisetState_of_periodic hf s
  rw [testFun_prodState_of_fixed Q (projSLM K s) q _ hP, hQ]

/-! ## §10. Lemma 4: the distance bound for a non-periodic subgroup (paper p.4–5) -/

/-- **Lemma 6** (paper p.6).  In the `ExactTest` construction the ancilla
probability vector is `y = M x` with every entry equal to `1/4` or `3/4`; hence
measuring the ancilla in the computational basis returns `1` with probability
`3/4` when `H ∈ Y_{3/4}` and `1/4` when `H ∈ Y_{1/4}`.  Stated as the elementary
finite linear-algebra core: the `ν`-th ancilla probability `(M x)_ν` is `1/4` or
`3/4` whenever the target vector `y` has that property. -/
theorem lemma6_ancilla_probability {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ)
    (x y : Fin r → ℝ) (hMx : M.mulVec x = y)
    (hy : ∀ ν, y ν = 1/4 ∨ y ν = 3/4) (ν : Fin r) :
    (∑ μ, M ν μ * x μ) = 1/4 ∨ (∑ μ, M ν μ * x μ) = 3/4 := by
  have h : (∑ μ, M ν μ * x μ) = y ν := by
    rw [← congrFun hMx ν]
    rfl
  rw [h]
  exact hy ν

/-- An abstract quantum algorithm for the hidden subgroup problem on a finite
group `G` with oracle values in `β` (paper Theorem 1, p.2): it makes a fixed
number of oracle queries and, for each oracle `f`, returns a probability
distribution over candidate generating sets `S ⊆ G`. -/
structure HSPAlgorithm (G β : Type*) [Fintype G] [DecidableEq G] where
  /-- Number of oracle queries used by the algorithm. -/
  queries : ℕ
  /-- Distribution over candidate generating sets for each oracle. -/
  outputDist : (G → β) → Finset G → ℝ
  /-- Every candidate generating set receives nonnegative probability. -/
  outputDist_nonneg : ∀ (f : G → β) (S : Finset G), 0 ≤ outputDist f S
  /-- The probabilities of all candidate generating sets sum to one. -/
  outputDist_sum : ∀ f : G → β, ∑ S : Finset G, outputDist f S = 1

/-- The success probability of an HSP algorithm on oracle `f`: the total
probability of those outputs whose closure is the hidden subgroup `H` (paper
Theorem 1, p.2, "outputs a generating set for `H`"). -/
noncomputable def HSPAlgorithm.successProb {G β : Type*} [Group G] [Fintype G] [DecidableEq G]
    (alg : HSPAlgorithm G β) (f : G → β) (H : Subgroup G) : ℝ :=
  ∑ S : Finset G, if Subgroup.closure (S : Set G) = H then alg.outputDist f S else 0

end Qatlib.Papers.EttingerHSP04.MainResults
