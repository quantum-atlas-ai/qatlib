/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.CvpToSweep.SourceCvpToSweep

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — from `S|LWE⟩^phase` to CVP (Theorems 68 and Corollary 71)

Fixed arXiv:2310.00644v2.

* c027 Theorem 68, p.36: with an `S|LWE⟩^phase` solver taking `m` samples of uniform
  `a ∈ Z_q^n` with the fixed Gaussian amplitude `f(e)=exp(-π(e/(αq))²)` and time `T`, one
  solves `CVP_{L*,αq/r}` on `L*/R` with probability `1-2^{-Ω(n)}` in time
  `O((m²+mT)poly(n))`.
* c028 Corollary 71, p.38: the same with `3m²n²` states `|D_{L,r}⟩` as input (composing
  Theorem 68 with the CVP oracle of Theorem 61).

The closest-vector outputs are compared through `IsClosestPoint` (the library's
`closestVector` stub returns its argument, so the paper's `κ_{L*}(x)` is an explicit
parameter here).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Theorem 68, p.36.** Let `L` be an `n`-dimensional integer lattice, `ε ∈ (0,2^{-n})`,
`α ∈ (0,1/(5√n))`, `r > 4qη_ε(L)`, `R > max{2√(nr log r), √(2n)/αq}`. Assume a quantum
algorithm `A` that, given `m` samples of uniform `a ∈ Z_q^n` and the state
`γ_{2αq}^a` (Eq. (13) at width `2αq`), solves for the secret `s` in time `T` with
probability `1-2^{-Ω(n)}`. Then there is a quantum algorithm that, given a CVP instance
`x ∈ L*/R` and `3m²n` states `|D_{L,r}⟩`, outputs `κ_{L*}(x)` (the closest vector of `L*`
to `x`) with probability `1-2^{-Ω(n)}` in time `O((m²+mT)poly(n))`.

Gap: the `2m`-step search over `σ_j = αq√(1+(√2-1)j/(2m))` and the final verification by
classical LWE samples (pp.36–37), together with Theorem 63's state generation, are not
formalized. Candidate dependencies: `cvp_to_slwe_state` (Theorem 63), `cvp_query_answer`
(Theorem 61). -/
def cvp_solver_from_slwe {n m q : ℕ} [NeZero q]
    (B : Matrix (Fin n) (Fin n) ℤ) (Bd : Matrix (Fin n) (Fin n) ℚ)
    {α r : ℝ} (hα : 0 < α) (hr : 0 < r) (T : ℝ) (hSolve : SolvesSLwePhase n m q T) : Prop := ∃ A : QuantumAlgo
        (fun _ : ℕ => (Fin n → ℝ) × (Fin (3 * m * m * n) → QState (Fin n → ℤ)))
        (fun _ : ℕ => Fin n → ℝ),
      (∀ (x : Fin n → ℝ) (dg : Fin (3 * m * m * n) → QState (Fin n → ℤ))
          (κx : Fin n → ℝ),
        IsClosestPoint (dualLatticeSet Bd) x κx →
          1 - (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)) ≤
            A.successProb 0 (x, dg) (fun out => out = κx)) ∧
      ∃ C kk : ℝ, 0 < C ∧
        A.timeCost 0 ≤ C * ((m : ℝ) ^ 2 + (m : ℝ) * T) * (((n : ℝ) + 1) ^ kk)

/-- **Corollary 71, p.38.** With the same assumption as Theorem 68, there is an algorithm
that, given a CVP instance `x ∈ L*/R` and `3m²n²` states `|D_{L,r}⟩`, outputs `κ_{L*}(x)`
with probability `1-2^{-Ω(n)}` in time `O((m²+mT)poly(n))`.

Gap: composing Theorem 68 with the CVP oracle of Theorem 61 (the extra `√n` factor in the
number of states and the precision `R > max{2√(nr log r), √(2n)/αq, 2^{2n+1}n r λ_n(L*)/(αq)}`)
is not formalized. Candidate dependencies: `cvp_solver_from_slwe` (Theorem 68). -/
def cvp_closest_vector_from_slwe {n m q : ℕ} [NeZero q]
    (B : Matrix (Fin n) (Fin n) ℤ) (Bd : Matrix (Fin n) (Fin n) ℚ)
    {α r : ℝ} (hα : 0 < α) (hr : 0 < r) (T : ℝ) (hSolve : SolvesSLwePhase n m q T) : Prop := ∃ A : QuantumAlgo
        (fun _ : ℕ => (Fin n → ℝ) × (Fin (3 * m * m * n * n) → QState (Fin n → ℤ)))
        (fun _ : ℕ => Fin n → ℝ),
      (∀ (x : Fin n → ℝ) (dg : Fin (3 * m * m * n * n) → QState (Fin n → ℤ))
          (κx : Fin n → ℝ),
        IsClosestPoint (dualLatticeSet Bd) x κx →
          1 - (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)) ≤
            A.successProb 0 (x, dg) (fun out => out = κx)) ∧
      ∃ C kk : ℝ, 0 < C ∧
        A.timeCost 0 ≤ C * ((m : ℝ) ^ 2 + (m : ℝ) * T) * (((n : ℝ) + 1) ^ kk)

end Qatlib.Papers.QuantumLWE25.MainResults
