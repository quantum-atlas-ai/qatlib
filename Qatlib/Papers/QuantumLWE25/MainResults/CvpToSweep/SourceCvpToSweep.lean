/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.LweToPhase.SourceLweToPhase
import Qatlib.Papers.QuantumLWE25.MainResults.SmoothingTail.SourceSmoothingTail

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — the CVP machinery (Theorems 60, 61, 63)

Fixed arXiv:2310.00644v2.

* c021 Theorem 60, p.32 (the iterative step): with an `S|LWE⟩^phase` solver of time `T`, the
  states `|D_{L,r}⟩` can be refreshed to width `√n·r/(αq)` at cost `O((m⁴+m³T)poly(n))`.
* c022 Theorem 61, p.32: with the same solver one answers a quantum CVP query on the
  support `L*/R` up to exponentially small error.
* c023 Theorem 63, p.34: a CVP instance plus `|D_{L,r}⟩` yields a uniform `a ← U(Z_q^n)` and
  a state `2^{-Ω(n)}`-close to the `S|LWE⟩^phase` state `γ_t^a` of Eq. (13).

Modelling: the `S|LWE⟩^phase` solver is the black box `SolvesSLwePhase` of
`LweToPhase.SourceLweToPhase`; CVP answers are read through the closest-vector map
`IsClosestPoint`, and the discrete Gaussian states through `gaussianLatticeState`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Theorem 60 (The iterative step), p.32.** Let `L` be an `n`-dimensional integer
lattice and `q > 2`. With an `S|LWE⟩^phase` solver of time `T`, there is a quantum
algorithm that, given `3m²n²` states `|D_{L,r}⟩`, produces `3m²n²` states
`2^{-Ω(n)}`-close to `|D_{L,√n r/(αq)}⟩`, in time `O((m⁴+m³T)poly(n))`.

Gap: the two-step proof (Theorem 61 for the CVP query, then Theorem 62/Regev's quantum step
generating the narrower Gaussian) is entirely unformalized; the state-fidelity analysis that
composes the two is also missing. Candidate dependencies: `cvp_query_answer` (Theorem 61),
`smoothing_tail_bound` (Lemma 72). -/
def iterative_step {n m q R : ℕ} [NeZero q] [NeZero R] (B : Matrix (Fin n) (Fin n) ℤ)
    {α r : ℝ} (hα : 0 < α) (hr : 0 < r) (T : ℝ) (hSolve : SolvesSLwePhase n m q T) : Prop := ∃ Bg : QuantumAlgo (fun _ : ℕ => Fin (3 * m * m * n * n) → QState (Fin n → ZMod R))
        (fun _ : ℕ => Fin (3 * m * m * n * n) → QState (Fin n → ZMod R)),
      (∀ (inp : Fin (3 * m * m * n * n) → QState (Fin n → ZMod R)),
        1 - (2 : ℝ) ^ (-(1 : ℝ) * (n : ℝ)) ≤
          Bg.successProb 0 inp (fun out =>
            ∀ k : Fin (3 * m * m * n * n), ∃ err : ℕ → ℝ, ExpSmall err ∧
              traceDistance (outerProduct (out k))
                (outerProduct (gaussianLatticeStateMod (R := R) B
                  (Real.sqrt (n : ℝ) * r / (α * (q : ℝ))))) ≤ err n)) ∧
      ∃ C kk : ℝ, 0 < C ∧
        Bg.timeCost 0 ≤ C * ((m : ℝ) ^ 4 + (m : ℝ) ^ 3 * T) * (((n : ℝ) + 1) ^ kk)

/-- **Theorem 61, p.32.** Let `L` be an `n`-dimensional integer lattice, `α ∈ (0, 1/(5√n))`,
`r > 4qη_ε(L)`, `R > max{2√(nr log r), √(2n+1)·√(nr)·λ₁(L*)/(αq), 2^{2n}/αq, 2^{3n}λ_n(L*)}`.
With an `S|LWE⟩^phase` solver of time `T` there is a quantum algorithm that, given `3m²n²`
states `|D_{L,r}⟩`, answers the quantum CVP query `|x,y⟩ ↦ |x, y+κ_{L*}(x)⟩` on the support
`L*/R` (for `dist(x,L*) ≤ αq/r`) up to exponentially small error, in time
`O((m²+mT)poly(n))`.

The output is compared with the closest-vector certificate `κx` through `IsClosestPoint`;
the two precision parameters `λ₁(L*)/(αq)` and `2^{3n}λ_n(L*)` are represented by the
`IsClosestPoint` hypothesis rather than by bounds on `λ`. Gap: the reduction to the
`S|LWE⟩^phase` solver (the "Step 1" of p.32, using Theorem 63 on the `3m²n²` states) is not
formalized. Candidate dependencies: `cvp_to_slwe_state` (Theorem 63). -/
def cvp_query_answer {n m q : ℕ} [NeZero q]
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

/-- **Theorem 63, p.34.** Let `L` be an `n`-dimensional integer lattice, `ε ∈ (0,2^{-n})`,
`α ∈ (0,1/(5√n))`, `σ ∈ [αq, 2αq]`, `r > 4qη_ε(L)`, `R > 2√(nr log r)`. Given a CVP
instance `x ∈ L*/R` and a state `|D_{L,r}⟩`, there is an efficient quantum algorithm that
produces `a ← U(Z_q^n)` and a state `2^{-Ω(n)}`-close to the state of Eq. (13), whose
`S|LWE⟩^phase` factor is
`|ψ_t^{a,y}⟩ = ∑_{u∈Z_{qR}/R} ρ_t(u)·exp(2πi r²⟨x',z⟩u/t²)|⟨s,a⟩+u mod q⟩`.

The target state's `S|LWE⟩^phase` factor is `slwePhaseState σ c a s` with the phase
`c = r²⟨x',z⟩/t²` passed as an explicit parameter `c` (the mixture over `y` and the first
register `y/R` of Eq. (13) are not modelled: a single `S|LWE⟩^phase` factor is stated, which
is what Theorem 68 consumes). Gap: Lemmas 64/66 plus the phase-function analysis of
pp.34–35. Candidate dependencies: `lemma64_state_close`, `lemma66_state_close`. -/
def cvp_to_slwe_state {n m q : ℕ} [NeZero q]
    (B : Matrix (Fin n) (Fin n) ℤ) (Bd : Matrix (Fin n) (Fin n) ℚ)
    {α σ r : ℝ} (hα : 0 < α) (hr : 0 < r)
    (hσ1 : α * (q : ℝ) ≤ σ) (hσ2 : σ ≤ 2 * α * (q : ℝ)) (c : ℝ) : Prop := ∃ Bg : QuantumAlgo (fun _ : ℕ => (Fin n → ℝ) × QState (Fin n → ℤ))
        (fun _ : ℕ => (Fin n → ZMod q) × QState (ZMod q)),
      (∀ (x : Fin n → ℝ) (dg : QState (Fin n → ℤ)) (s : Fin n → ZMod q),
        (2 : ℝ) / 3 ≤ Bg.successProb 0 (x, dg) (fun out =>
          ∃ err : ℕ → ℝ, ExpSmall err ∧
            traceDistance (outerProduct out.2)
              (outerProduct (slwePhaseStateVec σ c out.1 s)) ≤ err n)) ∧
      PolyBounded Bg.timeCost

end Qatlib.Papers.QuantumLWE25.MainResults
