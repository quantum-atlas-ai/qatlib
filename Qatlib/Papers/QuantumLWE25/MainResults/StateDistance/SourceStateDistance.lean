/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — trace distance of close and Gaussian states (Lemmas 26 and 28)

Fixed arXiv:2310.00644v2.

* Lemma 26, p.12: for un-normalized vectors `|φ⟩`, `|ψ⟩` with `‖φ‖ ≥ μ` and
  `‖φ − ψ‖ ≤ ε`,
  `δ(φ/‖φ‖, ψ/‖ψ‖) = √(1 − (|⟨φ|ψ⟩|/(‖φ‖‖ψ‖))²) ≤ O(ε/μ)`.
* Lemma 28, p.13: for `q > 2√n·max(β₁,β₂)` and `R ≥ 2√n/min(β₁,β₂)`, the trace
  distance between the superpositions `∑_{e∈Z_{qR}/R} ρ_{β_i}(e)|e⟩` is at most
  `√((β₁−β₂)²/(β₁²+β₂²))·(1+2^{-Ω(n)})`.

The trace distance is the library's `FidelityMetric.traceDistance` (‖ρ−σ‖₁/2).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedFidelity.FidelityMetric

/-- **Lemma 26, p.12**, with the explicit constant `2` in place of `O(·)`: for
un-normalized `φ`, `ψ` with `‖φ‖ ≥ μ` and `‖φ − ψ‖ ≤ ε`, the trace distance of the
normalized pure states is at most `2ε/μ`.

Proof route of the paper (p.12): the displayed equality is the pure-state form of the
trace distance, `δ = √(1 − |⟨φ|ψ⟩|²/(‖φ‖²‖ψ‖²))`; then `|⟨φ|ψ⟩| ≥ ‖φ‖² − ‖φ‖ε`
(Cauchy–Schwarz) gives `1 − |⟨φ|ψ⟩|²/(‖φ‖²‖ψ‖²) = O(ε²/μ²)`. In Lean the pure-state
trace distance is bounded by `pure_trace_distance_le_re_inner`
(`δ ≤ √(1 − (Re⟨u,v⟩)²) ≤ ‖u−v‖`), and the Euclidean estimate
`‖φ/‖φ‖ − ψ/‖ψ‖‖ ≤ 2ε/μ` is triangle inequality plus `|‖ψ‖−‖φ‖| ≤ ε`.
The remaining gap is the normalization/`sqrt` algebra (`normalize` has unit norm and
`√(1 − Re²) ≤ ‖u−v‖`), not a mathematical one. -/
def normalized_state_distance_le {D : ℕ} (φ ψ : QState (Fin D)) {μ ε : ℝ}
    (hμ : 0 < μ) (hφ : μ ≤ vecNorm φ) (hφψ : vecNorm (φ - ψ) ≤ ε) (hε : 0 ≤ ε) : Prop := traceDistance (outerProduct (normalize φ)) (outerProduct (normalize ψ)) ≤ 2 * ε / μ

/-- **Lemma 28, p.13.** For `q > 2√n·max(β₁,β₂)` and `R ≥ 2√n/min(β₁,β₂)`, the trace
distance between the two Gaussian superpositions on `Z_{qR}/R` is at most
`√((β₁−β₂)²/(β₁²+β₂²))·(1+2^{-Ω(n)})`.

The paper's proof (p.13) computes the normalized overlap
`⟨φ₁|φ₂⟩/(‖φ₁‖‖φ₂‖) = 2√(β₁β₂)/√(β₁²+β₂²)·(1+2^{-Ω(n)})` using Poisson summation
(Lemma 10) and Banaszczyk's tail bound, then substitutes into the pure-state trace
distance. Gap: Poisson summation over the lattice `Z_{qR}/R` (Lemma 10, itself not yet
proved) and the tail bound are missing; candidate dependencies are
`poisson_summation_formula` above and `ProbabilityCore.Concentration` Gaussian tails. -/
def gaussian_state_trace_distance {n q R : ℕ} {β1 β2 : ℝ}
    (hβ1 : 0 < β1) (hβ2 : 0 < β2)
    (hq : 2 * Real.sqrt (n : ℝ) * max β1 β2 < (q : ℝ))
    (hR : 2 * Real.sqrt (n : ℝ) / min β1 β2 ≤ (R : ℝ)) : Prop := ∃ c : ℝ, 0 < c ∧
      traceDistance (outerProduct (normalize (gaussianState (q * R) β1)))
        (outerProduct (normalize (gaussianState (q * R) β2))) ≤
        Real.sqrt ((β1 - β2) ^ 2 / (β1 ^ 2 + β2 ^ 2)) * (1 + (2 : ℝ) ^ (-(c * (n : ℝ))))

end Qatlib.Papers.QuantumLWE25.MainResults
