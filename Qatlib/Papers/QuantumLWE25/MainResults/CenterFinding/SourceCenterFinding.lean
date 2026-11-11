/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumLWE25.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# QuantumLWE25 — center finding (Theorem 36)

Fixed arXiv:2310.00644v2, Theorem 36, p.17 (§4.1).

Source: for positive integers `n, t` and `r ≥ 30tn log n`, a polynomial-time quantum
algorithm, given the complex Gaussian state
`|φ_c⟩ = ∑_{x∈Z} ρ_r(x) e^{-πi x²/t}|x+c⟩` with unknown `c ∈ Z`, finds `c mod t` with
probability `1 - 1/n`.

The proof (pp.17–19): for `c₁ ≢ c₂ (mod t)` the states `|φ_{c₁}⟩`, `|φ_{c₂}⟩` have
overlap `2^{-Ω(n)}` (computed by Poisson summation and the concentration of
`∑_y ρ_{√2/r}(y-c/t)`), so the POVM `{|ψ_d⟩⟨ψ_d|}_{d∈Z_t}` (Lemma 37) identifies
`c mod t` with error `2^{-Ω(n)}`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuantumLWE25.MainResults

open scoped BigOperators Matrix

/-- **Theorem 36 (Center finding), p.17.** For `r ≥ 30tn log n` there is a quantum
algorithm that maps an unknown center `c ∈ Z` to `c mod t` with success probability at
least `1 - 1/n`, in polynomial time.

Gap: the state `|φ_c⟩` itself and the overlap computation of pp.17–18 (Poisson summation
plus the Poisson-tail concentration) are not formalized, and the measurement in the
`{|ψ_d⟩}` basis (Lemma 37) is not connected to the success probability. Candidate
dependencies: `pure_imaginary_gaussian_basis_circuit` (Lemma 37),
`poisson_summation_formula` (Lemma 10) and `ProbabilityCore.Concentration`. -/
def center_finding (n t : ℕ) (hn : 1 ≤ n) (ht : 1 ≤ t) {r : ℝ}
    (hr : 30 * (t : ℝ) * (n : ℝ) * Real.log (n : ℝ) ≤ r) : Prop := ∃ A : QuantumAlgo (fun _ : ℕ => ℤ) (fun _ : ℕ => ZMod t),
      (∀ c : ℤ, 1 - 1 / (n : ℝ) ≤ A.successProb 0 c (fun d => d = (c : ZMod t))) ∧
      PolyBounded A.timeCost

end Qatlib.Papers.QuantumLWE25.MainResults
