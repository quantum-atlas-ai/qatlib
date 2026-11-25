/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegression21.MainResults.Model.SourceModel
public import Qatlib.Concepts.MonteCarloMean.FinDistBounds.HellingerTransport

@[expose] public section

/-!
# Lemma B.3: Hellinger versus total variation

Appendix B of the fixed source starts from the two-sided comparison between the squared Hellinger
distance and the total variation distance of two distributions on `ℤ_N`. In the normalisation of
`SourceModel`, `hellingerSqDist p q = ∑ x, (√(p x) - √(q x))²` is twice the squared Hellinger
distance `d_H²`, so the source's `d_H² ≤ d_TV ≤ √2 d_H` reads
`½ hellingerSqDist ≤ tvDist ≤ √(hellingerSqDist)`.

The reusable form of this estimate for the shared `FinDist` layer is
`Qatlib.Concepts.MonteCarloMean.FinDistBounds.hellingerSq_tvDist_two_sided`; this module
restates it for the paper's own definitions and records the source's Lemma B.3.

Boundary: only the finite two-sided comparison is proved. The Corollary B.7 chain and the
hypergeometric estimates of Theorems B.4--B.6 are not covered here.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QRegression21.MainResults.HellingerTV

open Qatlib.Concepts.MonteCarloMean.FinDistBounds (FinDist)
open Qatlib.Papers.QRegression21.MainResults

/-- The paper's squared Hellinger expression is the shared `hellingerSq`. -/
theorem hellingerSqDist_eq_hellingerSq {N : ℕ} (p q : FinDist (Fin N)) :
    hellingerSqDist p q
      = Qatlib.Concepts.MonteCarloMean.FinDistBounds.FiniteInformationDivergence.hellingerSq p q :=
  rfl

/-- The paper's total variation distance is the shared `tvDist`. -/
theorem tvDist_eq_shared {N : ℕ} (p q : FinDist (Fin N)) :
    tvDist p q = Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist p q := by
  unfold tvDist Qatlib.Concepts.MonteCarloMean.FinDistBounds.tvDist
  ring

/-- Lemma B.3 of the fixed source: `½ hellingerSqDist ≤ tvDist ≤ √ hellingerSqDist` for
distributions on a finite set. -/
theorem lemma_B_3 {N : ℕ} (p q : FinDist (Fin N)) :
    (1 / 2) * hellingerSqDist p q ≤ tvDist p q ∧
      tvDist p q ≤ Real.sqrt (hellingerSqDist p q) := by
  have htwo :=
    Qatlib.Concepts.MonteCarloMean.FinDistBounds.hellingerSq_tvDist_two_sided p q
  rw [hellingerSqDist_eq_hellingerSq, tvDist_eq_shared]
  exact htwo

end Qatlib.Papers.QRegression21.MainResults.HellingerTV
