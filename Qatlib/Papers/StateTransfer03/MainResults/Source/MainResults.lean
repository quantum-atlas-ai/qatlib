/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StateTransfer03.MainResults.Source.HypercubeConstantTime
import Qatlib.Papers.StateTransfer03.MainResults.Source.HypercubeDistance
import Qatlib.Papers.StateTransfer03.MainResults.Source.EngineeredChain
import Qatlib.Papers.StateTransfer03.MainResults.Source.ColumnGraph
import Qatlib.Papers.StateTransfer03.MainResults.Source.HittingTimeSeparation

/-!
# Collected state transfer results

`main_results` collects spectral perfect transfer for one- and two-link Cartesian powers and for
their two base paths. It also records the two-link distance formula, positivity of interior
engineered couplings, and unbounded domination of the one-link quantum time by the stated
classical scale. See [ChristandlEtAl2004].

## Main statements

* `main_results`: the conjunction of transfer, distance, coupling-positivity, and one-link
  scale-comparison results.

## References

* [Christandl et al., 2004][ChristandlEtAl2004]
-/

set_option warningAsError false

namespace Qatlib.Papers.StateTransfer03.MainResults.Source

open Qatlib.Papers.StateTransfer03.MainResults.Defs

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- Collects perfect transfer for both hypercube spectral families and their base paths, the
two-link logarithmic distance formula, positive interior engineered couplings, and unbounded
one-link classical-to-quantum scale comparison. See [ChristandlEtAl2004]. -/
theorem main_results :
    (∀ d : ℕ, SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 2) d)
        (powerWeight (fun k => (pathWeight 2 k : ℂ)) d)) ∧
    (∀ d : ℕ, SpectralPerfectTransfer (powerEigenvalue (pathEigenvalue 3) d)
        (powerWeight (fun k => (pathWeight 3 k : ℂ)) d)) ∧
    (SpectralPerfectTransfer (pathEigenvalue 2) (fun k => (pathWeight 2 k : ℂ)) ∧
      SpectralPerfectTransfer (pathEigenvalue 3) (fun k => (pathWeight 3 k : ℂ))) ∧
    (∀ d : ℕ, twolinkDistance (twolinkFirst d) (twolinkLast d) =
      2 * Nat.log 3 (twolinkSiteCount d)) ∧
    (∀ (N : ℕ) (lam : ℝ), 0 < lam → ∀ n : ℕ, 1 ≤ n → n < N →
        0 < engineeredCoupling N lam n) ∧
    (∀ C : ℝ, ∃ d : ℕ,
      C * quantumHittingTimeOnelink < (classicalHittingTimeOnelink d : ℝ)) := by
  refine ⟨onelink_hypercube_perfect, twolink_hypercube_perfect,
    chain_perfect_transfer_two_three, twolink_max_distance, ?_,
    hitting_time_ratio_unbounded_onelink⟩
  · intro N lam hlam n hn hnN
    exact engineeredCoupling_pos N lam hlam n hn hnN

end

end Qatlib.Papers.StateTransfer03.MainResults.Source
