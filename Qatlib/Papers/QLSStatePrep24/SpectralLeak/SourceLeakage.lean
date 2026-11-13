/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLSStatePrep24.SpectralLeak.WeightedSpectralLeakageLows
import Qatlib.Papers.QLSStatePrep24.SpectralLeak.FiveSuccessProbabilitiesLows
import Qatlib.Papers.QLSStatePrep24.SpectralLeak.ThresholdSumStabilityLows

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLeakage — spectral leakage and success probabilities

Low--Su, fixed arXiv:2410.18178v2,
PDF SHA-256 5bc33df5fbcd340bd3381e798bb80a436fdc6596027697440f882c15769de5a6.

Lemma 24 (p.72) is the weighted spectral-leakage estimate with the one-sided
factors `9` and `1/9`; Proposition 25 (p.73, Eq. (385)) compares the five
success probabilities `p_succ`, `p_succ,d-inv,1`, `p_succ,d-inv`,
`p_succ,d-inv,m`, `p_succ,d-inv,bm`; Proposition 26 (p.74) is the `9^l`
threshold-sum stability with its `ε_bm` perturbation bound.

They are bridged to the formal contracts `Clause30WeightedSpectralLeakage`,
`Clause31FiveSuccessProbabilities` and `Clause32ThresholdSumStability`, all proved in
the existing formalisation.

Boundary: the contracts take the band rows, the normalized coefficient rows and
the approximated output vector as hypotheses; they do not construct the
GPE word or the branch-marking word, and carry no algorithm-level query cost.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.QLSStatePrep24.SpectralLeak
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

namespace Qatlib.Papers.QLSStatePrep24.SpectralLeak

/-- Fixed arXiv:2410.18178v2, Lemma 24 (p.72): under `bandRowsLegal`, the stop
coefficient rows satisfy `Σ_j ‖ζ_{j+1} u‖² = 1` for every eigenvalue index,
and the weighted leakage is bounded by `9 p₁ e²` (true flag) and
`p₁ e²/9` (false flag), where `e = Σ_j δ_{j+1}`. The established formalisation
`Clause30WeightedSpectralLeakage` proved by `Clause30WeightedSpectralLeakage_answer`. -/
theorem lemma24_weighted_spectral_leakage : Clause30WeightedSpectralLeakage :=
  Clause30WeightedSpectralLeakage_answer

/-- Fixed arXiv:2410.18178v2, Proposition 25 (p.73, Eq. (385)): the five
success probabilities satisfy
`p₁/9 ≤ p ≤ p₁`, `p₁(1-e²)/9 ≤ p_n ≤ p₁`, `p_n ≤ p_f`,
`p_f ≤ p_n (1 + 9³ e²/(1-e)²)` and `|p_f - p_bm| ≤ 4 ε_bm`.
`Clause31FiveSuccessProbabilities` proved by
`Clause31FiveSuccessProbabilities_answer`. -/
theorem prop25_five_success_probabilities : Clause31FiveSuccessProbabilities :=
  Clause31FiveSuccessProbabilities_answer

/-- Fixed arXiv:2410.18178v2, Proposition 26 (p.74): the threshold sum obeys
`p 9^l ≤ thresholdSum m l γ ζ ≤ (5/4) p 9^l` for `0 < l ≤ m` (and vanishes at
`l = 0`), while perturbing each of `l` vectors by `≤ 2 ε_bm` perturbs the
`9^j`-weighted sum by at most `(9/8) · 4 ε_bm · 9^l`. The established formalisation
`Clause32ThresholdSumStability` proved by `Clause32ThresholdSumStability_answer`. -/
theorem prop26_threshold_sum_stability : Clause32ThresholdSumStability :=
  Clause32ThresholdSumStability_answer

/-- Fixed arXiv:2410.18178v2, Proposition 26 (p.74), first clause: the
multiplicative `9^l` bounds on the threshold sum, extracted from
`Clause32ThresholdSumStability_answer`. -/
theorem prop26_threshold_sum_bounds {I : Type} [Fintype I] (m l : ℕ) (γ : I → ℂ)
    (ζ : ℕ → I → ℂ) (hl : l ≤ m) :
    (l = 0 → thresholdSum m l γ ζ = 0) ∧
    (0 < l → (normVec (weightedBandState m γ ζ))^2*(9 : ℝ)^l ≤ thresholdSum m l γ ζ ∧
      thresholdSum m l γ ζ ≤ (5/4)*(normVec (weightedBandState m γ ζ))^2*(9 : ℝ)^l) :=
  (Clause32ThresholdSumStability_answer).1 I m l γ ζ hl

end Qatlib.Papers.QLSStatePrep24.SpectralLeak
