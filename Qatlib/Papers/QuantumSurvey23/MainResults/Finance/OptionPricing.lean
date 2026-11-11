/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c003 — Option pricing: `Õ(σ/ε)` versus `Õ(σ²/ε²)`

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 8.2 (arXiv source lines 7537–7540).

Source conclusion: classical Monte Carlo pricing of an option needs
`M = Õ(σ²/ε²)` samples (variance `σ²`, additive error `ε`); quantum Monte
Carlo / amplitude estimation needs only `Õ(√M) = Õ(σ/ε)` samples or queries —
a quadratic speedup in the sample count.

Formalization notes: the real-valued cost functions
* `classicalSamples σ ε = σ²/ε²`,
* `quantumSamples σ ε = σ/ε`.

The exact identity `quantumSamples² = classicalSamples` is the entire arithmetic
content of the "quartic speedup in `σ/ε`" phrasing: the quantum query count is
the square root of the classical sample count, which is what amplitude
estimation provides.

Reusable dependency (Dev bind `MonteCarloMean.PayoffEncoding`,
`AmplitudeCore.AmplifyCore`): the payoff/mean encoding is
`QuantumAlgorithm.Concepts.MonteCarloMean.PayoffEncoding`, and the
amplitude-estimation backend is
`QuantumAlgorithm.Concepts.AmplitudeCore.AmplifyCore` (paper `MCMontanaro15`
proves the `1/ε` query bound as `monteCarlo_standard_deviation_queries`).  This
module records only the sample-count arithmetic.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Finance

/-- Classical Monte Carlo sample count for variance `σ²` and additive error `ε`:
`σ²/ε²`. -/
noncomputable def classicalSamples (σ ε : ℝ) : ℝ := σ ^ 2 / ε ^ 2

/-- Quantum (amplitude-estimation) sample/query count: `σ/ε = √(σ²/ε²)`. -/
noncomputable def quantumSamples (σ ε : ℝ) : ℝ := σ / ε

/-- **c003a (Section 8.2).** The quantum sample count is exactly the
square root of the classical count: `(σ/ε)² = σ²/ε²`. -/
theorem quantum_samples_square (σ ε : ℝ) (hε : ε ≠ 0) :
    quantumSamples σ ε ^ 2 = classicalSamples σ ε := by
  unfold quantumSamples classicalSamples
  field_simp

/-- **c003b (Section 8.2).** Whenever the quantum count is at least one
sample, it is no larger than the classical count — the quadratic speedup
`Õ(√M) ≤ Õ(M)`. -/
theorem quantum_samples_le_classical (σ ε : ℝ) (_hσ : 0 < σ) (hε : 0 < ε)
    (hge : 1 ≤ quantumSamples σ ε) :
    quantumSamples σ ε ≤ classicalSamples σ ε := by
  have hsq : quantumSamples σ ε ^ 2 = classicalSamples σ ε :=
    quantum_samples_square σ ε (ne_of_gt hε)
  have hq0 : 0 ≤ quantumSamples σ ε := le_trans zero_le_one hge
  have hmul : quantumSamples σ ε * 1 ≤ quantumSamples σ ε * quantumSamples σ ε :=
    mul_le_mul_of_nonneg_left hge hq0
  rw [mul_one] at hmul
  calc quantumSamples σ ε ≤ quantumSamples σ ε ^ 2 := by
        simpa [pow_two] using hmul
    _ = classicalSamples σ ε := hsq

/-- **c003 (Section 8.2), combined assessment.** The sample count drops
from `M = σ²/ε²` to `√M = σ/ε`: the quantum count squares to the classical
count and never exceeds it (in the regime of at least one sample). -/
theorem option_pricing_quadratic_speedup (σ ε : ℝ) (_hσ : 0 < σ) (hε : 0 < ε)
    (hge : 1 ≤ quantumSamples σ ε) :
    quantumSamples σ ε ^ 2 = classicalSamples σ ε ∧
    quantumSamples σ ε ≤ classicalSamples σ ε := by
  exact ⟨quantum_samples_square σ ε (ne_of_gt hε),
    quantum_samples_le_classical σ ε _hσ hε hge⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Finance
