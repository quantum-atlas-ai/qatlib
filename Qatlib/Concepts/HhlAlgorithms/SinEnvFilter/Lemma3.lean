/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.FilterBounds
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability

/-!
# Corrected relative stability of HHL filters

`source_lemma3_corrected` bounds the squared change in the two selected filter amplitudes using
coefficient `2 * π^2`. `printed_pi_sq_half_constant_refuted` gives explicit phases and condition
parameter at which the coefficient `π^2 / 2` fails, clarifying the relative stability statement
associated with Lemma 3 of [HarrowHassidimLloyd2009].

## Main statements

* `source_lemma3_corrected`: the corrected relative squared-error estimate.
* `printed_pi_sq_half_constant_refuted`: a counterexample to the smaller coefficient.

## References

* [Harrow et al., 2009, Lemma 3][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

/-- The two selected filter amplitudes satisfy the relative stability inequality with
coefficient `2 * π^2 * κ^2 * δ^2 / t₀^2` when `lam - lam' = δ / t₀`. This is the corrected
form of [Harrow et al., Lemma 3][HarrowHassidimLloyd2009]. -/
theorem source_lemma3_corrected (κ t₀ δ lam lam' : ℝ)
    (hκ : 0 < κ) (ht₀ : 0 < t₀) (hδ : lam - lam' = δ / t₀) :
    (sinEnvelopeFilterF (1 / (2 * κ)) lam - sinEnvelopeFilterF (1 / (2 * κ)) lam') ^ 2 +
        (sinEnvelopeFilterG (1 / (2 * κ)) lam - sinEnvelopeFilterG (1 / (2 * κ)) lam') ^ 2 ≤
      2 * Real.pi ^ 2 * κ ^ 2 * δ ^ 2 / t₀ ^ 2 *
        (sinEnvelopeFilterF (1 / (2 * κ)) lam ^ 2 +
          sinEnvelopeFilterG (1 / (2 * κ)) lam ^ 2) := by
  have h := source_corrected_filter_stability κ t₀ δ lam lam' hκ ht₀ hδ
  simpa only [one_div_one_div] using h

/-- The relative filter-stability inequality with coefficient `π^2 / 2` fails at `κ = 4`, phases
`1 / 8` and `1 / 4`, and `t₀ = 1`. -/
theorem printed_pi_sq_half_constant_refuted :
    ¬ ((sinEnvelopeFilterF (1 / (2 * 4)) (1 / 8) -
          sinEnvelopeFilterF (1 / (2 * 4)) (1 / 4)) ^ 2 +
        (sinEnvelopeFilterG (1 / (2 * 4)) (1 / 8) -
          sinEnvelopeFilterG (1 / (2 * 4)) (1 / 4)) ^ 2 ≤
      Real.pi ^ 2 / 2 * 4 ^ 2 * (1 / 8 : ℝ) ^ 2 / 1 ^ 2 *
        (sinEnvelopeFilterF (1 / (2 * 4)) (1 / 8) ^ 2 +
          sinEnvelopeFilterG (1 / (2 * 4)) (1 / 8) ^ 2)) := by
  simp only [sinEnvelopeFilterF, sinEnvelopeFilterG]
  norm_num
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3
