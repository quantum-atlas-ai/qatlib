/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.FilterBounds
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
import Qatlib.Concepts.HhlErrorBridge.FilterStability
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

theorem source_lemma3_corrected (κ t₀ δ lam lam' : ℝ)
    (hκ : 0 < κ) (ht₀ : 0 < t₀) (hδ : lam - lam' = δ / t₀) :
    (sinEnvelopeFilterF (1 / (2 * κ)) lam - sinEnvelopeFilterF (1 / (2 * κ)) lam') ^ 2 +
        (sinEnvelopeFilterG (1 / (2 * κ)) lam - sinEnvelopeFilterG (1 / (2 * κ)) lam') ^ 2 ≤
      2 * Real.pi ^ 2 * κ ^ 2 * δ ^ 2 / t₀ ^ 2 *
        (sinEnvelopeFilterF (1 / (2 * κ)) lam ^ 2 +
          sinEnvelopeFilterG (1 / (2 * κ)) lam ^ 2) := by
  have h := source_corrected_filter_stability κ t₀ δ lam lam' hκ ht₀ hδ
  simpa only [one_div_one_div] using h

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
