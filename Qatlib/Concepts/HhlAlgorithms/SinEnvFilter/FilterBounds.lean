/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

/-!
# Three-state HHL filter bounds

This module expresses normalization, Lipschitz continuity, and relative stability of the
three-state filter at gap `1 / (2 * κ)`. `source_corrected_filter_stability` uses the
coefficient `2 * π^2` in the relative bound associated with Lemma 3 of
[HarrowHassidimLloyd2009].

## Main statements

* `source_filter_normalized`: the filter vector has squared norm one.
* `source_filter_lipschitz`: the filter vector is `2 * κ`-Lipschitz.
* `source_corrected_filter_stability`: the selected amplitudes satisfy the corrected relative
  error bound.

## References

* [Harrow et al., 2009, Lemmas 2 and 3][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

/-- For positive `κ`, the three-state filter vector at gap `1 / (2 * κ)` has squared norm one. -/
theorem source_filter_normalized (κ lam : ℝ) (hκ : 0 < κ) :
    ∑ s : Fin 3, ‖sinEnvelopeHVector (1/(2*κ)) lam s‖^2 = 1 := by
  have hd : 0 < (1/(2*κ) : ℝ) := by positivity
  exact Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_normalized (1/(2*κ)) lam hd

/-- For positive `κ`, the three-state filter vector at gap `1 / (2 * κ)` is `2 * κ`-Lipschitz in
the phase, as in [Harrow et al., Lemma 2][HarrowHassidimLloyd2009]. -/
theorem source_filter_lipschitz (κ lam lam' : ℝ) (hκ : 0 < κ) :
    Real.sqrt (∑ s : Fin 3,
      ‖(sinEnvelopeHVector (1/(2*κ)) lam - sinEnvelopeHVector (1/(2*κ)) lam') s‖^2) ≤
      2*κ*|lam-lam'| := by
  have hd : 0 < (1/(2*κ) : ℝ) := by positivity
  have h :=
      Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_lipschitz (1/(2*κ)) lam lam' hd
  simpa only [one_div_one_div] using! h

/-- When `lam - lam' = δ / t₀`, the squared changes of the two selected filter amplitudes
satisfy the relative stability bound with coefficient `2 * π^2 * κ^2 * δ^2 / t₀^2`. This is
the corrected form of [Harrow et al., Lemma 3][HarrowHassidimLloyd2009]. -/
theorem source_corrected_filter_stability (κ t₀ δ lam lam' : ℝ)
    (hκ : 0 < κ) (_ht₀ : 0 < t₀) (hδ : lam-lam' = δ/t₀) :
    (sinEnvelopeFilterF (1/(2*κ)) lam-sinEnvelopeFilterF (1/(2*κ)) lam')^2 +
      (sinEnvelopeFilterG (1/(2*κ)) lam-sinEnvelopeFilterG (1/(2*κ)) lam')^2 ≤
      2*Real.pi^2*κ^2*δ^2/t₀^2 *
        (sinEnvelopeFilterF (1/(2*κ)) lam^2+sinEnvelopeFilterG (1/(2*κ)) lam^2) := by
  have hd : 0 < (1/(2*κ) : ℝ) := by positivity
  change (Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterF (1/(2*κ)) lam-
      Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterF (1/(2*κ)) lam')^2 +
    (Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterG (1/(2*κ)) lam-
      Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterG (1/(2*κ)) lam')^2 ≤
    2*Real.pi^2*κ^2*δ^2/t₀^2 *
      (Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterF (1/(2*κ)) lam^2+
        Qatlib.Concepts.HhlErrorBridge.FilterStability.sinEnvelopeFilterG (1/(2*κ)) lam^2)
  have h :=
      Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_filter_stability_global
      (1/(2*κ)) lam lam' hd
  have hk : (1/(2*(1/(2*κ))) : ℝ) = κ := by field_simp
  rw [hk, hδ, div_pow] at h
  convert! h using 1 <;> ring

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
