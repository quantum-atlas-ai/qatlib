/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2Stat

/-!
# Specification of corrected HHL filter stability

`Lemma3` states the relative squared-error inequality for the well-conditioned and
ill-conditioned filter amplitudes on the specified phase ranges. Its coefficient `2 * π^2 * (1 /
(2 * d))^2` records the corrected form of the estimate associated with Lemma 3 of
[HarrowHassidimLloyd2009].

## Main statements

* `Lemma3`: the corrected relative stability proposition.

## References

* [Harrow et al., 2009, Lemma 3][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

/-- The relative squared-error bound for the two selected filter amplitudes, with coefficient `2
* π^2 * (1 / (2 * d))^2` on the specified phase ranges. This uses the corrected constant for
[Harrow et al., Lemma 3][HarrowHassidimLloyd2009]. -/
def Lemma3 : Prop :=
  ∀ (d θ θ' : ℝ), 0 < d → 0 ≤ θ → θ ≤ 1 / 4 → -1 / 2 ≤ θ' → θ' ≤ 1 / 2 →
    (sinEnvelopeFilterF d θ - sinEnvelopeFilterF d θ') ^ 2 +
        (sinEnvelopeFilterG d θ - sinEnvelopeFilterG d θ') ^ 2 ≤
      2 * Real.pi ^ 2 * (1 / (2 * d)) ^ 2 * (θ - θ') ^ 2 *
        (sinEnvelopeFilterF d θ ^ 2 + sinEnvelopeFilterG d θ ^ 2)

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
