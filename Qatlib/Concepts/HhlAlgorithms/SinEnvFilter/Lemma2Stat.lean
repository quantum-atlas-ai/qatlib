/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs

/-!
# Specification of HHL filter Lipschitz continuity

`Lemma2` states that the three-state filter vector changes by at most `1 / d` times the phase
difference for positive `d`. The proposition isolates the quantitative continuity estimate
associated with Lemma 2 of [HarrowHassidimLloyd2009].

## Main statements

* `Lemma2`: the universal filter Lipschitz inequality.

## References

* [Harrow et al., 2009, Lemma 2][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

open Matrix
open scoped Real

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Matrix Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeSpecDefs.SinEnvelopeSpec
open scoped Real

/-- The proposition that the three-state filter vector is `1 / d`-Lipschitz for every positive
gap `d`; see [Harrow et al., Lemma 2][HarrowHassidimLloyd2009]. -/
def Lemma2 : Prop :=
  ∀ (d θ₁ θ₂ : ℝ), 0 < d →
    Real.sqrt (∑ s : Fin 3, ‖(sinEnvelopeHVector d θ₁ - sinEnvelopeHVector d θ₂) s‖ ^ 2) ≤
      (1 / d) * |θ₁ - θ₂|

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
