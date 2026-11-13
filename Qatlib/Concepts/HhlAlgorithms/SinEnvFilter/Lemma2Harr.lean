/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

/-!
# Certificate for HHL filter Lipschitz continuity

`lemma2` proves the proposition `Lemma2`, which states the `1 / d` Lipschitz bound for the
three-state filter vector at every positive gap. This packages the filter-continuity estimate
associated with Lemma 2 of [HarrowHassidimLloyd2009].

## Main statements

* `lemma2`: the packaged Lipschitz proposition holds.

## References

* [Harrow et al., 2009, Lemma 2][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

/-- Establishes the `1 / d` Lipschitz bound packaged in `Lemma2`, corresponding to [Harrow et
al., Lemma 2][HarrowHassidimLloyd2009]. -/
theorem lemma2 : Lemma2 := Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_lipschitz

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
