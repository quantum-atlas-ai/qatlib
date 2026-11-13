/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

/-!
# Certificate for corrected HHL filter stability

`lemma3` proves the proposition `Lemma3`, which bounds relative squared error of the two
selected filter amplitudes with the corrected coefficient. The proposition corresponds to the
stability estimate associated with Lemma 3 of [HarrowHassidimLloyd2009].

## Main statements

* `lemma3`: the corrected filter-stability proposition holds.

## References

* [Harrow et al., 2009, Lemma 3][HarrowHassidimLloyd2009]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

/-- Establishes the corrected relative filter-stability proposition `Lemma3`; see [Harrow et
al., Lemma 3][HarrowHassidimLloyd2009]. -/
theorem lemma3 : Lemma3 :=
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_filter_stability

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
