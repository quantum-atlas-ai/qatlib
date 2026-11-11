/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.AppendixA3PhaseConcentrationStat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

/-!
# Sine-envelope phase-concentration certificate

`appendixA3PhaseConcentration` assembles the sine-envelope kernel identity, normalization,
far-label tail estimate, and second-moment estimate into `AppendixA3PhaseConcentration`. These
are the phase-estimation concentration properties associated with Appendix A.3 of
[HarrowHassidimLloyd2009].

## Main statements

* `appendixA3PhaseConcentration`: the packaged phase-concentration proposition holds.

## References

* [Harrow et al., 2009, Appendix A.3][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

/-- Establishes the geometric kernel identity, normalization, fourth-power tail bound, and
second-moment bound packaged in `AppendixA3PhaseConcentration`; see [Harrow et al., Appendix
A.3][HarrowHassidimLloyd2009]. -/
theorem appendixA3PhaseConcentration : AppendixA3PhaseConcentration :=
  ⟨Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_geometric_identity,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_normalized,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_far_label_tail,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_second_moment⟩

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
