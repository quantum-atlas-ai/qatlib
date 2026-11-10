/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.AppendixA3PhaseConcentrationStat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

set_option autoImplicit false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

theorem appendixA3PhaseConcentration : AppendixA3PhaseConcentration :=
  ⟨Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_geometric_identity,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_normalized,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_far_label_tail,
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_kernel_second_moment⟩

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
