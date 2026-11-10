/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma3Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

theorem lemma3 : Lemma3 :=
    Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL.sin_envelope_filter_stability

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
