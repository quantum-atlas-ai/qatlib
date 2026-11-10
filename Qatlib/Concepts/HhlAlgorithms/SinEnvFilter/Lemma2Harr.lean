/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.Lemma2Stat
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.HHL2009

open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvFilter

theorem lemma2 : Lemma2 := Qatlib.Concepts.HhlErrorBridge.FilterStability.sin_envelope_h_lipschitz

end Qatlib.Concepts.HhlAlgorithms.SinEnvFilter
