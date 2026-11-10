/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.OracleAmplify.StandardOracleCopyProgram
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.UniformBqp.OracleAmplify
open Qatlib

theorem standardOracleSequentialCopies : StandardOracleSequentialCopies := by
  intro n k hn W _ _ _ C hC
  obtain ⟨hu, hq, hg, hr⟩ := standardCopiesCircuit_spec k C hC
  exact ⟨StandardCopiesCircuit k C, hu, hq, hg, fun x ψ => hr x (Ket (⟨0, hn⟩, false)) ψ⟩

end Qatlib.Concepts.UniformBqp.OracleAmplify
