/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

noncomputable def approxCountCor14Grid (N : ℕ) : ℕ :=
  Nat.ceil (Real.sqrt (N : ℝ))
noncomputable def approxCountCor14Output (N : ℕ)
    (z : Fin (approxCountCor14Grid N)) : ℤ :=
  ⌊(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate (approxCountCor14Grid N) z+1/2⌋

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
