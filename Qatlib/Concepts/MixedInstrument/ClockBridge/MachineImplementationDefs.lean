/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffective
import Qatlib.Concepts.CircuitImpl.Phi3Universal.ImplementationMachine
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open Qatlib.Concepts.CircuitImpl.Phi3Universal

def MiDyadicTruncationBound (a : RatAngle) (d : ℕ) : Prop :=
  dyadicApprox a d * a.den ≤ a.num * 2 ^ d

def MiCopyProgramLedger (inW work : ℕ) : Prop :=
  (copyProgram inW work).length = 4 ∧
    (copyProgram inW work)
      = [.alloc work, .fixedGate (.cx inW work), .fixedGate (.cx inW work),
        .releaseClean work]

noncomputable def realDyadicApprox (r : ℝ) (d : ℕ) : ℤ := ⌊r * (2 : ℝ) ^ d⌋

noncomputable def realDyadicValue (r : ℝ) (d : ℕ) : ℝ :=
  (realDyadicApprox r d : ℝ) / (2 : ℝ) ^ d

noncomputable def realDyadicStep (d : ℕ) : ℝ := ((2 : ℝ) ^ d)⁻¹

def MiRealQuantizationLedger (r : ℝ) (d : ℕ) : Prop :=
  realDyadicValue r d ≤ r ∧ r < realDyadicValue r d + realDyadicStep d

end Qatlib.Concepts.MixedInstrument.ClockBridge
