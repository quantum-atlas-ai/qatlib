/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.ImplementationEffective
import Qatlib.Concepts.CircuitImpl.Phi3Universal.ImplementationMachine

/-!
# Definitions for machine implementation ledgers

This module defines the rational truncation and copy-program ledgers and introduces floor-based
dyadic quantization of real numbers. The predicates specify exact instruction accounting and the
half-open interval containing the quantized input. Circuit approximation provides the
surrounding context in [NielsenChuang2010].

## Main statements

* `realDyadicValue`: defines the real dyadic approximation.
* `MiRealQuantizationLedger`: specifies its quantization interval.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option warningAsError false

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Qatlib
open Qatlib.Concepts.CircuitImpl.GateSynthesis
open Qatlib.Concepts.CircuitImpl.Phi3Universal

/-- The predicate that the rational dyadic approximation satisfies `dyadicApprox a d * a.den ≤
a.num * 2 ^ d`. -/
def MiDyadicTruncationBound (a : RatAngle) (d : ℕ) : Prop :=
  dyadicApprox a d * a.den ≤ a.num * 2 ^ d

/-- The predicate that the copy program has length four and consists of allocation, two
controlled-X gates, and clean release. -/
def MiCopyProgramLedger (inW work : ℕ) : Prop :=
  (copyProgram inW work).length = 4 ∧
    (copyProgram inW work)
      = [.alloc work, .fixedGate (.cx inW work), .fixedGate (.cx inW work),
        .releaseClean work]

/-- The integer obtained by taking the floor of `r * 2 ^ d`. -/
noncomputable def realDyadicApprox (r : ℝ) (d : ℕ) : ℤ := ⌊r * (2 : ℝ) ^ d⌋

/-- The real dyadic approximation obtained by dividing `realDyadicApprox r d` by `2 ^ d`. -/
noncomputable def realDyadicValue (r : ℝ) (d : ℕ) : ℝ :=
  (realDyadicApprox r d : ℝ) / (2 : ℝ) ^ d

/-- The dyadic mesh size `2⁻ᵈ`. -/
noncomputable def realDyadicStep (d : ℕ) : ℝ := ((2 : ℝ) ^ d)⁻¹

/-- The predicate that `r` belongs to the half-open interval from its dyadic approximation to
that approximation plus one dyadic step. -/
def MiRealQuantizationLedger (r : ℝ) (d : ℕ) : Prop :=
  realDyadicValue r d ≤ r ∧ r < realDyadicValue r d + realDyadicStep d

end Qatlib.Concepts.MixedInstrument.ClockBridge
