/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs

/-!
# Fair-bit masses for Pauli record sampling

Defines `fairBitMass` and `fairBitMassReal` as the mass of an individual length-`k` fair-bit
word in extended nonnegative and real form. `fairBitRejectedMass` names the rejection mass used
by the underlying bounded coin sampler, supplying notation for record-generation analyses. For
the local Pauli measurement framework, see [HuangKuengPreskill2020].

## Main statements

* `fairBitMass`: The extended nonnegative probability mass `((2 ^ k : ℕ) : ℝ≥0∞)⁻¹` of a single
  length-`k` fair-bit word.
* `fairBitRejectedMass`: The rejection mass `coinRejectMass k m` for the `k`-bit coin sampler
  with acceptance range `m`.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution

namespace Qatlib.Concepts.ShadowModels.FairBitRecords

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- The extended nonnegative probability mass `((2 ^ k : ℕ) : ℝ≥0∞)⁻¹` of a single length-`k`
fair-bit word. -/
noncomputable def fairBitMass (k : ℕ) : ℝ≥0∞ := ((2 ^ k : ℕ) : ℝ≥0∞)⁻¹

/-- The real value of the extended nonnegative fair-bit word mass `fairBitMass k`. -/
noncomputable def fairBitMassReal (k : ℕ) : ℝ := ENNReal.toReal (fairBitMass k)

/-- The rejection mass `coinRejectMass k m` for the `k`-bit coin sampler with acceptance range
`m`. -/
noncomputable def fairBitRejectedMass (k m : ℕ) : ℝ≥0∞ := coinRejectMass k m

end Qatlib.Concepts.ShadowModels.FairBitRecords
