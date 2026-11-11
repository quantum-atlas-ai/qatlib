/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecovery
import Qatlib.Concepts.HspRecovery.Reduction.PhaseReadoutSynthesisDefs
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit

/-!
# Consistency tests for paired phase records

This module defines normalized record positions and circular-distance consistency tests for
paired Fourier readouts. `recordDecode` accepts a candidate exactly when the two labels are
consistent, while `recordWindowEvent` describes pairs lying in prescribed windows about a phase,
in the phase-estimation setting of [NielsenChuang2010].

## Main definitions

* `recordConsistent`: circular separation at most the sum of the two grid spacings.
* `recordDecodeEvent`: full records passing the consistency test.
* `recordEffectiveConfidence`: the constant `(8 / Real.pi^2)^2`.
* `recordEffectiveQueries` and `recordEffectiveGates`: resource expressions for the two
  readouts.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.ReductionCore

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib
open Matrix
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The normalized real position `z.val / M` of a finite readout label. -/
noncomputable def labelPosition (M : ℕ) (z : Fin M) : ℝ := (z.val : ℝ) / (M : ℝ)

/-- The condition that the circular distance between two normalized labels is at most `1 / M + 1
/ N`. -/
noncomputable def recordConsistent (M N : ℕ) (x : Fin M) (y : Fin N) : Prop :=
  phaseDistance (labelPosition M x) (labelPosition N y) ≤
    1 / (M : ℝ) + 1 / (N : ℝ)

/-- The decoder that returns `some y` when the two readout labels are consistent and `none`
otherwise. -/
noncomputable def recordDecode (M N : ℕ) (x : Fin M) (y : Fin N) : Option (Fin N) :=
  if recordConsistent M N x y then some y else none

/-- The finite set of full records whose two readout labels satisfy `recordConsistent`. -/
noncomputable def recordDecodeEvent (M N : ℕ) : Finset (RecordSpace M N I) :=
  Finset.univ.filter fun p => recordConsistent M N p.1 p.2.2.1

/-- The finite set of label pairs whose normalized positions lie within circular distances `1 /
M` and `1 / N` of `φ`, respectively. -/
noncomputable def recordWindowEvent (M N : ℕ) (φ : ℝ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun r =>
    phaseDistance φ (labelPosition M r.1) ≤ 1 / (M : ℝ) ∧
      phaseDistance φ (labelPosition N r.2) ≤ 1 / (N : ℝ)

/-- The smaller of the two error parameters `ε` and `δ`. -/
def recordEffectiveRadius (ε δ : ℝ) : ℝ := min ε δ

/-- The confidence constant `(8 / Real.pi^2)^2` for paired records. -/
noncomputable def recordEffectiveConfidence : ℝ := (8 / Real.pi^2)^2

/-- The query-count expression `(M - 1) + (N - 1)` for paired readouts. -/
def recordEffectiveQueries (M N : ℕ) : ℕ := (M - 1) + (N - 1)

/-- The gate-count expression `2 * (M - 1) + 2 * (N - 1) + 4` for paired readouts. -/
def recordEffectiveGates (M N : ℕ) : ℕ := 2 * (M - 1) + 2 * (N - 1) + 4

/-- The constant phase table with value `1 / 4` on the register with zero wires. -/
noncomputable def zeroWirePhase : Reg 0 → ℝ := fun _ => 1 / 4

/-- The constant false label on the register with zero wires. -/
def zeroWireLabel : Reg 0 → Bool := fun _ => false

end Qatlib.Concepts.HspRecovery.ReductionCore
