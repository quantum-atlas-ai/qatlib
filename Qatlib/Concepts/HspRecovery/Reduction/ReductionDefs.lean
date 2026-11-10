/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecovery
import Qatlib.Concepts.HspRecovery.Reduction.PhaseReadoutSynthesisDefs
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
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

noncomputable def labelPosition (M : ℕ) (z : Fin M) : ℝ := (z.val : ℝ) / (M : ℝ)

noncomputable def recordConsistent (M N : ℕ) (x : Fin M) (y : Fin N) : Prop :=
  phaseDistance (labelPosition M x) (labelPosition N y) ≤
    1 / (M : ℝ) + 1 / (N : ℝ)

noncomputable def recordDecode (M N : ℕ) (x : Fin M) (y : Fin N) : Option (Fin N) :=
  if recordConsistent M N x y then some y else none

noncomputable def recordDecodeEvent (M N : ℕ) : Finset (RecordSpace M N I) :=
  Finset.univ.filter fun p => recordConsistent M N p.1 p.2.2.1

noncomputable def recordWindowEvent (M N : ℕ) (φ : ℝ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun r =>
    phaseDistance φ (labelPosition M r.1) ≤ 1 / (M : ℝ) ∧
      phaseDistance φ (labelPosition N r.2) ≤ 1 / (N : ℝ)

def recordEffectiveRadius (ε δ : ℝ) : ℝ := min ε δ

noncomputable def recordEffectiveConfidence : ℝ := (8 / Real.pi^2)^2

def recordEffectiveQueries (M N : ℕ) : ℕ := (M - 1) + (N - 1)

def recordEffectiveGates (M N : ℕ) : ℕ := 2 * (M - 1) + 2 * (N - 1) + 4

noncomputable def zeroWirePhase : Reg 0 → ℝ := fun _ => 1 / 4

def zeroWireLabel : Reg 0 → Bool := fun _ => false

end Qatlib.Concepts.HspRecovery.ReductionCore
