/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.AmpTransform.NoiseEnvelope.AmplifiedFourierProbabilities
public import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
public import Qatlib.Foundations.QueryWordCore.Circuit

@[expose] public section

/-!
# Counted words for the QFT and QHS baselines

The states `Qatlib.Concepts.AmpTransform.NoiseEnvelope.aqPhaseBaseline` and
`Qatlib.Concepts.AmpTransform.NoiseEnvelope.aqQHSBaseline` are written as matrices applied to the
all-zero preparation, but the comparison of [Cornwell2014], Chapter 2, Sections 2.5-2.6, printed
pp. 19-21, spends them in the query model. This module writes the two words as explicit gate
lists over `Qatlib.Foundations.QueryWordCore.Circuit.Circuit`: the phase word is one Fourier gate,
one phase query and one inverse Fourier gate, and the hidden-subgroup word is the same with every
gate tensored with the identity on the answer bit. Each word therefore costs one query and two
explicit gates, and executing it reproduces the corresponding baseline state. The Fourier and
oracle matrices are those of the published definitions; the register-level compilation of the
phase oracle into elementary gates is not part of this module.

## Main statements

* `run_aqPhaseCircuit`: the phase word executes to `aqPhaseBaseline`.
* `run_aqQHSCircuit`: the hidden-subgroup word executes to `aqQHSBaseline`.
* `aqPhaseCircuit_queryCount`, `aqPhaseCircuit_gateCount`, `aqQHSCircuit_queryCount`,
  `aqQHSCircuit_gateCount`: the two words cost one query and two explicit gates.

## References

* [Cornwell, 2014][Cornwell2014], Chapter 2, Sections 2.5-2.6, printed pp. 19-21,
  [arXiv:1406.0190](https://arxiv.org/abs/1406.0190)
-/

set_option autoImplicit false

namespace Qatlib.Papers.AmpTransform14.OracleCompile

open Qatlib.Concepts.AmpTransform.NoiseEnvelope
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Matrix

/-- The phase-estimation baseline word: a Fourier gate, one phase-oracle query and the inverse
Fourier gate on the label register. -/
noncomputable def aqPhaseCircuit (N : ℕ) : Circuit (Fin N) :=
  [Step.gate (QFTMatrix N), Step.query, Step.gate (QFTMatrix N)ᴴ]

/-- The phase word makes exactly one oracle query. -/
@[simp]
theorem aqPhaseCircuit_queryCount (N : ℕ) : QueryCount (aqPhaseCircuit N) = 1 := rfl

/-- The phase word contains exactly two explicit gates. -/
@[simp]
theorem aqPhaseCircuit_gateCount (N : ℕ) : GateCount (aqPhaseCircuit N) = 2 := rfl

/-- Executing the phase word on the all-zero state with the marking oracle reproduces the phase
baseline state. -/
theorem run_aqPhaseCircuit (N : ℕ) (hN : 0 < N) (A : Finset (Fin N)) :
    Run (preparedMark A) (aqPhaseCircuit N) (Ket ⟨0, hN⟩) = aqPhaseBaseline N hN A := rfl

/-- The hidden-subgroup baseline word: the Fourier and inverse Fourier gates of the phase word,
each tensored with the identity on the Boolean answer bit. -/
noncomputable def aqQHSCircuit (N : ℕ) : Circuit (Fin N × Bool) :=
  [Step.gate (LiftGate (QFTMatrix N)), Step.query, Step.gate (LiftGate (QFTMatrix N)ᴴ)]

/-- The hidden-subgroup word makes exactly one oracle query. -/
@[simp]
theorem aqQHSCircuit_queryCount (N : ℕ) : QueryCount (aqQHSCircuit N) = 1 := rfl

/-- The hidden-subgroup word contains exactly two explicit gates. -/
@[simp]
theorem aqQHSCircuit_gateCount (N : ℕ) : GateCount (aqQHSCircuit N) = 2 := rfl

/-- Executing the hidden-subgroup word on the zero label and the false answer bit with the bit
oracle reproduces the hidden-subgroup baseline state. -/
theorem run_aqQHSCircuit (N : ℕ) (hN : 0 < N) (f : Fin N → Bool) :
    Run (BitOracleOn f) (aqQHSCircuit N) (TensorState (Ket ⟨0, hN⟩) (Ket false)) =
      aqQHSBaseline N hN f := by
  simp only [aqQHSCircuit, aqQHSBaseline, Run, applyGate_liftGate]
  rfl

end Qatlib.Papers.AmpTransform14.OracleCompile
