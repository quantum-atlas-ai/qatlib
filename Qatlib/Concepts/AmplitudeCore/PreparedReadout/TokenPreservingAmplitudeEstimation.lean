/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion

/-!
# Amplitude estimation preserving oracle tokens

`instructions` builds amplitude estimation directly from an adjoint preparation word, retaining
queries to the original oracle through spectator lifts and circuit substitution. Its actual
`output` agrees with prepared phase estimation and with `countedAECircuit`.

The module proves forward and inverse resource ledgers, unitarity, normalization, event-law
equality, and the actual BHMT success guarantee from [BrassardEtAl2002].

## Main statements

* `output_eq_countedAE`: identifies the output with the prepared amplitude-estimation circuit.
* `resources`: counts original-oracle queries and fixed gates.
* `bhmt_actual`: proves the amplitude-error event bound on the actual output.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation

open Matrix
open scoped Classical BigOperators Kronecker

variable {H : Type} [Fintype H] [DecidableEq H]

/-- Lift a flag-and-system operator by tensoring it with the identity on the counter. -/
noncomputable def counterLift (M : ℕ) (V : Matrix (Bool × H) (Bool × H) ℂ) :
    Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ :=
  Qatlib.Foundations.PureStateMath.TensorGate (1 : Qatlib.Foundations.PureStateMath.Operator M) V

omit [Fintype H] in

/-- The counter lift sends the identity to the identity. -/
private theorem counterLift_one (M : ℕ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift (H := H) M 1 = 1 := Matrix.one_kronecker_one

omit [DecidableEq H] in

/-- The counter lift preserves matrix multiplication. -/
private theorem counterLift_mul (M : ℕ) (V W : Matrix (Bool × H) (Bool × H) ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M (V * W) = Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M V * Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M W := by
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift, Qatlib.Foundations.PureStateMath.TensorGate, ← Matrix.mul_kronecker_mul, Matrix.one_mul]

omit [Fintype H] [DecidableEq H] in

/-- The counter lift commutes with taking adjoints. -/
private theorem counterLift_adjoint (M : ℕ) (V : Matrix (Bool × H) (Bool × H) ℂ) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M Vᴴ = (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M V)ᴴ := by
  simp only [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift, Qatlib.Foundations.PureStateMath.TensorGate, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]

/-- The counter lift preserves unitarity. -/
private theorem counterLift_unitary (M : ℕ) {V : Matrix (Bool × H) (Bool × H) ℂ}
    (hV : V ∈ Matrix.unitaryGroup _ ℂ) : Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M V ∈ Matrix.unitaryGroup _ ℂ :=
  Qatlib.Foundations.PureStateMath.tensorGate_unitary (Submonoid.one_mem _) hV

/-- The original oracle acting with spectator flag and counter registers. -/
noncomputable def oracle (M : ℕ) (U : Matrix H H ℂ) :
    Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U)

/-- The Grover implementation word lifted to include the counter register. -/
noncomputable def body (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)

/-- The counted phase-estimation circuit compiled into an adjoint query word. -/
noncomputable def outer (M : ℕ) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit (I := H) M)

/-- The phase-estimation word obtained by substituting the lifted Grover body into each outer
query. -/
noncomputable def qpeWord (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer M)

/-- The preparation word lifted with spectator flag and counter registers. -/
noncomputable def initWord (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword)

/-- The complete amplitude-estimation word combining the substituted phase-estimation word and
the initialization word. -/
noncomputable def instructions (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep (Fin M × (Bool × H))) :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord M Aword seed S ++ Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword

/-- The basis input with counter zero, flag `false`, and system at `seed`. -/
noncomputable def input (M : ℕ) (hM : 0 < M) (seed : H) : Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H)) :=
  Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket seed))

/-- The actual state produced by evaluating `instructions` with the lifted original oracle. -/
noncomputable def output (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H) :
    Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H)) :=
  Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S) *ᵥ Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.input M hM seed

/-- The lifted Grover body evaluates to the controlled prepared amplification iterate when the
preparation word is well formed and `U` is unitary. -/
theorem body_evaluate (M : ℕ) (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S) := by
  have h := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift (H := H) M)
    (counterLift_one M) (counterLift_mul M) (counterLift_adjoint M)
    (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.evaluate_instructions U Aword seed S hU hw] at h
  exact h

/-- On every input state, the substituted query word agrees with the counted phase-estimation
circuit using the prepared iterate. -/
theorem qpeWord_coherent (M : ℕ) (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) (ξ : Qatlib.Foundations.PureStateMath.QState (Fin M × (Bool × H))) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord M Aword seed S) *ᵥ ξ =
      Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S))
        (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit M) ξ := by
  have he := (Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer M)).1
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body_evaluate M U Aword seed S hU hw] at he
  change Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U)
    (Qatlib.Concepts.QsvtCore.QueryLowerBound.substituteAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer M)) *ᵥ ξ = _
  rw [he]
  exact Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_evaluate _ _ ξ

/-- The initialization word evaluates to the original preparation operator with spectator flag
and counter registers. -/
theorem initWord_evaluate (M : ℕ) (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword) =
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword)) := by
  have h := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift (H := H) M)
    (counterLift_one M) (counterLift_mul M) (counterLift_adjoint M)
    (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle (J := Bool) U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword)
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_evaluate] at h
  exact h

/-- The initialization word prepares the system state while preserving counter zero and flag
`false`. -/
private theorem initWord_input (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword) *ᵥ Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.input M hM seed =
      Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M))
        (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed)) := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord_evaluate, Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_eq_kronecker]
  change Qatlib.Foundations.PureStateMath.ApplyGate (Qatlib.Foundations.PureStateMath.TensorGate (1 : Qatlib.Foundations.PureStateMath.Operator M)
      (Qatlib.Foundations.PureStateMath.TensorGate (1 : Matrix Bool Bool ℂ) (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword)))
      (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0,hM⟩ : Fin M)) (Qatlib.Foundations.PureStateMath.TensorState (Qatlib.Foundations.PureStateMath.Ket false) (Qatlib.Foundations.PureStateMath.Ket seed))) = _
  rw [Qatlib.Foundations.PureStateMath.applyGate_tensorGate,
      Qatlib.Foundations.PureStateMath.applyGate_one, Qatlib.Foundations.PureStateMath.applyGate_tensorGate, Qatlib.Foundations.PureStateMath.applyGate_one]
  rfl

/-- The actual output equals the flag embedding of phase estimation on the prepared
amplification iterate. -/
theorem output_eq_qpe (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output M hM U Aword seed S =
      Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.phaseFlagEmbed M (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.qpeOutput M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S)
        (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed)) := by
  unfold Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions
  rw [Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_append, ← Matrix.mulVec_mulVec, initWord_input,
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord_coherent M U Aword seed S hU hw]
  exact (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.counted_offgrid_qpe_clean_flag M hM
    (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAIterate (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S) (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedAAState (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed)).1

/-- The actual output equals that of `countedAECircuit` built from the evaluated preparation
word. -/
theorem output_eq_countedAE (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output M hM U Aword seed S =
      Qatlib.Foundations.QueryWordCore.Circuit.Run (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeControlledGate M (Qatlib.Concepts.LchsSimulation.StaticLchs.preparedMark S))
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.countedAECircuit M (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.input M hM seed) :=
  (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output_eq_qpe M hM U Aword seed S hU hw).trans
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.countedAE_output M hM (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S).symm

/-- The compiled outer word is well formed, with `M - 1` queries and `2 * (M - 1) + 2` gates. -/
private theorem outer_resources (M : ℕ) (hM : 0 < M) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer (H := H) M) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer (H := H) M) = M - 1 ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer (H := H) M) = 2 * (M - 1) + 2 := by
  have hc :=
      (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.counted_offgrid_qpe_clean_flag M hM (1 : Matrix H H ℂ) (0 : Qatlib.Foundations.PureStateMath.QState H)).2
  have hr :=
      Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_counts
      (Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout.countedPhaseCircuit (I := H) M)
  exact ⟨Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseCompileCircuit_wellFormed hc.2.2,
      hr.1.trans hc.1, hr.2.trans hc.2.1⟩

/-- The lifted Grover body is well formed, with twice the preparation query count and twice its
gate count plus two. -/
private theorem body_resources (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) = 2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 2 := by
  have hc := Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift (H := H) M)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions Aword seed S)
  exact ⟨Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M) (fun _ h => counterLift_unitary M h)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.instructions_wellFormed Aword seed S hw),
    hc.1.trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.counts Aword seed S).1,
    hc.2.trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.counts Aword seed S).2⟩

/-- The initialization word is well formed and preserves the preparation word's query and gate
counts. -/
private theorem initWord_resources (M : ℕ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.initWord M Aword) = Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword := by
  have hc :=
      Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_counts
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift (H := H) M) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord Aword)
  exact ⟨Qatlib.Concepts.SpectralFilter.PhaseReadout.phaseLiftWord_wellFormed (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.counterLift M) (fun _ h => counterLift_unitary M h)
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_wellFormed hw),
    hc.1.trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_counts Aword).1,
    hc.2.trans (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingGrover.spectatorWord_counts Aword).2⟩

/-- The substituted phase-estimation word is well formed and has the stated query and gate
counts from repeated Grover bodies. -/
theorem qpeWord_resources (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord M Aword seed S) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord M Aword seed S) = (M - 1) * (2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord M Aword seed S) =
        2 * (M - 1) + 2 + (M - 1) * (2 * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 2) := by
  have ho := outer_resources (H := H) M hM
  have hb := body_resources M Aword seed S hw
  have hs := Qatlib.Concepts.QsvtCore.QueryLowerBound.substitute_adjoint_evaluate_cost
    (1 : Matrix (Fin M × (Bool × H)) (Fin M × (Bool × H)) ℂ)
    (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.body M Aword seed S) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.outer M)
  refine ⟨hs.2.2.2 hb.1 ho.1, ?_, ?_⟩
  · simpa only
      [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord,
      ho.2.1, hb.2.1] using! hs.2.1
  · simpa only
      [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord,
      ho.2.1, ho.2.2, hb.2.2] using! hs.2.2.1

/-- The complete word is well formed, uses `(2 * M - 1)` times the preparation queries, and adds
`4 * (M - 1) + 2` gates to the corresponding preparation cost. -/
theorem resources (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S) = (2 * M - 1) * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S) =
        (2 * M - 1) * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 4 * (M - 1) + 2 := by
  have hq :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.qpeWord_resources M hM Aword seed S hw
  have hi := initWord_resources M Aword hw
  have hm : 2 * M - 1 = 2 * (M - 1) + 1 := by omega
  refine ⟨hq.1.append hi.1, ?_, ?_⟩
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append, hq.2.1, hi.2.1, hm]
    ring
  · rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append, hq.2.2, hi.2.2, hm]
    ring

/-- The complete instruction word evaluates to a unitary operator under the preparation and
oracle hypotheses. -/
theorem instructions_unitary (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S) ∈ Matrix.unitaryGroup _ ℂ :=
  (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.resources M hM Aword seed S hw).1.evaluate_unitary
    (counterLift_unitary M (Qatlib.Concepts.CopyEvolution.Discriminate.parallelOracle_unitary hU))

/-- The actual output state is normalized under the preparation and oracle hypotheses. -/
theorem output_normalized (M : ℕ) (hM : 0 < M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Foundations.PureStateMath.Normalized (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output M hM U Aword seed S) :=
  Qatlib.Foundations.PureStateMath.normalized_applyGate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions_unitary M hM U Aword seed S hU hw)
    (Qatlib.Foundations.PureStateMath.normalized_tensorState (Qatlib.Foundations.PureStateMath.normalized_ket _)
      (Qatlib.Foundations.PureStateMath.normalized_tensorState (Qatlib.Foundations.PureStateMath.normalized_ket _) (Qatlib.Foundations.PureStateMath.normalized_ket _)))

/-- The literal adjoint instruction word evaluates to the adjoint of the forward operator. -/
theorem inverse_evaluate (M : ℕ) (U : Matrix H H ℂ) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) :
    Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S)) =
      (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.oracle M U) (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S))ᴴ :=
  Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate_adjointCircuit _ _

/-- The inverse word is well formed and has the same stated query and gate costs as the forward
construction. -/
theorem inverse_resources (M : ℕ) (hM : 0 < M) (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H))
    (seed : H) (S : Finset H) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S)) ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S)) =
        (2 * M - 1) * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount Aword ∧
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointCircuit (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.instructions M Aword seed S)) =
        (2 * M - 1) * Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount Aword + 4 * (M - 1) + 2 := by
  have h :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.resources M hM Aword seed S hw
  exact ⟨h.1.adjointCircuit, (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_adjointCircuit _).trans h.2.1,
    (Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_adjointCircuit _).trans h.2.2⟩

/-- The actual Born probability of a counter-label predicate equals its probability under the
prepared `aeLaw`. -/
theorem event_eq_aeLaw (M : ℕ) (hM : 2 ≤ M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword)
    (P : Fin M → Prop) :
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output M (by omega) U Aword seed S)
      (Finset.univ.filter (fun z : Fin M × (Bool × H) => P z.1)) =
      ∑ z ∈ Finset.univ.filter P,
        (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S (hw.evaluate_unitary hU) hM).prob z := by
  rw [Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output_eq_countedAE M (by omega) U Aword seed S hU hw]
  exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw_event M hM (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S (hw.evaluate_unitary hU) P).symm

/-- The actual output satisfies the BHMT amplitude-error success bound of at least `8 / π²`
[BrassardEtAl2002]. -/
theorem bhmt_actual (M : ℕ) (hM : 2 ≤ M) (U : Matrix H H ℂ)
    (Aword : List (Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointStep H)) (seed : H) (S : Finset H)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (hw : Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit Aword) :
    let p :=
        Qatlib.Foundations.PureStateMath.MeasureProb
        (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S
    Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.output M (by omega) U Aword seed S)
      (Finset.univ.filter (fun z : Fin M × (Bool × H) =>
        |Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z.1 - p| ≤ 2*Real.pi*Real.sqrt (p*(1-p))/(M : ℝ) +
          Real.pi^2/(M : ℝ)^2)) ≥ 8/Real.pi^2 := by
  (try dsimp only)
  have he := Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation.event_eq_aeLaw M hM U Aword seed S hU hw
    (fun z : Fin M =>
      |Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z - Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S| ≤
        2*Real.pi*Real.sqrt (Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S *
          (1-Qatlib.Foundations.PureStateMath.MeasureProb (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword *ᵥ Qatlib.Foundations.PureStateMath.Ket seed) S))/(M : ℝ) +
            Real.pi^2/(M : ℝ)^2)
  rw [he]
  exact (Qatlib.Concepts.AmplitudeCore.PreparedReadout.prepared_ae_bhmt_error_and_endpoints M hM (Qatlib.Concepts.CoherentSim.CoherentOAA.evaluate U Aword) seed S
    (hw.evaluate_unitary hU)).1

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.TokenPreservingAmplitudeEstimation
