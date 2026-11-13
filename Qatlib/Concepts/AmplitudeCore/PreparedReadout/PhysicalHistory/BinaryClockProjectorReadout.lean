/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockCoordinateFrame
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ClockDefinitions

/-!
# Projector readout of a binary clock history

This module applies a projector encoding to a purified binary clock simulation.
`projectorTransport` inserts the projector ancilla, applies its unitary, and rearranges
registers into `Result` coordinates.

`actual` is the simulated output and `framedReference` uses exact midpoint evolution. Their
distance controls the error between a projector measurement probability and the physical time
integral, using the Born-rule framework of [NielsenChuang2010].

## Main statements

* `framedReference_eq`: the reference agrees with the ideal projector history on the augmented
  purification.
* `actual_integral_error`: the integral error is bounded by quadrature error plus simulation
  error.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorReadout

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Interval Kronecker Matrix.Norms.L2Operator

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- The raw single controlled-oracle simulator register together with the purification
environment. -/
abbrev Raw (q a : ℕ) (I E : Type) := BinaryClockSingleCU.New q (Reg a × I) × E
/-- The readout register containing the finite clock label, environment with simulator work, and
projector ancilla with system. -/
abbrev Result (q a m : ℕ) (I E : Type) :=
  Fin (2^q) × ((E × BinaryClockCoordinateFrame.Work a) × (Reg m × I))

noncomputable local instance executionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q (Reg a × I)) :=
  BinaryClockSingleCU.newDecidableEq q (Reg a × I)

/-- A basis-fiber embedding places a state on the selected ancilla label and gives zero on every
other label. -/
theorem fiber_apply {X Y : Type} [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (a : X) (v : QState Y) (x : X × Y) :
    (encodingFiber a *ᵥ v) x = if x.1 = a then v x.2 else 0 := by
  by_cases h : x.1 = a
  · simp only [encodingFiber, Matrix.of_apply, Matrix.mulVec, dotProduct, h, true_and,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [encodingFiber, Matrix.of_apply, Matrix.mulVec, dotProduct, h, false_and,
      if_false, zero_mul, Finset.sum_const_zero]

/-- Applying an isometry to a normalized state preserves normalization. -/
theorem normalized_isometry_apply {X Y : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (F : Matrix X Y ℂ) (hF : IsIsometry F)
    (v : QState Y) (hv : Normalized v) : Normalized (F *ᵥ v) := by
  apply (normalized_iff_norm_toEuclidean_fromVec _).mpr
  rw [isometry_mulVec_norm hF, (normalized_iff_norm_toEuclidean_fromVec _).mp hv]

/-- Move the purification environment past the system while retaining the clock coordinate. -/
def logicalEquiv (q : ℕ) : (Reg q × (E × I)) ≃ ((Reg q × I) × E) where
  toFun x := ((x.1,x.2.2),x.2.1)
  invFun x := (x.1.1,(x.2,x.1.2))
  left_inv := by rintro ⟨z,r,i⟩; rfl
  right_inv := by rintro ⟨⟨z,i⟩,r⟩; rfl

/-- Tensor a purification with the uniform binary clock state and rearrange it into logical
simulator coordinates. -/
noncomputable def logicalState (q : ℕ) (ψ : QState (E × I)) : QState ((Reg q × I) × E) :=
  relabelState (logicalEquiv (I := I) (E := E) q) (TensorState (Uniform (Reg q)) ψ)

omit [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] in

/-- A logical history input amplitude factors as the uniform clock amplitude times the
purification amplitude. -/
theorem logicalState_apply (q : ℕ) (ψ : QState (E × I)) (z : Reg q) (i : I) (r : E) :
    logicalState q ψ ((z,i),r) = Uniform (Reg q) z * ψ (r,i) := rfl

/-- The logical history input is normalized whenever the purification is normalized. -/
theorem logicalState_normalized (q : ℕ) (ψ : QState (E × I)) (hψ : Normalized ψ) :
    Normalized (logicalState q ψ) :=
  normalized_relabelState _ (normalized_tensorState
    (normalized_uniform (I := Reg q) Fintype.card_pos) hψ)

/-- Casting a rational midpoint time to the reals equals the real time scale times the real
midpoint. -/
theorem midpoint_time (q : ℕ) (T : ℚ) (j : Fin (2^q)) :
    ((T * Clock.rationalMidpoint (2^q) j : ℚ) : ℝ) =
      (T : ℝ) * Clock.midpoint (2^q) j := by
  simp only [Clock.rationalMidpoint, Clock.midpoint,
    Rat.cast_mul, Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]

/-- The uniform amplitude is unchanged when a binary clock string is converted to its finite
clock label. -/
theorem clock_uniform (q : ℕ) (z : Reg q) :
    Uniform (Reg q) z = Uniform (Fin (2^q)) (Clock.clockEquiv q z) := by
  simp only [Uniform, Fintype.card_congr (Clock.clockEquiv q)]

/-- The real cast of a rational midpoint equals the corresponding real midpoint. -/
theorem midpoint_cast (N : ℕ) (j : Fin N) :
    ((Clock.rationalMidpoint N j : ℚ) : ℝ) =
      Clock.midpoint N j := by
  simp only [Clock.rationalMidpoint, Clock.midpoint,
    Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat]

/-- On each clock and environment slice, the purified target applies Hamiltonian evolution at
that clock's midpoint time. -/
theorem target_slice (q : ℕ) (H : Matrix I I ℂ) (T : ℚ)
    (Ψ : QState ((Reg q × I) × E)) (z : Reg q) (i : I) (r : E) :
    (BinaryClockPurifier.target (E := E) q H T *ᵥ Ψ) ((z,i),r) =
      (HamiltonianEvolution H ((T : ℝ) * Clock.midpoint (2^q)
        (Clock.clockLabel q z)) *ᵥ (fun j => Ψ ((z,j),r))) i := by
  simp [BinaryClockPurifier.target, BinaryClockPhysicalTime.physicalTarget,
    Matrix.mulVec, dotProduct, Qatlib.Concepts.BlockEncoding.LCU.select,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul, Rat.cast_mul, midpoint_cast]

/-- Rearrange the projector ancilla and raw simulator coordinates into the readout result
coordinates. -/
def outputEquiv (q a m : ℕ) :
    (Reg m × Raw q a I E) ≃ Result q a m I E where
  toFun x :=
    let p := BinaryClockCoordinateFrame.placement (I := I) (E := E) q a x.2
    (Clock.clockEquiv q p.1, (p.2.1,(x.1,p.2.2)))
  invFun y :=
    (y.2.2.1, (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a).symm
      ((Clock.clockEquiv q).symm y.1, (y.2.1,y.2.2.2)))
  left_inv := by
    rintro ⟨anc,x⟩
    (try dsimp only)
    simp only [Equiv.symm_apply_apply]
    change (anc, (BinaryClockCoordinateFrame.placement q a).symm
      (BinaryClockCoordinateFrame.placement q a x)) = (anc,x)
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨j,⟨ew,⟨anc,i⟩⟩⟩
    simp only [Equiv.apply_symm_apply]

/-- The projector encoding acting on its ancilla and system, transported to raw simulator
coordinates. -/
noncomputable def projectorPort (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) :
    Matrix (Reg m × Raw q a I E) (Reg m × Raw q a I E) ℂ :=
  relabelGate (outputEquiv (I := I) (E := E) q a m).symm
    (parallelOracle (J := Fin (2^q))
      (parallelOracle (J := E × BinaryClockCoordinateFrame.Work a) UPi))

/-- Transporting a unitary projector encoding to the raw simulator coordinates preserves
unitarity. -/
theorem projectorPort_unitary (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPi : UPi ∈ Matrix.unitaryGroup (Reg m × I) ℂ) :
    projectorPort (E := E) q a m UPi ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup (outputEquiv (I := I) (E := E) q a m).symm _).2
    (parallelOracle_unitary (parallelOracle_unitary hPi))

/-- Insert the zero projector ancilla, apply the projector port, and relabel the resulting state
into readout coordinates. -/
noncomputable def projectorTransport (q a m : ℕ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (v : QState (Raw q a I E)) :
    QState (Result q a m I E) :=
  relabelState (outputEquiv q a m)
    (projectorPort q a m UPi *ᵥ (encodingFiber (ZeroStr m) *ᵥ v))

/-- Projector transport preserves differences of input states. -/
theorem transport_sub (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (v w : QState (Raw q a I E)) :
    projectorTransport q a m UPi v - projectorTransport q a m UPi w =
      projectorTransport q a m UPi (v-w) := by
  funext x
  simp only [projectorTransport, relabelState, Function.comp_apply,
    Matrix.mulVec_sub, Pi.sub_apply]

/-- Projector transport preserves the Euclidean norm when the projector encoding is unitary. -/
theorem transport_norm (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPi : UPi ∈ Matrix.unitaryGroup (Reg m × I) ℂ) (v : QState (Raw q a I E)) :
    ‖toEuclidean_fromVec (projectorTransport q a m UPi v)‖ = ‖toEuclidean_fromVec v‖ := by
  have hi : IsIsometry (projectorPort (E := E) q a m UPi) := by
    simpa only [IsIsometry, Matrix.star_eq_conjTranspose] using!
      (projectorPort_unitary q a m UPi hPi).1
  rw [projectorTransport, norm_toEuclidean_relabelState, isometry_mulVec_norm hi,
    isometry_mulVec_norm (encodingFiber_isIsometry (I := Raw q a I E) (ZeroStr m))]

/-- Projector transport equals the extended projector gate applied after insertion and
relabeling of the zero ancilla. -/
theorem transport_gate (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (v : QState (Raw q a I E)) :
    projectorTransport q a m UPi v =
      parallelOracle (J := Fin (2^q))
        (parallelOracle (J := E × BinaryClockCoordinateFrame.Work a) UPi) *ᵥ
          relabelState (outputEquiv q a m) (encodingFiber (ZeroStr m) *ᵥ v) := by
  let e := outputEquiv (I := I) (E := E) q a m
  let P := parallelOracle (J := Fin (2^q))
    (parallelOracle (J := E × BinaryClockCoordinateFrame.Work a) UPi)
  let φ := encodingFiber (ZeroStr m) *ᵥ v
  have h := applyGate_relabelGate e.symm P (relabelState e φ)
  rw [relabelState_relabelState] at h
  have hh := congrArg (relabelState e) h
  have hinv (v) : relabelState e (relabelState e.symm v) = v :=
    relabelState_relabelState e.symm v
  simpa only [hinv, projectorTransport, projectorPort, ApplyGate, e, P, φ] using! hh

/-- Each readout slice is obtained by applying `UPi` to the corresponding raw-state slice
embedded at the zero projector ancilla. -/
theorem transport_slice (q a m : ℕ) (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (v : QState (Raw q a I E)) (j : Fin (2^q))
    (ew : E × BinaryClockCoordinateFrame.Work a) (b : Reg m) (i : I) :
    projectorTransport q a m UPi v (j,(ew,(b,i))) =
      (UPi *ᵥ fun y : Reg m × I => if y.1 = ZeroStr m then
        relabelState (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a) v
          ((Clock.clockEquiv q).symm j,(ew,y.2)) else 0) (b,i) := by
  rw [transport_gate]
  change (Qatlib.Concepts.BlockEncoding.LCU.select (fun _ : Fin (2^q) =>
    Qatlib.Concepts.BlockEncoding.LCU.select (fun _ : E × BinaryClockCoordinateFrame.Work a => UPi)) *ᵥ
      relabelState (outputEquiv q a m) (encodingFiber (ZeroStr m) *ᵥ v)) (j,(ew,(b,i))) = _
  rw [BinaryClockSignalWord.select_mulVec, BinaryClockSignalWord.select_mulVec]
  apply congrArg (fun x : QState (Reg m × I) => (UPi *ᵥ x) (b,i))
  funext y
  rcases y with ⟨b',i'⟩
  change (encodingFiber (ZeroStr m) *ᵥ v)
    (b', (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a).symm
      ((Clock.clockEquiv q).symm j,(ew,i'))) = _
  rw [fiber_apply]
  rfl

/-- The projector readout state produced by the purified physical-time simulator from the
logical history input. -/
noncomputable def actual (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (ψ : QState (E × I)) :
    QState (Result q a m I E) :=
  projectorTransport q a m UPi
    (evaluate (BinaryClockPurifier.oracle (E := E) q U_H)
      (BinaryClockPurifier.instructions q (encodingFiber (I := I) (ZeroStr a)) α T k) *ᵥ
        (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ
          logicalState q ψ))

/-- The projector readout state obtained from exact physical midpoint evolution in the simulator
frame. -/
noncomputable def framedReference (q a m : ℕ) (H : Matrix I I ℂ) (T : ℚ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (ψ : QState (E × I)) :
    QState (Result q a m I E) :=
  projectorTransport q a m UPi
    (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ
      (BinaryClockPurifier.target q H T *ᵥ logicalState q ψ))

/-- For a normalized purification, the actual and framed reference outputs differ in Euclidean
norm by at most `(q+1)*2⁻ᵏ`. -/
theorem full_output_error (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (hα : 0 < α)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (henc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U_H
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPi : UPi ∈ Matrix.unitaryGroup (Reg m × I) ℂ)
    (ψ : QState (E × I)) (hψ : Normalized ψ) :
    ‖toEuclidean_fromVec (actual q a m α T k U_H UPi ψ -
      framedReference q a m H T UPi ψ)‖ ≤ ((q+1 : ℕ) : ℝ) * (1/2 : ℝ)^k := by
  have hn : ‖toEuclidean_fromVec (logicalState q ψ)‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec _).mp (logicalState_normalized q ψ hψ)
  have hsim := BinaryClockPurifier.full_output_error q α T k H U_H
    (encodingFiber (I := I) (ZeroStr a)) hα hH henc (logicalState q ψ)
  simp only [hn, mul_one] at hsim
  change ‖toEuclidean_fromVec
    (projectorTransport q a m UPi _ - projectorTransport q a m UPi _)‖ ≤ _
  rw [transport_sub, transport_norm q a m UPi hPi]
  exact hsim

/-- The actual projector readout state is normalized under the stated unitary encoding and
normalized purification assumptions. -/
theorem actual_normalized (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (henc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U_H
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPi : UPi ∈ Matrix.unitaryGroup (Reg m × I) ℂ)
    (ψ : QState (E × I)) (hψ : Normalized ψ) : Normalized (actual q a m α T k U_H UPi ψ) := by
  have hf := normalized_isometry_apply _
    (BinaryClockPurifier.initialFrame_isometry (E := E) q α H U_H
      (encodingFiber (I := I) (ZeroStr a)) hH henc) _ (logicalState_normalized q ψ hψ)
  have ho : BinaryClockPurifier.oracle (E := E) q U_H ∈ Matrix.unitaryGroup _ ℂ := by
    exact tensorGate_unitary (BinaryClockSingleCU.oracle_unitary q henc.unitary)
        (Submonoid.one_mem _)
  have he := (BinaryClockPurifier.resources (E := E) q α T k H U_H
    (encodingFiber (I := I) (ZeroStr a)) hH henc).1.evaluate_unitary ho
  have hs := normalized_applyGate he hf
  have hz := normalized_isometry_apply _
    (encodingFiber_isIsometry (I := Raw q a I E) (ZeroStr m)) _ hs
  exact normalized_relabelState _ (normalized_applyGate (projectorPort_unitary q a m UPi hPi) hz)

/-- The framed reference equals the ideal midpoint projector history state built from the
augmented purification. -/
theorem framedReference_eq (q a m : ℕ) (H : Matrix I I ℂ) (T : ℚ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (ψ : QState (E × I)) :
    framedReference q a m H T UPi ψ =
      ProjectorHistoryBorn.idealOutput UPi (ZeroStr m)
        (fun j : Fin (2^q) => HamiltonianEvolution H
          ((T : ℝ) * Clock.midpoint (2^q) j))
        (BinaryClockCoordinateFrame.augmented a ψ) := by
  funext x
  rcases x with ⟨j,⟨⟨r,w⟩,⟨b,i⟩⟩⟩
  unfold framedReference
  rw [transport_slice]
  let z := (Clock.clockEquiv q).symm j
  let V := HamiltonianEvolution H ((T : ℝ) * Clock.midpoint (2^q) j)
  let χ : QState I := fun i' => ψ (r,i')
  have hj : Clock.clockLabel q z = j := by
    change Clock.clockEquiv q z = j
    exact Equiv.apply_symm_apply _ _
  have hu : Uniform (Reg q) z = Uniform (Fin (2^q)) j := by
    have hh := clock_uniform q z
    change Uniform (Reg q) z = Uniform (Fin (2^q))
      (Clock.clockLabel q z) at hh
    rw [hj] at hh
    exact hh
  have hlogical : (fun i' => logicalState q ψ ((z,i'),r)) =
      Uniform (Reg q) z • χ := by
    funext i'
    exact logicalState_apply q ψ z i' r
  have ht (i' : I) :
      (BinaryClockPurifier.target q H T *ᵥ logicalState q ψ) ((z,i'),r) =
        Uniform (Fin (2^q)) j * (V *ᵥ χ) i' := by
    rw [target_slice, hj, hlogical, Matrix.mulVec_smul, hu]
    rfl
  have hf (i' : I) :
      relabelState (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a)
        (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ
          (BinaryClockPurifier.target q H T *ᵥ logicalState q ψ)) (z,((r,w),i')) =
        BinaryClockCoordinateFrame.eta a w *
          (Uniform (Fin (2^q)) j * (V *ᵥ χ) i') := by
    rw [BinaryClockCoordinateFrame.relabel_frame]
    change BinaryClockCoordinateFrame.eta a w * _ = _
    rw [ht]
  have haug : (fun i' => BinaryClockCoordinateFrame.augmented a ψ ((r,w),i')) =
      BinaryClockCoordinateFrame.eta a w • χ := by
    funext i'
    rfl
  have hinput :
      (fun y : Reg m × I => if y.1 = ZeroStr m then
        relabelState (BinaryClockCoordinateFrame.placement (I := I) (E := E) q a)
          (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ
            (BinaryClockPurifier.target q H T *ᵥ logicalState q ψ)) (z,((r,w),y.2)) else 0) =
      Uniform (Fin (2^q)) j •
        (encodingFiber (ZeroStr m) *ᵥ (V *ᵥ
          (fun i' => BinaryClockCoordinateFrame.augmented a ψ ((r,w),i')))) := by
    rw [haug, Matrix.mulVec_smul, Matrix.mulVec_smul]
    funext y
    rcases y with ⟨b',i'⟩
    rw [hf]
    simp only [Pi.smul_apply, smul_eq_mul, fiber_apply]
    by_cases hb : b' = ZeroStr m <;> simp [hb, mul_left_comm]
  change (UPi *ᵥ _) (b,i) = Uniform (Fin (2^q)) j *
    (UPi *ᵥ (encodingFiber (ZeroStr m) *ᵥ (V *ᵥ
      (fun i' => BinaryClockCoordinateFrame.augmented a ψ ((r,w),i'))))) (b,i)
  rw [hinput, Matrix.mulVec_smul]
  rfl

/-- The physical projector integral differs from `T` times the actual zero-ancilla probability
by at most `α*‖Pi‖*T²/(2*2^q) + 2*T*(q+1)*2⁻ᵏ` under the stated assumptions. -/
theorem actual_integral_error (q a m : ℕ) (α T : ℚ) (k : ℕ)
    (hα : 0 < α) (hT : 0 ≤ T) (H Pi : Matrix I I ℂ) (hH : H.IsHermitian)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (hHenc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U_H
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPienc : ProjectedUnitaryEncoding Pi UPi (encodingFiber (I := I) (ZeroStr m))
      (encodingFiber (I := I) (ZeroStr m))) (hPistar : Piᴴ = Pi) (hPisq : Pi * Pi = Pi)
    (ψ : QState (E × I)) (hψ : Normalized ψ) :
    |(∫ t in (0:ℝ)..(T:ℝ), ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) -
      (T:ℝ) * MeasureProb (actual q a m α T k U_H UPi ψ)
        {x | x.2.2.1 = ZeroStr m}| ≤
      (α:ℝ) * ‖Pi‖ * (T:ℝ)^2 / (2 * (2^q : ℕ)) +
        2 * (T:ℝ) * (((q+1 : ℕ) : ℝ) * (1/2 : ℝ)^k) := by
  have herr := full_output_error q a m α T k H hH hα U_H hHenc UPi hPienc.unitary ψ hψ
  rw [framedReference_eq] at herr
  have hn := actual_normalized q a m α T k H hH U_H hHenc UPi hPienc.unitary ψ hψ
  have ht : (0 : ℝ) ≤ T := by exact_mod_cast hT
  have hbound := ProjectorHistoryBorn.approximate_history_integral_error H hH Pi UPi
    (ZeroStr m) hPienc hPistar hPisq (BinaryClockCoordinateFrame.augmented a ψ)
    (BinaryClockCoordinateFrame.augmented_normalized a ψ hψ) (α : ℝ) (T : ℝ)
    (BinaryClockPhysicalTime.source_norm_le α H U_H (encodingFiber (I := I) (ZeroStr a)) hα hHenc)
    ht (2^q) (by positivity) (actual q a m α T k U_H UPi ψ) hn
    (((q+1 : ℕ) : ℝ) * (1/2 : ℝ)^k) herr
  simpa only [BinaryClockCoordinateFrame.augmented_density] using! hbound

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorReadout
