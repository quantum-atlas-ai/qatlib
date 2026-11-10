/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPurifier
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalInitialization
import Qatlib.Concepts.OperatorAccess.EncodedAccess
set_option warningAsError false

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockCoordinateFrame

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit
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
open Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Kronecker

abbrev Work (a : ℕ) := Bool × (Bool × (Bool × (Bool × (Bool × Reg a))))

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

def placement (q a : ℕ) :
    (BinaryClockSingleCU.New q (Reg a × I) × E) ≃ (Reg q × ((E × Work a) × I)) where
  toFun x :=
    let p := x.1
    let w : Work a := (p.1, (p.2.2.1, (p.2.2.2.1,
      (p.2.2.2.2.1, (p.2.2.2.2.2.1, p.2.2.2.2.2.2.1)))))
    (p.2.1, ((x.2, w), p.2.2.2.2.2.2.2))
  invFun y :=
    let w := y.2.1.2
    ((w.1, (y.1, (w.2.1, (w.2.2.1, (w.2.2.2.1,
      (w.2.2.2.2.1, (w.2.2.2.2.2, y.2.2))))))), y.2.1.1)
  left_inv := by
    rintro ⟨⟨t, ⟨z, ⟨e, ⟨u, ⟨b, ⟨c, ⟨anc, i⟩⟩⟩⟩⟩⟩⟩, r⟩
    rfl
  right_inv := by
    rintro ⟨z, ⟨⟨r, w⟩, i⟩⟩
    rcases w with ⟨t,e,u,b,c,anc⟩
    rfl

noncomputable def eta (a : ℕ) : QState (Work a) := fun w =>
  if w.1 = false ∧ w.2.1 = false ∧ w.2.2.1 = false ∧
      w.2.2.2.2.2 = ZeroStr a then Complex.I / 2 else 0

theorem average_phase (b c : Bool) :
    realPartAmplitude b * realPartAmplitude c = Complex.I / 2 := by
  apply Complex.ext <;> norm_num [realPartAmplitude, Complex.mul_re, Complex.mul_im]

theorem eta_entry (a : ℕ) (t e u b c : Bool) (anc : Reg a) :
    eta a (t,(e,(u,(b,(c,anc))))) =
      if t = false ∧ e = false ∧ u = false ∧ anc = ZeroStr a then Complex.I / 2 else 0 := rfl

private theorem phase_norm_sq : ‖(Complex.I / 2 : ℂ)‖^2 = (1 : ℝ)/4 := by
  rw [norm_div, Complex.norm_I]
  norm_num

theorem eta_normalized (a : ℕ) : Normalized (eta a) := by
  norm_num [Normalized, eta, Fintype.sum_prod_type, apply_ite]

noncomputable local instance oldExecutionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.Old q (Reg a × I)) :=
  BinaryClockSingleCU.oldDecidableEq q (Reg a × I)

noncomputable local instance executionDecidableEq (q a : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q (Reg a × I)) :=
  BinaryClockSingleCU.newDecidableEq q (Reg a × I)

private theorem fiber_mul_entry {X Y Z : Type} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y] (b : X) (F : Matrix Y Z ℂ) (x : X × Y) (j : Z) :
    (encodingFiber (I := Y) b * F : Matrix (X × Y) Z ℂ) x j = if x.1 = b then F x.2 j else 0 := by
  simp [Matrix.mul_apply, encodingFiber, ite_and, ite_mul]

theorem frame_entry (q a : ℕ) (t e u b c : Bool) (z z' : Reg q)
    (anc : Reg a) (i j : I) :
    BinaryClockSingleCU.initialFrame q (encodingFiber (I := I) (ZeroStr a))
      (t,(z,(e,(u,(b,(c,(anc,i))))))) (z',j) =
      if t = false ∧ e = false ∧ u = false ∧ anc = ZeroStr a ∧ z = z' ∧ i = j then
        Complex.I / 2 else 0 := by
  change (encodingFiber false * BinaryClockSignalWord.commonFrame q
    (encodingFiber (I := I) (ZeroStr a)) : Matrix (BinaryClockSingleCU.New q (Reg a × I)) (Reg q × I) ℂ) _ _ = _
  rw [fiber_mul_entry]
  simp only [BinaryClockSignalWord.commonFrame, BinaryClockSignalWord.liftFrame,
    Matrix.kronecker_apply, Matrix.one_apply]
  change (if t = false then (if z = z' then 1 else 0) *
    (encodingFiber false * BinaryClockSignalWord.simulatorFrame
      (encodingFiber (I := I) (ZeroStr a)) : Matrix (Bool × BinaryClockSignalWord.SimulatorSpace (Reg a × I)) I ℂ) (e,(u,(b,(c,(anc,i))))) j else 0) = _
  rw [fiber_mul_entry, BinaryClockSignalInitialization.simulatorFrame_entry]
  by_cases hi : i = j <;> by_cases hz : z = z' <;>
    simp [encodingFiber, average_phase, ite_and, hi, hz]

theorem frame_apply (q a : ℕ) (Ψ : QState ((Reg q × I) × E))
    (t e u b c : Bool) (z : Reg q) (anc : Reg a) (i : I) (r : E) :
    (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ Ψ)
      ((t,(z,(e,(u,(b,(c,(anc,i))))))),r) =
        eta a (t,(e,(u,(b,(c,anc))))) * Ψ ((z,i),r) := by
  simp [BinaryClockPurifier.initialFrame, BinaryClockPhysicalTime.initialFrame,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    frame_entry, eta, Matrix.one_apply, mul_ite, ite_mul, ite_and]

theorem relabel_frame (q a : ℕ) (Ψ : QState ((Reg q × I) × E)) :
    relabelState (placement (I := I) (E := E) q a)
      (BinaryClockPurifier.initialFrame q (encodingFiber (I := I) (ZeroStr a)) *ᵥ Ψ) =
        fun y => eta a y.2.1.2 * Ψ ((y.1,y.2.2),y.2.1.1) := by
  funext y
  rcases y with ⟨z,⟨⟨r,w⟩,i⟩⟩
  rcases w with ⟨t,e,u,b,c,anc⟩
  exact frame_apply q a Ψ t e u b c z anc i r

noncomputable def augmented (a : ℕ) (ψ : QState (E × I)) : QState ((E × Work a) × I) :=
  fun x => eta a x.1.2 * ψ (x.1.1,x.2)

theorem augmented_normalized (a : ℕ) (ψ : QState (E × I)) (hψ : Normalized ψ) :
    Normalized (augmented a ψ) := by
  let e : (Work a × (E × I)) ≃ ((E × Work a) × I) :=
    { toFun := fun x => ((x.2.1,x.1),x.2.2)
      invFun := fun x => (x.1.2,(x.1.1,x.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact normalized_relabelState e (normalized_tensorState (eta_normalized a) hψ)

omit [Fintype I] [DecidableEq I] [DecidableEq E] in

theorem augmented_density (a : ℕ) (ψ : QState (E × I)) :
    purifiedDensity (augmented a ψ) = purifiedDensity ψ := by
  have he : (∑ w : Work a, eta a w * star (eta a w)) = 1 := by
    have hn := eta_normalized a
    change (∑ w, ‖eta a w‖^2) = 1 at hn
    have hw (w : Work a) : eta a w * star (eta a w) = ((‖eta a w‖^2 : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_norm_sq, Complex.star_def, Complex.mul_conj]
    simp only [hw, ← Complex.ofReal_sum, hn, Complex.ofReal_one]
  ext i j
  simp only [purifiedDensity, Matrix.of_apply, augmented, star_mul]
  rw [Fintype.sum_prod_type]
  calc
    _ = ∑ r : E, (∑ w : Work a, eta a w * star (eta a w)) *
        (ψ (r,i) * star (ψ (r,j))) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro w _
      ring
    _ = _ := by simp only [he, one_mul]

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockCoordinateFrame
