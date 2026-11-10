/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QlsReadoutSpec.Amplification.PaidModels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

def Clause3ClockFlagResolutions : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (m : ℕ)
    (P : Fin (m+1) → Matrix H H ℂ) (bad : Matrix H H ℂ), clockLegal m P bad →
    (∀ j k, j.val ≤ k.val →
      P k*P j=P j ∧ P j*P k=P j ∧
      (1-P j)*(1-P k)=1-P k ∧ (1-P k)*(1-P j)=1-P k ∧
      IsOrthogonalProjector (P k-P j) ∧
      IsOrthogonalProjector (potential (P j) bad) ∧
      potential (P k) bad*potential (P j) bad=potential (P k) bad ∧
      potential (P j) bad*potential (P k) bad=potential (P k) bad ∧
      (potential (P j) bad-potential (P k) bad).PosSemidef) ∧
    (∑ j : Fin m, (P ⟨j.val+1,by omega⟩-P ⟨j.val,by omega⟩))=1 ∧
    (∀ j : Fin m,
      let D := P ⟨j.val+1,by omega⟩-P ⟨j.val,by omega⟩
      IsOrthogonalProjector D ∧ D*bad=bad*D ∧
      IsOrthogonalProjector (D*bad) ∧ IsOrthogonalProjector (D*(1-bad))) ∧
    (∀ j k : Fin m, j≠k →
      (P ⟨j.val+1,by omega⟩-P ⟨j.val,by omega⟩)*
        (P ⟨k.val+1,by omega⟩-P ⟨k.val,by omega⟩)=0) ∧
    (∀ j, potential (P j) bad=P j*(1-bad)+(1-P j)) ∧
    potential (P 0) bad=1 ∧ potential (P ⟨m,by omega⟩) bad=1-bad

end Qatlib.Concepts.QlsReadoutSpec.Amplification
