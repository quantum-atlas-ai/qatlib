/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PhaseGeometry.Phase
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.CoherentSim.CoherentOAA

open Matrix
open Qatlib
open Qatlib
open Qatlib
open Qatlib
variable {H K : Type*} [Fintype H] [DecidableEq H]

structure SignalPair (U P Q : Matrix H H ℂ) (σ : ℂ)
    (r l : Matrix H K ℂ) : Prop where
  unitary : U ∈ Matrix.unitaryGroup H ℂ
  right_projector : IsOrthogonalProjector P
  left_projector : IsOrthogonalProjector Q
  right_fixed : P * r = r
  left_fixed : Q * l = l
  forward : Q * U * r = σ • l
  backward : P * Uᴴ * l = σ • r

noncomputable def rightResidual (U : Matrix H H ℂ) (σ : ℂ)
    (r l : Matrix H K ℂ) : Matrix H K ℂ := Uᴴ * l - σ • r

noncomputable def leftResidual (U : Matrix H H ℂ) (σ : ℂ)
    (r l : Matrix H K ℂ) : Matrix H K ℂ := U * r - σ • l

theorem SignalPair.adjoint {U P Q : Matrix H H ℂ} {σ : ℂ} {r l : Matrix H K ℂ}
    (h : SignalPair U P Q σ r l) : SignalPair Uᴴ Q P σ l r := by
  refine ⟨adjoint_unitary h.unitary, h.left_projector, h.right_projector,
    h.left_fixed, h.right_fixed, h.backward, ?_⟩
  simpa using h.forward

theorem SignalPair.rightResidual_zero {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) :
    P * rightResidual U σ r l = 0 := by
  simp only [rightResidual, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
    h.backward, h.right_fixed, sub_self]

theorem SignalPair.leftResidual_zero {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) :
    Q * leftResidual U σ r l = 0 := by
  simp only [leftResidual, Matrix.mul_sub, Matrix.mul_smul, ← Matrix.mul_assoc,
    h.forward, h.left_fixed, sub_self]

omit [DecidableEq H] in

theorem signal_first (U : Matrix H H ℂ) (σ : ℂ) (r l : Matrix H K ℂ) :
    U * r = σ • l + leftResidual U σ r l := by
  unfold leftResidual
  abel

theorem SignalPair.signal_second {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) :
    U * rightResidual U σ r l =
      (1 - σ ^ 2) • l - σ • leftResidual U σ r l := by
  have hu : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using h.unitary.2
  simp only [rightResidual, Matrix.mul_sub, Matrix.mul_smul,
    ← Matrix.mul_assoc, hu, Matrix.one_mul]
  unfold leftResidual
  module

theorem SignalPair.step {U P Q : Matrix H H ℂ} {σ : ℂ}
    {r l : Matrix H K ℂ} (h : SignalPair U P Q σ r l) (z a b : ℂ) :
    phaseRotation Q z * U * (a • r + b • rightResidual U σ r l) =
      (z * (σ * a + (1 - σ ^ 2) * b)) • l +
        (star z * (a - σ * b)) • leftResidual U σ r l := by
  rw [Matrix.mul_assoc, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    signal_first U σ r l, h.signal_second]
  simp only [smul_add, smul_sub, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_smul,
    phaseRotation_mul_of_fixed h.left_fixed,
    phaseRotation_mul_of_zero h.leftResidual_zero, smul_smul]
  module

section Encoding

variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

theorem lift_compressed_action {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (v : Matrix I K ℂ) :
    rangeProjector L * U * (R * v) = L * (A * v) := by
  calc
    rangeProjector L * U * (R * v) = L * compress L U R * v := by
      simp only [rangeProjector, compress, Matrix.mul_assoc]
    _ = L * (A * v) := by rw [h.encoded, Matrix.mul_assoc]

theorem signalPair_of_encoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {σ : ℂ}
    {v : Matrix I K ℂ} {w : Matrix O K ℂ}
    (hav : A * v = σ • w) (haw : Aᴴ * w = σ • v) :
    SignalPair U (rangeProjector R) (rangeProjector L) σ (R * v) (L * w) := by
  refine ⟨h.unitary, rangeProjector_isOrthogonalProjector h.right_isometry,
    rangeProjector_isOrthogonalProjector h.left_isometry, ?_, ?_, ?_, ?_⟩
  · rw [← Matrix.mul_assoc, rangeProjector_mul h.right_isometry]
  · rw [← Matrix.mul_assoc, rangeProjector_mul h.left_isometry]
  · rw [lift_compressed_action h, hav, Matrix.mul_smul]
  · rw [lift_compressed_action h.adjoint, haw, Matrix.mul_smul]

end Encoding

end Qatlib.Concepts.CoherentSim.CoherentOAA
