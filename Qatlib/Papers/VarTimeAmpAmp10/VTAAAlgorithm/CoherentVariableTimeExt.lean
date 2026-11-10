/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeCost
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum


open Qatlib.Foundations.PureStateMath

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt
open Matrix
open Qatlib.Concepts.QlsReadoutSpec.Amplification
open Qatlib.Concepts.QlsReadoutSpec.BlockPrecond
open Qatlib.Concepts.QlsReadoutSpec.PrepLowerBound
open Qatlib.Concepts.QlsReadoutSpec.ProgramModel
open Qatlib.Concepts.QlsReadoutSpec.WalkQSVT
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVtFrame
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
variable {H : Type} [Fintype H] [DecidableEq H] {m : ℕ}

def payload (Φ : QState (Qatlib.Concepts.QlsReadoutSpec.Amplification.Space H 2)) : QState H :=
    fun h => Φ (h, 0)

theorem payload_clean (ψ : QState H) : payload (Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ) = ψ := by
  funext h
  change (if (0 : Fin 2) = 0 then ψ h else 0) = ψ h
  exact if_pos rfl

theorem paidPrefix_payload (f : CoherentVtFrame H m) (ψ : QState H)
    (n : ℕ) (hn : n ≤ m) :
    payload (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f) (paidPrefix f n hn) ψ) =
      f.stageState ψ n hn := by
  rw [Qatlib.Concepts.QlsReadoutSpec.Amplification.run, paidPrefix_clean, payload_clean]

theorem frontier1 (f : CoherentVtFrame H m) (ψ : QState H) (n : ℕ) (hn : n ≤ m) :
    ∃ C : Qatlib.Concepts.QlsReadoutSpec.Amplification.Word H 2, Qatlib.Concepts.QlsReadoutSpec.Amplification.legal m C ∧
      Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) C *ᵥ Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ =
        Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (f.stageState ψ n hn) ∧
      Qatlib.Concepts.QlsReadoutSpec.Amplification.wordMatrix (baseOracles f) (Qatlib.Concepts.QlsReadoutSpec.Amplification.wordAdjoint C) *ᵥ
        Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (f.stageState ψ n hn) = Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) ψ ∧
      Qatlib.Concepts.QlsReadoutSpec.Amplification.gateCount C = 4 * n ∧ Qatlib.Concepts.QlsReadoutSpec.Amplification.weightedCost (fun j => 2 ^ j) C + 1 = 2 ^ n :=
  ⟨paidPrefix f n hn, paidPrefix_legal f n hn, paidPrefix_clean f ψ n hn,
    paidPrefix_reverse_clean f ψ n hn, paidPrefix_knownCount f n hn,
    paidPrefix_accessPrice f n hn⟩

theorem paid_history_retained (f : CoherentVtFrame H m) (ψ : QState H)
    (j k : Fin m) (hjk : j.val ≤ k.val) :
    ApplyGate (f.stopAt j) (payload
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f) (paidPrefix f k.val (by omega)) ψ)) =
    ApplyGate (f.stopAt j) (payload
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f) (paidPrefix f j.val (by omega)) ψ)) := by
  rw [paidPrefix_payload, paidPrefix_payload]
  exact f.frozenFragment_frozen ψ j k hjk

theorem paid_fresh_mass (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    MeasureProb (ApplyGate (f.freshStop j) (payload
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f)
        (paidPrefix f (j.val + 1) (by omega)) ψ))) Finset.univ = f.freshStopMass ψ j := by
  rw [paidPrefix_payload]
  have hzero : f.freshStop j * f.stopAt j = 0 := (f.freshStop_orthogonal j).2
  have hstep : f.freshStop j * f.stageOp j = f.freshStop j * f.round j := by
    change f.freshStop j * (f.stopAt j + (1 - f.stopAt j) * f.round j) = _
    rw [Matrix.mul_add, hzero, _root_.zero_add, ← Matrix.mul_assoc, Matrix.mul_sub,
      Matrix.mul_one, hzero, sub_zero]
  rw [f.stageState_succ, ← applyGate_mul, hstep, applyGate_mul]
  rfl

theorem paid_total_state (f : CoherentVtFrame H m) (ψ : QState H) :
    Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f) (paidPrefix f m (by omega)) ψ =
      Qatlib.Concepts.QlsReadoutSpec.Amplification.clean 2 (by decide) (ApplyGate f.totalOp ψ) := by
  rw [Qatlib.Concepts.QlsReadoutSpec.Amplification.run, paidPrefix_clean,
      f.totalOp_apply_eq_stageState]

theorem paid_history_final (f : CoherentVtFrame H m) (ψ : QState H) (j : Fin m) :
    ApplyGate (f.stopAt j) (payload
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f) (paidPrefix f m (by omega)) ψ)) =
      ApplyGate (f.stopAt j) (f.stageState ψ j.val (by omega)) := by
  rw [paid_total_state, payload_clean]
  exact totalOp_retains_stopHistory f ψ j

theorem paid_complete_fresh_total (f : CoherentVtFrame H m) (ψ : QState H)
    (hcomplete : f.stop ⟨m, by omega⟩ = 1) (hψ : Normalized ψ) :
    (∑ j : Fin m, MeasureProb (ApplyGate (f.freshStop j) (payload
      (Qatlib.Concepts.QlsReadoutSpec.Amplification.run (by decide : 0 < 2) (baseOracles f)
        (paidPrefix f (j.val + 1) (by omega)) ψ))) Finset.univ) = 1 := by
  simp_rw [paid_fresh_mass]
  exact f.freshStopMass_total_eq_one ψ hcomplete hψ

end
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt
