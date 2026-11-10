/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedStat
import Qatlib.Papers.VarTimeAmpAmp10.StopModel.VariableTimeModelWellFormedContracts
import Qatlib.Concepts.BlockEncoding.LinearCombination
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.LinearCombination

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Matrix

section
variable {C : Type} [Fintype C] [DecidableEq C]

theorem vt_stage_stopped_ket {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (p : VtSpace C) (hp : p.1 ≠ vtRunningFlag) :
    U *ᵥ Ket p = Ket p := by
  funext q
  rw [mulVec_ket_apply, hU.2 p hp q]
  rfl

theorem vt_stage_stopped_row {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (p : VtSpace C) (hp : p.1 ≠ vtRunningFlag)
    (q : VtSpace C) : U p q = if p = q then 1 else 0 := by
  have hunit : Uᴴ * U = 1 := by
    simpa only [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose] using hU.1
  have hadj : Uᴴ *ᵥ Ket p = Ket p := by
    calc
      _ = Uᴴ *ᵥ (U *ᵥ Ket p) := by rw [vt_stage_stopped_ket hU p hp]
      _ = Ket p := by rw [Matrix.mulVec_mulVec, hunit, Matrix.one_mulVec]
  have he := congrArg star (congrFun hadj q)
  simpa [mulVec_ket_apply, Matrix.conjTranspose_apply, Ket, eq_comm] using he

theorem vt_stage_stopped_apply {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (ψ : QState (VtSpace C)) (p : VtSpace C)
    (hp : p.1 ≠ vtRunningFlag) : ApplyGate U ψ p = ψ p := by
  simp [ApplyGate, Matrix.mulVec, dotProduct, vt_stage_stopped_row hU p hp]

theorem vt_stage_collapse {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (ψ : QState (VtSpace C)) :
    Collapse (ApplyGate U ψ) (stoppedSet C) = Collapse ψ (stoppedSet C) := by
  funext p
  rw [collapse_apply, collapse_apply]
  by_cases hp : p ∈ stoppedSet C
  · simp only [if_pos hp]
    exact vt_stage_stopped_apply hU ψ p (by simpa [stoppedSet] using hp)
  · simp [hp]

theorem vt_stage_measure_eq {U : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (ψ : QState (VtSpace C)) :
    MeasureProb (ApplyGate U ψ) (stoppedSet C) = MeasureProb ψ (stoppedSet C) := by
  rw [← sum_normSq_collapse, vt_stage_collapse hU, sum_normSq_collapse]

theorem isVtStage_one : IsVtStage (1 : Matrix (VtSpace C) (VtSpace C) ℂ) := by
  exact ⟨(Matrix.unitaryGroup _ _).one_mem, fun _ _ _ => Matrix.one_apply⟩

theorem isVtStage_mul {U V : Matrix (VtSpace C) (VtSpace C) ℂ}
    (hU : IsVtStage U) (hV : IsVtStage V) : IsVtStage (U * V) := by
  refine ⟨(Matrix.unitaryGroup _ _).mul_mem hU.1 hV.1, ?_⟩
  intro p hp q
  rw [← mulVec_ket_apply (U * V) p q, ← Matrix.mulVec_mulVec,
    vt_stage_stopped_ket hV p hp, mulVec_ket_apply]
  exact hU.2 p hp q

theorem vt_fold_isVtStage (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (A : Matrix (VtSpace C) (VtSpace C) ℂ)
    (hA : IsVtStage A) : IsVtStage (stages.foldl (fun A U => U * A) A) := by
  induction stages generalizing A with
  | nil => exact hA
  | cons U us ih =>
      exact ih (fun V hV => hs V (List.mem_cons_of_mem U hV)) (U * A)
        (isVtStage_mul (hs U (by simp)) hA)

theorem vtRunMatrix_isVtStage
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (k : ℕ) : IsVtStage (vtRunMatrix stages k) := by
  exact vt_fold_isVtStage (stages.take k)
    (fun U hU => hs U (List.mem_of_mem_take hU)) 1 isVtStage_one

theorem stoppedMass_eq_initial
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (j₀ : VtSpace C) (k : ℕ) :
    stoppedMass stages j₀ k = MeasureProb (Ket j₀) (stoppedSet C) :=
  vt_stage_measure_eq (vtRunMatrix_isVtStage stages hs k) (Ket j₀)

theorem vt_pstop_eq_zero (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (j₀ : VtSpace C) (j : ℕ) :
    pstop stages j₀ j = 0 := by
  simp [pstop, stoppedMass_eq_initial stages hs]

theorem vtTav_eq_zero (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (j₀ : VtSpace C) : vtTav stages j₀ = 0 := by
  simp [vtTav, vt_pstop_eq_zero stages hs]

theorem variableTimeModelWellFormed_proof : variableTimeModelWellFormed := by
  intro C _ _ stages hs
  refine ⟨fun U hU ψ => vt_stage_collapse hU ψ, ?_, ?_⟩
  · intro j₀ k _
    rw [stoppedMass_eq_initial stages hs j₀ k,
      stoppedMass_eq_initial stages hs j₀ (k + 1)]
  · intro k
    exact (vtRunMatrix_isVtStage stages hs k).1

theorem vt_running_source_good_mass_zero
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ))
    (hs : ∀ U ∈ stages, IsVtStage U) (j₀ : VtSpace C)
    (hj : j₀.1 = vtRunningFlag) (k : ℕ) :
    MeasureProb (vtState stages k (Ket j₀)) (goodSet C) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  have hpg : p.1 = vtGoodFlag := by simpa [goodSet] using hp
  have hpr : p.1 ≠ vtRunningFlag := by rw [hpg]; decide
  have hpj : p ≠ j₀ := by
    intro he
    have := congrArg Prod.fst he
    rw [hpg, hj] at this
    exact (by decide : vtGoodFlag ≠ vtRunningFlag) this
  have he := vt_stage_stopped_apply (vtRunMatrix_isVtStage stages hs k) (Ket j₀) p hpr
  change ‖ApplyGate (vtRunMatrix stages k) (Ket j₀) p‖ ^ 2 = 0
  rw [he]
  simp [Ket, hpj]

end

theorem variableTimeModelWellFormed_answer : VariableTimeModelWellFormed := by
  intro C _ _ stages history hs
  refine ⟨?_,?_,growing_prefix_unitary stages history hs⟩
  · intro k hk ψ
    exact growing_stage_preserves_reached (hs.2.2.2 k hk) ψ
  · intro ψ k hk
    exact ⟨reached_stopped_mass_mono stages history hs ψ k hk,reached_pstop_nonneg stages history hs ψ k hk⟩
end Qatlib.Papers.VarTimeAmpAmp10.StopModel
