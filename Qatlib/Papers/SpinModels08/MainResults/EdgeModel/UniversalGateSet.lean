/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpinModels08.MainResults.EdgeModel.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
set_option warningAsError false

noncomputable section

open scoped BigOperators Matrix

namespace Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet

open Qatlib.Papers.SpinModels08.MainResults
open Qatlib.Papers.SpinModels08.MainResults.EdgeModel

def singleQubitGate (w : EdgeW 2) : Matrix (Fin 2) (Fin 2) ℂ := fun i j => w i j

theorem singleQubitGate_apply (w : EdgeW 2) (i j : Fin 2) :
    singleQubitGate w i j = w i j := rfl

def diagTwoQubitGate (v : EdgeW 2) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun (i, j) (k, l) => if i = k ∧ j = l then v i j else 0

theorem diagTwoQubitGate_apply (v : EdgeW 2) (i j k l : Fin 2) :
    diagTwoQubitGate v (i, j) (k, l) = if i = k ∧ j = l then v i j else 0 := rfl

def sqLayer {N : ℕ} (hW : Fin N → EdgeW 2) : Matrix (Config 2 N) (Config 2 N) ℂ :=
  fun l j => ∏ r, hW r (l r) (j r)

def diagLayer {N : ℕ} (vW : Fin N → EdgeW 2) : Matrix (Config 2 N) (Config 2 N) ℂ :=
  fun l j => if l = j then bondProd vW j else 0

theorem emLayer_eq_sqLayer_mul_diagLayer {N : ℕ} (hW vW : Fin N → EdgeW 2) :
    emLayer (fun (_ : Fin 1) => hW) (fun (_ : Fin 1) => vW) 0
      = sqLayer hW * diagLayer vW := by
  ext l j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j]
  · simp [emLayer, sqLayer, diagLayer]
  · intro k _ hk
    simp [diagLayer, hk]
  · intro hj
    simp at hj

def hadamardWeight : EdgeW 2 := fun i j => if i = 1 ∧ j = 1 then -1 else 1

def cpWeight : EdgeW 2 := fun i j => if i = 1 ∧ j = 1 then -1 else 1

def gateI1 : Matrix (Fin 2) (Fin 2) ℂ := 1

def gateH : Matrix (Fin 2) (Fin 2) ℂ := ((Real.sqrt 2)⁻¹ : ℂ) • singleQubitGate hadamardWeight

def gateP : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 0, Complex.exp ((Real.pi / 8 : ℝ) * Complex.I)]

def gateI2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1

def gateCP : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := diagTwoQubitGate cpWeight

theorem gateI1_apply (i j : Fin 2) :
    gateI1 i j = if i = j then 1 else 0 := Matrix.one_apply

theorem gateH_apply (i j : Fin 2) :
    gateH i j = ((Real.sqrt 2)⁻¹ : ℂ) * hadamardWeight i j := by
  simp [gateH, singleQubitGate, Matrix.smul_apply]

theorem gateP_apply (i j : Fin 2) :
    gateP i j = if i = j then (if i = 0 then 1 else Complex.exp ((Real.pi / 8 : ℝ) * Complex.I))
      else 0 := by
  fin_cases i <;> fin_cases j <;> simp [gateP]

theorem gateI2_apply (i j k l : Fin 2) :
    gateI2 (i, j) (k, l) = if i = k ∧ j = l then 1 else 0 := by
  simp [gateI2, Matrix.one_apply, Prod.mk.injEq]

theorem gateCP_apply (i j k l : Fin 2) :
    gateCP (i, j) (k, l) = if i = k ∧ j = l then cpWeight i j else 0 := rfl

theorem gateCP_diag (i j : Fin 2) :
    gateCP (i, j) (i, j) = if i = 1 ∧ j = 1 then -1 else 1 := by
  rw [gateCP_apply]
  simp [cpWeight]

theorem gateI1_eq_edgeGate :
    gateI1 = singleQubitGate (fun i j => if i = j then (1 : ℂ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gateI1, singleQubitGate]

theorem gateH_eq_edgeGate :
    gateH = singleQubitGate (fun i j => ((Real.sqrt 2)⁻¹ : ℂ) * hadamardWeight i j) := by
  ext i j
  exact gateH_apply i j

theorem gateP_eq_edgeGate :
    gateP = singleQubitGate (fun i j =>
      if i = j then (if i = 0 then 1 else Complex.exp ((Real.pi / 8 : ℝ) * Complex.I))
      else 0) := by
  ext i j
  exact gateP_apply i j

theorem gateI2_eq_edgeGate :
    gateI2 = diagTwoQubitGate (fun _ _ => (1 : ℂ)) := by
  ext x y
  obtain ⟨i, j⟩ := x
  obtain ⟨k, l⟩ := y
  simp [gateI2, diagTwoQubitGate, Matrix.one_apply, Prod.mk.injEq]

theorem gateCP_eq_edgeGate : gateCP = diagTwoQubitGate cpWeight := rfl

theorem universal_gate_set_isEdgeModel :
    (∃ w : EdgeW 2, gateI1 = singleQubitGate w) ∧
    (∃ w : EdgeW 2, gateH = singleQubitGate w) ∧
    (∃ w : EdgeW 2, gateP = singleQubitGate w) ∧
    (∃ v : EdgeW 2, gateI2 = diagTwoQubitGate v) ∧
    (∃ v : EdgeW 2, gateCP = diagTwoQubitGate v) :=
  ⟨⟨_, gateI1_eq_edgeGate⟩, ⟨_, gateH_eq_edgeGate⟩, ⟨_, gateP_eq_edgeGate⟩,
    ⟨_, gateI2_eq_edgeGate⟩, ⟨_, gateCP_eq_edgeGate⟩⟩

def allZeroConfig (N : ℕ) : Config 2 N := fun _ => 0

theorem isingType_amplitude_eq_partition {N M : ℕ}
    (hW vW : Fin M → Fin N → EdgeW 2) :
    matElem (emCircuit M hW vW) (allZeroConfig N) (allZeroConfig N) =
      emPartition0 M hW vW (allZeroConfig N) (allZeroConfig N) :=
  matElem_emCircuit_eq M hW vW _ _

def IsingAmplitudeForm : Prop :=
  ∀ (N M : ℕ) (hW vW : Fin M → Fin N → EdgeW 2) (L R : Config 2 N),
    ∃ (C : Matrix (Config 2 N) (Config 2 N) ℂ),
      matElem C L R = emPartition0 M hW vW L R

theorem ising_amplitude_form : IsingAmplitudeForm := by
  intro N M hW vW L R
  exact ⟨emCircuit M hW vW, matElem_emCircuit_eq M hW vW L R⟩

end Qatlib.Papers.SpinModels08.MainResults.EdgeModel.UniversalGateSet
