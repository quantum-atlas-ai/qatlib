/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
variable {H : Type*} [Fintype H] [DecidableEq H]

noncomputable def controlOracle (U : Matrix H H ℂ) : Matrix (Bool × H) (Bool × H) ℂ :=
  select (fun b : Bool => if b then U else 1)

theorem controlOracle_mul (U V : Matrix H H ℂ) :
    controlOracle U * controlOracle V = controlOracle (U * V) := by
  rw [controlOracle, controlOracle, parallel_select_mul]
  congr 1
  funext b
  cases b <;> simp

omit [Fintype H] in

@[simp] theorem controlOracle_one : controlOracle (1 : Matrix H H ℂ) = 1 := by
  simpa only [controlOracle, ite_self] using (parallel_select_one (J := Bool) (H := H))

omit [Fintype H] in

theorem controlOracle_adjoint (U : Matrix H H ℂ) :
    (controlOracle U)ᴴ = controlOracle Uᴴ := by
  rw [controlOracle, parallel_select_adjoint]
  congr 1
  funext b
  cases b <;> simp

theorem controlOracle_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    controlOracle U ∈ Matrix.unitaryGroup (Bool × H) ℂ := by
  apply select_unitary
  intro b
  cases b
  · simp
  · simpa using hU

noncomputable def controlStep : AdjointStep H → AdjointStep (Bool × H)
  | .gate V => .gate (controlOracle V)
  | .forward => .forward
  | .backward => .backward

noncomputable def compileControlled (cs : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) := cs.map controlStep

theorem evaluate_compileControlled (U : Matrix H H ℂ) (cs : List (AdjointStep H)) :
    evaluate (controlOracle U) (compileControlled cs) = controlOracle (evaluate U cs) := by
  induction cs with
  | nil => simp [compileControlled, evaluate]
  | cons c cs ih =>
    change instructionMatrix (controlOracle U) (controlStep c) *
      evaluate (controlOracle U) (compileControlled cs) =
        controlOracle (instructionMatrix U c * evaluate U cs)
    rw [ih]
    cases c <;> simp [instructionMatrix, controlStep, controlOracle_adjoint, controlOracle_mul]

omit [Fintype H] in

@[simp] theorem queryCount_compileControlled (cs : List (AdjointStep H)) :
    adjointQueryCount (compileControlled cs) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change adjointQueryCount (controlStep c :: compileControlled cs) = adjointQueryCount (c :: cs)
    cases c <;> simp [controlStep, adjointQueryCount, ih]

omit [Fintype H] in

@[simp] theorem gateCount_compileControlled (cs : List (AdjointStep H)) :
    adjointGateCount (compileControlled cs) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change adjointGateCount (controlStep c :: compileControlled cs) = adjointGateCount (c :: cs)
    cases c <;> simp [controlStep, adjointGateCount, ih]

noncomputable def controlFlip : Matrix (Bool × H) (Bool × H) ℂ :=
  Matrix.of fun p q => if p.1 = !q.1 then (1 : Matrix H H ℂ) p.2 q.2 else 0

theorem controlFlip_select (V : Bool → Matrix H H ℂ) :
    controlFlip * select V * controlFlip = select (fun b => V (!b)) := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;>
    simp [controlFlip, select, Matrix.mul_apply, Fintype.sum_prod_type,
      Matrix.one_apply, mul_ite, ite_mul]

omit [Fintype H] in

@[simp] theorem controlFlip_adjoint : (controlFlip (H := H))ᴴ = controlFlip := by
  ext ⟨b, i⟩ ⟨c, j⟩
  cases b <;> cases c <;> simp [controlFlip, Matrix.conjTranspose_apply, Matrix.one_apply,
    eq_comm]

theorem controlFlip_mul_self : controlFlip (H := H) * controlFlip = 1 := by
  have h := controlFlip_select (fun _ : Bool => (1 : Matrix H H ℂ))
  simpa only [parallel_select_one, Matrix.mul_one] using h

theorem controlFlip_unitary : controlFlip (H := H) ∈ Matrix.unitaryGroup (Bool × H) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    controlFlip_adjoint, controlFlip_mul_self]

private theorem controlled_select_product (U V : Matrix H H ℂ) :
    controlOracle U * controlFlip * controlOracle V * controlFlip =
      select (fun b : Bool => if b then U else V) := by
  calc
    _ = controlOracle U * (controlFlip * controlOracle V * controlFlip) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by
      simp only [controlOracle]
      rw [controlFlip_select, parallel_select_mul]
      congr 1
      funext b
      cases b <;> simp

noncomputable def compileSelected (csTrue csFalse : List (AdjointStep H)) :
    List (AdjointStep (Bool × H)) :=
  compileControlled csTrue ++ [.gate controlFlip] ++ compileControlled csFalse ++ [.gate controlFlip]

theorem evaluate_compileSelected (U : Matrix H H ℂ) (csTrue csFalse : List (AdjointStep H)) :
    evaluate (controlOracle U) (compileSelected csTrue csFalse) =
      select (fun b : Bool => if b then evaluate U csTrue else evaluate U csFalse) := by
  simp only [compileSelected, evaluate_append, evaluate_compileControlled, evaluate,
    instructionMatrix, Matrix.mul_one]
  exact controlled_select_product _ _

omit [Fintype H] in

theorem queryCount_compileSelected (csTrue csFalse : List (AdjointStep H)) :
    adjointQueryCount (compileSelected csTrue csFalse) =
      adjointQueryCount csTrue + adjointQueryCount csFalse := by
  simp [compileSelected, adjointQueryCount]

omit [Fintype H] in

theorem gateCount_compileSelected (csTrue csFalse : List (AdjointStep H)) :
    adjointGateCount (compileSelected csTrue csFalse) =
      adjointGateCount csTrue + adjointGateCount csFalse + 2 := by
  simp only [compileSelected, adjointGateCount_append, gateCount_compileControlled,
      adjointGateCount]
  omega

def controlSpectatorEquiv (J H : Type*) : Bool × (J × H) ≃ J × (Bool × H) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

omit [Fintype H] in

theorem controlOracle_parallelOracle {J : Type*} [DecidableEq J]
    (U : Matrix H H ℂ) :
    controlOracle (parallelOracle (J := J) U) =
      (parallelOracle (J := J) (controlOracle U)).submatrix
        (controlSpectatorEquiv J H) (controlSpectatorEquiv J H) := by
  ext ⟨b, l, i⟩ ⟨c, m, j⟩
  by_cases hl : l = m <;> by_cases hi : i = j <;> cases b <;> cases c <;>
    simp [controlOracle, parallelOracle, select, Matrix.submatrix_apply,
      controlSpectatorEquiv, hl, hi]

theorem compileControlled_wellFormed {cs : List (AdjointStep H)}
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (compileControlled cs) := by
  unfold compileControlled
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons c cs ih =>
    cases c <;> simp only [List.map_cons, controlStep,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.forward_cons_iff,
      WellFormedAdjointCircuit.backward_cons_iff] at hcs ⊢
    · exact ⟨controlOracle_unitary hcs.1, ih hcs.2⟩
    · exact ih hcs
    · exact ih hcs

theorem compileSelected_wellFormed {csTrue csFalse : List (AdjointStep H)}
    (hTrue : WellFormedAdjointCircuit csTrue) (hFalse : WellFormedAdjointCircuit csFalse) :
    WellFormedAdjointCircuit (compileSelected csTrue csFalse) := by
  have hx : WellFormedAdjointCircuit ([.gate controlFlip] : List (AdjointStep (Bool × H))) := by
    simpa only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
      using controlFlip_unitary (H := H)
  exact (((compileControlled_wellFormed hTrue).append hx).append
    (compileControlled_wellFormed hFalse)).append hx

end Qatlib.Concepts.LocalMachine.LocalTransport
