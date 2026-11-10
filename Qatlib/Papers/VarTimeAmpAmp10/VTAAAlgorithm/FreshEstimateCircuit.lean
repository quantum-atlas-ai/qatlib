/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HhlAlgorithms.Postselection.FreshTrials
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.ResourceDerivation
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.PrescribedEstimate
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.Postselection

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.HhlAlgorithms.Postselection.SignalProcessing
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical
variable {I : Type} [Fintype I] [DecidableEq I]

def vtExecutedGates (O : Matrix I I ℂ) (cs : Circuit I) : List (Matrix I I ℂ) :=
  cs.map fun s=>match s with | .query=>O | .gate U=>U

theorem vt_executed_gates_run (O : Matrix I I ℂ) (cs : Circuit I) (ψ : QState I) :
    Run 1 (Circuit.ofGates (vtExecutedGates O cs)) ψ=Run O cs ψ := by
  induction cs generalizing ψ with
  | nil=>rfl
  | cons s cs ih=>cases s <;> simpa [vtExecutedGates,Circuit.ofGates,Run] using ih _

def vtFreshGates (gs : List (Matrix I I ℂ)) :
    (n : ℕ) → List (Matrix (FreshRegister I n) (FreshRegister I n) ℂ)
  | 0=>[]
  | n+1=>gs.map (fun U=>TensorGate U 1) ++ (vtFreshGates gs n).map (fun U=>TensorGate 1 U)

omit [Fintype I] in

theorem vt_fresh_gates_length (gs : List (Matrix I I ℂ)) (n : ℕ) :
    (vtFreshGates gs n).length=n*gs.length := by
  induction n with
  | zero=>simp [vtFreshGates]
  | succ n ih=>simp [vtFreshGates,ih,Nat.succ_mul,Nat.add_comm]

private theorem run_left_gates {J : Type} [Fintype J] [DecidableEq J]
    (gs : List (Matrix I I ℂ)) (ψ : QState I) (χ : QState J) :
    Run 1 (Circuit.ofGates (gs.map fun U=>TensorGate U (1 : Matrix J J ℂ))) (TensorState ψ χ)=
      TensorState (Run 1 (Circuit.ofGates gs) ψ) χ := by
  induction gs generalizing ψ with
  | nil=>rfl
  | cons U gs ih=>simpa [Circuit.ofGates,Run,applyGate_tensorGate,applyGate_one] using ih (ApplyGate U ψ)

private theorem run_right_gates {J : Type} [Fintype J] [DecidableEq J]
    (gs : List (Matrix J J ℂ)) (ψ : QState I) (χ : QState J) :
    Run 1 (Circuit.ofGates (gs.map fun U=>TensorGate (1 : Matrix I I ℂ) U)) (TensorState ψ χ)=
      TensorState ψ (Run 1 (Circuit.ofGates gs) χ) := by
  induction gs generalizing χ with
  | nil=>rfl
  | cons U gs ih=>simpa [Circuit.ofGates,Run,applyGate_tensorGate,applyGate_one] using ih (ApplyGate U χ)

omit [Fintype I] [DecidableEq I] in

private theorem ofGates_append (gs hs : List (Matrix I I ℂ)) :
    Circuit.ofGates (gs++hs)=Circuit.ofGates gs++Circuit.ofGates hs := List.map_append

theorem vt_fresh_gates_run (gs : List (Matrix I I ℂ)) (ψ : QState I) (n : ℕ) :
    Run 1 (Circuit.ofGates (vtFreshGates gs n)) (freshState ψ n)=
      freshState (Run 1 (Circuit.ofGates gs) ψ) n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    change Run 1
        (Circuit.ofGates (gs.map (fun U=>TensorGate U 1) ++ (vtFreshGates gs n).map (fun U=>TensorGate 1 U))) (TensorState ψ (freshState ψ n)) = _
    rw [ofGates_append,run_append,run_left_gates,run_right_gates,ih]
    rfl

def vtFreshLabel {M : ℕ} : (n : ℕ) → FreshRegister (Fin M × (Bool × I)) n → Fin n → Fin M
  | 0,_=>Fin.elim0
  | n+1,p=>Fin.cons p.1.1 (vtFreshLabel n p.2)

theorem vt_fresh_label_marginal {M : ℕ} (ψ : QState (Fin M × (Bool × I))) (n : ℕ)
    (ω : Fin n → Fin M) :
    MeasureProb (freshState ψ n) (Finset.univ.filter (fun p=>vtFreshLabel n p=ω))=
      ∏ k,MeasureProb ψ (Finset.univ.filter (fun p=>p.1=ω k)) := by
  induction n with
  | zero=>
    have he : (Fin.elim0 : Fin 0 → Fin M)=ω := funext fun i=>Fin.elim0 i
    simp [freshState,vtFreshLabel,MeasureProb,bornProb_ket,he]
  | succ n ih=>
    have hfiber : (Finset.univ.filter (fun p : FreshRegister (Fin M × (Bool × I)) (n+1)=>vtFreshLabel (n+1) p=ω))=
        (Finset.univ.filter (fun p : Fin M × (Bool × I)=>p.1=ω 0)) ×ˢ
          (Finset.univ.filter (fun p : FreshRegister (Fin M × (Bool × I)) n=>vtFreshLabel n p=fun i=>ω i.succ)) := by
      ext p
      constructor
      · intro hp
        have he:=(Finset.mem_filter.mp hp).2
        apply Finset.mem_product.mpr
        exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrFun he 0⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,funext fun i=>congrFun he i.succ⟩⟩
      · intro hp
        obtain ⟨hp,ht⟩:=Finset.mem_product.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _,?_⟩
        funext i
        exact Fin.cases (Finset.mem_filter.mp hp).2
          (fun j=>congrFun (Finset.mem_filter.mp ht).2 j) i
    rw [hfiber,freshState,measureProb_tensorState_prod,Fin.prod_univ_succ,ih]

def vtFreshAECircuit (M : ℕ) (A : Matrix I I ℂ) (j : I) (S : Finset I) (n : ℕ) :
    Circuit (FreshRegister (Fin M × (Bool × I)) n) :=
  Circuit.ofGates (vtFreshGates (vtExecutedGates (aeControlledGate M (preparedMark S))
    (countedAECircuit M A j)) n)

def vtFreshAEInput (M : ℕ) (hM : 2 ≤ M) (j : I) (n : ℕ) :
    QState (FreshRegister (Fin M × (Bool × I)) n) :=
  freshState (TensorState (Ket (⟨0,by omega⟩ : Fin M)) (TensorState (Ket false) (Ket j))) n

theorem vt_fresh_ae_born_law (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) (n : ℕ) (ω : Fin n → Fin M) :
    (aeLaw M A j S hA hM).probOf ω=
      MeasureProb (Run 1 (vtFreshAECircuit M A j S n) (vtFreshAEInput M hM j n))
        (Finset.univ.filter (fun p=>vtFreshLabel n p=ω)) := by
  unfold vtFreshAECircuit vtFreshAEInput
  rw [vt_fresh_gates_run,vt_executed_gates_run,vt_fresh_label_marginal]
  rfl

theorem vt_fresh_ae_count (M : ℕ) (hM : 2 ≤ M) (A : Matrix I I ℂ)
    (hA : A∈Matrix.unitaryGroup I ℂ) (j : I) (S : Finset I) (n : ℕ) :
    QueryCount (vtFreshAECircuit M A j S n)+GateCount (vtFreshAECircuit M A j S n)=n*(6*M-3) := by
  have hcount:=(vt_prescribed_estimate_circuit_and_count M hM A hA j S).2
  have hlen : (countedAECircuit M A j).length=6*M-3 := by
    have he:=size_eq_gateCount_add_queryCount (countedAECircuit M A j)
    change (countedAECircuit M A j).length=GateCount _+QueryCount _ at he
    omega
  simp only [vtFreshAECircuit,Circuit.queryCount_ofGates,Circuit.gateCount_ofGates,
    vt_fresh_gates_length,vtExecutedGates,List.length_map,_root_.zero_add,hlen]
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
