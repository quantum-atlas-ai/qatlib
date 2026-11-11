/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBornBridge

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Resource Accounting

Resource Accounting constructions and identities for Spinor Sampling.
-/

open Qatlib.Concepts.SpinorSampling.Model Qatlib.Concepts.SpinorSampling.NativeRecords

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

set_option autoImplicit false
namespace Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources
open ShiftCircuit NativeBridge Qatlib

/-- Construction for control Cost in the resource accounting model. -/
def controlCost (k : ℕ) : ℕ := if k=1 then 1 else 15*(2*k-3)

/-- Construction for increment Cost in the resource accounting model. -/
def incrementCost (p r : ℕ) : ℕ :=
  match r with
  | 0 => 0
  | r+1 => incrementCost (p+1) r+controlCost p
termination_by r

/-- Complete original `native_reverse_length` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem native_reverse_length {n : ℕ} (gs : List (BitGate (Fin n))) :
    (nativeWord gs.reverse).length=(nativeWord gs).length := by
  simp only [nativeWord, List.length_flatMap, List.map_reverse, List.sum_reverse]

/-- Complete original `increment_aux_native_length` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem increment_aux_native_length {n : ℕ} (lower axis ws : List (Fin n))
    (hpos : 0 < lower.length) (hsize : lower.length+axis.length ≤ ws.length+3) :
    (nativeWord (incrementAux lower axis ws)).length=incrementCost lower.length axis.length := by
  induction axis generalizing lower with
  | nil => simp [incrementAux, nativeWord, incrementCost]
  | cons a rest ih =>
    have ht := ih (lower++[a]) (by simp only [List.length_append, List.length_singleton]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil] at hsize ⊢; omega)
    rw [incrementAux]
    simp only [nativeWord, List.flatMap_append, List.length_append]
    change (nativeWord (incrementAux (lower++[a]) rest ws)).length+
      (nativeWord (multiX lower a ws)).length=incrementCost lower.length (a::rest).length
    rw [ht, native_multiX_gate_count lower a ws hpos (by
      simp only [List.length_cons] at hsize; omega)]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, incrementCost, controlCost]

/-- Complete original `control_cost_ge_two` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem control_cost_ge_two (q : ℕ) : controlCost (q+2)=15*(2*q+1) := by
  rw [controlCost, ite_eq_right (by omega)]
  congr 1

/-- Complete original `increment_cost_ge_two` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem increment_cost_ge_two (q r : ℕ) : incrementCost (q+2) r=15*(r*(2*q+r)) := by
  induction r generalizing q with
  | zero => simp [incrementCost]
  | succ r ih =>
    rw [incrementCost]
    rw [show q+2+1=(q+1)+2 by omega, ih, control_cost_ge_two]
    ring

/-- Complete original `increment_cost_one` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem increment_cost_one (r : ℕ) :
    incrementCost 1 r=if r=0 then 0 else 15*(r-1)^2+1 := by
  cases r with
  | zero => simp [incrementCost]
  | succ r =>
    rw [incrementCost]
    rw [show 1+1=0+2 from rfl, increment_cost_ge_two]
    simp [controlCost, pow_two]

/-- Complete original `spatial_native_length` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem spatial_native_length (d r : ℕ) (j : Fin d) :
    (nativeWord (spatialIncrementWord d r j)).length=if r=0 then 0 else 15*(r-1)^2+1 := by
  unfold spatialIncrementWord incrementWord
  rw [increment_aux_native_length [testWire d r] (axisWires d r j) (workWires d r) (by simp) (by
    simp only [List.length_cons, List.length_nil, axisWires, workWires, List.length_ofFn]
    omega)]
  simpa only [List.length_cons, List.length_nil, axisWires, List.length_ofFn] using increment_cost_one r

/-- Construction for velocity Record Gates in the resource accounting model. -/
def velocityRecordGates (r : ℕ) : ℕ := (if r=0 then 0 else 15*(r-1)^2+1)+3

/-- Complete original `velocity_word_length` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem velocity_word_length (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    (velocityWord d r j positiveNeighbor).length=velocityRecordGates r := by
  cases positiveNeighbor <;>
    simp only [velocityWord, velocityRecordGates, Bool.false_eq_true, ite_false, ite_true,
      List.length_append, List.length_cons, List.length_nil, List.length_map,
      native_reverse_length, spatial_native_length] <;> omega

/-- Complete original `velocity_gate_count` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem velocity_gate_count (d r : ℕ) (j : Fin d) (positiveNeighbor : Bool) :
    GateCount (velocityProgram d r j positiveNeighbor)=velocityRecordGates r :=
  (velocity_program_counts d r j positiveNeighbor).2.trans (velocity_word_length d r j positiveNeighbor)

/-- Complete original `spin_word_length` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem spin_word_length (d r : ℕ) (p : Fin 3) :
    (spinWord d r p).length=if p=0 then 1 else if p=1 then 2 else 0 := by
  fin_cases p <;> simp [spinWord]

/-- Complete original `spin_gate_count` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem spin_gate_count (d r : ℕ) (p : Fin 3) :
    GateCount (spinProgram d r p)=if p=0 then 1 else if p=1 then 2 else 0 :=
  (spin_program_counts d r p).2.trans (spin_word_length d r p)

/-- Complete original `computable_double_shift_eq` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem computable_double_shift_eq (d r : ℕ) (j : Fin d) :
    (decodedNeighbor d r j).trans (decodedNeighbor d r j)=periodicDoubleShift d (2^r) j := by
  rw [decoded_neighbor_eq_original, periodic_unit_shift_square]

/-- Construction for velocity Copies in the resource accounting model. -/
def velocityCopies (d : ℕ) (p : SamplePlanQ) : ℕ := d*p.velocityRecords*p.velocityBlocks
/-- Construction for spin Copies in the resource accounting model. -/
def spinCopies (d : ℕ) (p : SamplePlanQ) : ℕ := 3*d*p.spinRecords*p.spinBlocks
/-- Construction for native Gate Budget in the resource accounting model. -/
def nativeGateBudget (d r : ℕ) (p : SamplePlanQ) : ℕ :=
  velocityCopies d p*velocityRecordGates r+spinCopies d p
/-- Construction for readout Budget in the resource accounting model. -/
def readoutBudget (d r : ℕ) (p : SamplePlanQ) : ℕ :=
  velocityCopies d p*registerWidth d r+spinCopies d p*(d*r+1)

/-- Complete original `sample_plan_copy_fields` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem sample_plan_copy_fields (d r : ℕ) (α β bound γ η δ : ℚ) :
    let p := samplePlanQ d r α β bound γ η δ
    p.copies=velocityCopies d p+spinCopies d p ∧
      p.targetQueries=velocityCopies d p ∧ p.controlledShifts=velocityCopies d p := by
  by_cases hγ : γ=0 <;> simp [samplePlanQ, hγ, velocityCopies, spinCopies]

open scoped BigOperators
noncomputable section

/-- Construction for scheduled Native Gates in the resource accounting model. -/
def scheduledNativeGates (d r : ℕ) (p : SamplePlanQ)
    (R : Fin d → Fin p.velocityBlocks → Fin p.velocityRecords → Bool) : ℕ :=
  (∑ j : Fin d, ∑ k : Fin p.velocityBlocks, ∑ i : Fin p.velocityRecords,
    GateCount (velocityProgram d r j (R j k i)))+
  (∑ a : Fin 3, ∑ _j : Fin d, ∑ _k : Fin p.spinBlocks, ∑ _i : Fin p.spinRecords,
    GateCount (spinProgram d r a))

/-- Complete original `scheduled_native_gates_eq` guarantee for `ResourceAccounting`; all source hypotheses and output obligations are retained. -/
theorem scheduled_native_gates_eq (d r : ℕ) (p : SamplePlanQ)
    (R : Fin d → Fin p.velocityBlocks → Fin p.velocityRecords → Bool) :
    scheduledNativeGates d r p R=nativeGateBudget d r p := by
  simp only [scheduledNativeGates, velocity_gate_count, spin_gate_count]
  simp [Fin.sum_univ_succ, nativeGateBudget, velocityCopies, spinCopies]
  ring

end

end Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources


#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.native_reverse_length
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.increment_aux_native_length
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.control_cost_ge_two
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.increment_cost_ge_two
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.increment_cost_one
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.spatial_native_length
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.velocity_word_length
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.velocity_gate_count
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.spin_word_length
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.spin_gate_count
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.computable_double_shift_eq
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.sample_plan_copy_fields
#print axioms Qatlib.Concepts.SpinorSampling.FiniteExecution.Resources.scheduled_native_gates_eq
