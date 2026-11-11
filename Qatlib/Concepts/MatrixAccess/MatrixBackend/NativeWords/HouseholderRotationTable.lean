/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation

open Qatlib.Concepts.BlockEncoding.LCU

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Concepts.QspSimulation.Achievability
/-! The actual supplied Givens table, in the Householder emitter's order.
This is the logical label operator and exact rational axis; arbitrary-width
physical multi-control and work-register transport remain separate. -/
set_option autoImplicit false
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Construction for table Axis Step in the householder rotation table model. -/
def tableAxisStep {n : ℕ} (r : Fin n × Circle) (q : Option (Fin n) → ℚ) : Option (Fin n) → ℚ
  | none => r.2.c*q none-r.2.s*q (some r.1)
  | some i => if i=r.1 then r.2.s*q none+r.2.c*q (some r.1) else q (some i)

/-- Tail first: the supplied table is traversed in reverse physical order. -/
def tableAxis {n : ℕ} : List (Fin n × Circle) → Option (Fin n) → ℚ
  | [] => fun a => match a with | none => 1 | some _ => 0
  | r::rs => tableAxisStep r (tableAxis rs)

/-- Construction for table Prepared Column in the householder rotation table model. -/
def tablePreparedColumn {n : ℕ} (rs : List (Fin n × Circle)) (a : Option (Fin n)) : ℚ :=
  2*tableAxis rs a*tableAxis rs none-(if a=none then 1 else 0)

noncomputable section
open scoped Classical

/-- Construction for table Axis Complex in the householder rotation table model. -/
def tableAxisComplex {n : ℕ} (rs : List (Fin n × Circle)) : QState (Option (Fin n)) :=
  fun a => (tableAxis rs a : ℂ)

/-- Matrix-product order is the supplied order, hence physical order is reversed. -/
def tableGivensWord {n : ℕ} (rs : List (Fin n × Circle)) : List (AdjointStep (Option (Fin n))) :=
  rs.map (fun r => .gate (weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ)))

/-- Construction for table Givens in the householder rotation table model. -/
def tableGivens {n : ℕ} (rs : List (Fin n × Circle)) : Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
  evaluate 1 (tableGivensWord rs)

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem table_rotation_unitary {n : ℕ} (r : Fin n × Circle) :
    weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ) ∈ unitaryGroup (Option (Fin n)) ℂ := by
  have hq : r.2.c^2+r.2.s^2=1 := by simpa only [pow_two] using r.2.norm
  have hr : (r.2.c : ℝ)^2+(r.2.s : ℝ)^2=1 := by exact_mod_cast hq
  simpa only [Complex.ofReal_ratCast] using weightTwoLevel_unitary r.1 (r.2.c : ℝ) (r.2.s : ℝ) hr

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem tableGivensWord_legal {n : ℕ} (rs : List (Fin n × Circle)) :
    WellFormedAdjointCircuit (tableGivensWord rs) := by
  induction rs with
  | nil => exact Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil
  | cons r rs ih =>
    exact (Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff _ _).2 ⟨table_rotation_unitary r, ih⟩

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem tableGivens_unitary {n : ℕ} (rs : List (Fin n × Circle)) :
    tableGivens rs ∈ unitaryGroup (Option (Fin n)) ℂ :=
  (tableGivensWord_legal rs).evaluate_unitary (unitaryGroup _ ℂ).one_mem

/-- Casting the concrete rational data preserves the stated complex-vector identity. -/
theorem tableAxisStep_cast {n : ℕ} (r : Fin n × Circle) (q : Option (Fin n) → ℚ) :
    (fun a => (tableAxisStep r q a : ℂ)) =
      weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ) *ᵥ (fun a => (q a : ℂ)) := by
  funext a
  rw [weightTwoLevel_mulVec]
  cases a with
  | none => simp [tableAxisStep]
  | some i =>
    by_cases hi : i=r.1
    · simp [tableAxisStep, hi]
    · simp [tableAxisStep, hi]

/-- Casting the concrete rational data preserves the stated complex-vector identity. -/
theorem tableAxis_cast {n : ℕ} (rs : List (Fin n × Circle)) :
    tableAxisComplex rs = tableGivens rs *ᵥ Qatlib.Foundations.PureStateMath.Ket none := by
  induction rs with
  | nil =>
    funext a
    cases a <;> simp [tableAxisComplex, tableAxis, tableGivens, tableGivensWord,
      evaluate, Qatlib.Foundations.PureStateMath.Ket]
  | cons r rs ih =>
    change (fun a => (tableAxisStep r (tableAxis rs) a : ℂ)) = _
    rw [tableAxisStep_cast]
    change weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ) *ᵥ tableAxisComplex rs = _
    rw [ih]
    simp only [tableGivens, tableGivensWord, List.map_cons, evaluate, instructionMatrix,
      Matrix.mulVec_mulVec]

/-- The concrete rational or complex data satisfy the displayed normalization identity. -/
theorem tableAxis_normalized {n : ℕ} (rs : List (Fin n × Circle)) :
    Normalized (tableAxisComplex rs) := by
  rw [tableAxis_cast]
  exact normalized_applyGate (tableGivens_unitary rs) (normalized_ket none)

/-- The concrete rational or complex data satisfy the displayed normalization identity. -/
theorem tableAxis_sum_sq {n : ℕ} (rs : List (Fin n × Circle)) :
    (∑ a, (tableAxis rs a)^2) = 1 := by
  have h := inner_self_eq_one (tableAxis_normalized rs)
  have hc : (∑ a, (tableAxis rs a : ℂ)^2) = 1 := by
    simpa [Qatlib.Foundations.PureStateMath.Inner, dotProduct, tableAxisComplex, pow_two] using h
  exact_mod_cast hc

/-- Construction for table Householder in the householder rotation table model. -/
def tableHouseholder {n : ℕ} (rs : List (Fin n × Circle)) :
    Matrix (Option (Fin n)) (Option (Fin n)) ℂ :=
  ReflectionAbout (outerProduct (tableAxisComplex rs))

/-- The constructed finite matrix is unitary under the stated hypotheses. -/
theorem tableHouseholder_unitary {n : ℕ} (rs : List (Fin n × Circle)) :
    tableHouseholder rs ∈ unitaryGroup (Option (Fin n)) ℂ :=
  outerProduct_reflection_unitary (tableAxis_normalized rs)

/-- This is the V / origin-reflection / true V-adjoint of the actual table. -/
theorem tableHouseholder_conjugation {n : ℕ} (rs : List (Fin n × Circle)) :
    tableGivens rs * ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (none : Option (Fin n)))) * (tableGivens rs)ᴴ =
      tableHouseholder rs := by
  have hVV : tableGivens rs*(tableGivens rs)ᴴ=1 := by
    simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose] using tableGivens_unitary rs
  unfold tableHouseholder ReflectionAbout
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hVV,
    Qatlib.Concepts.LcuPostselect.ScaledLCU.LCUFixedPoint.outerProduct_conj, ← tableAxis_cast]

/-- The concrete matrix entries have the displayed exact coordinate formula. -/
theorem tableHouseholder_entry {n : ℕ} (rs : List (Fin n × Circle)) (a b : Option (Fin n)) :
    tableHouseholder rs a b =
      ((2*tableAxis rs a*tableAxis rs b : ℚ) : ℂ)-(if a=b then 1 else 0) := by
  simp [tableHouseholder, ReflectionAbout, outerProduct, tableAxisComplex,
    Matrix.one_apply, smul_eq_mul, mul_assoc]

/-- The actual matrix or program has the displayed value on its origin column. -/
theorem tableHouseholder_origin_column {n : ℕ} (rs : List (Fin n × Circle)) (a : Option (Fin n)) :
    tableHouseholder rs a none = (tablePreparedColumn rs a : ℂ) := by
  rw [tableHouseholder_entry]
  by_cases ha : a=none <;> simp [tablePreparedColumn, ha]

/-- The explicit unselected-address or padding condition gives the stated coordinate behaviour. -/
theorem tableAxis_zero_outside {n : ℕ} (rs : List (Fin n × Circle)) (i : Fin n)
    (hi : ∀ r ∈ rs, r.1 ≠ i) : tableAxis rs (some i) = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hri : i ≠ r.1 := Ne.symm (hi r (by simp))
    simpa [tableAxis, tableAxisStep, hri] using ih (fun r hr => hi r (by simp [hr]))

/-- Unvisited labels are not prepared from the origin, exactly. -/
theorem tablePreparedColumn_zero_outside {n : ℕ} (rs : List (Fin n × Circle)) (i : Fin n)
    (hi : ∀ r ∈ rs, r.1 ≠ i) : tablePreparedColumn rs (some i) = 0 := by
  simp [tablePreparedColumn, tableAxis_zero_outside rs i hi]

/-- On a padded input column the entire PREP is minus identity, not zero. -/
theorem tableHouseholder_padding_column {n : ℕ} (rs : List (Fin n × Circle)) (i : Fin n)
    (hi : ∀ r ∈ rs, r.1 ≠ i) (a : Option (Fin n)) :
    tableHouseholder rs a (some i) = -(1 : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) a (some i) := by
  rw [tableHouseholder_entry, tableAxis_zero_outside rs i hi]
  simp [Matrix.one_apply]

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem tableGivensWord_evaluate {n : ℕ} (rs : List (Fin n × Circle))
    (O : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) :
    evaluate O (tableGivensWord rs) = tableGivens rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simpa only [tableGivensWord, List.map_cons, evaluate, instructionMatrix, tableGivens] using
      congrArg (fun T => weightTwoLevel r.1 (r.2.c : ℂ) (r.2.s : ℂ)*T) ih

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem tableGivensWord_counts {n : ℕ} (rs : List (Fin n × Circle)) :
    adjointQueryCount (tableGivensWord rs) = 0 ∧
    adjointGateCount (tableGivensWord rs) = rs.length := by
  induction rs with
  | nil => simp [tableGivensWord, adjointQueryCount, adjointGateCount]
  | cons r rs ih =>
    simpa [tableGivensWord, adjointQueryCount, adjointGateCount] using ih

/-- Exact ordered logical PREP, retaining the supplied rotations and true adjoint. -/
def tableHouseholderWord {n : ℕ} (rs : List (Fin n × Circle)) : List (AdjointStep (Option (Fin n))) :=
  tableGivensWord rs ++ [.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (none : Option (Fin n)))))] ++
    adjointCircuit (tableGivensWord rs)

/-- Evaluation of the emitted native word equals the stated concrete matrix semantics. -/
theorem tableHouseholderWord_evaluate {n : ℕ} (rs : List (Fin n × Circle))
    (O : Matrix (Option (Fin n)) (Option (Fin n)) ℂ) :
    evaluate O (tableHouseholderWord rs) = tableHouseholder rs := by
  simp only [tableHouseholderWord, evaluate_append, evaluate_adjointCircuit, tableGivensWord_evaluate,
    evaluate, instructionMatrix, Matrix.mul_one]
  exact tableHouseholder_conjugation rs

/-- The same emitted program has the displayed exact query and elementary-gate counts. -/
theorem tableHouseholderWord_counts {n : ℕ} (rs : List (Fin n × Circle)) :
    adjointQueryCount (tableHouseholderWord rs) = 0 ∧
    adjointGateCount (tableHouseholderWord rs) = 2*rs.length+1 := by
  have hc := tableGivensWord_counts rs
  constructor
  · simp [tableHouseholderWord, adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, hc.1, adjointQueryCount]
  · simp only [tableHouseholderWord, adjointGateCount_append,
      adjointGateCount_adjointCircuit, hc.2, adjointGateCount]
    omega

/-- The emitted native program is legal under the displayed input and wire conditions. -/
theorem tableHouseholderWord_legal {n : ℕ} (rs : List (Fin n × Circle)) :
    WellFormedAdjointCircuit (tableHouseholderWord rs) := by
  have hv := tableGivensWord_legal rs
  have hm : WellFormedAdjointCircuit
      [.gate (ReflectionAbout (outerProduct (Qatlib.Foundations.PureStateMath.Ket (none : Option (Fin n)))))] := by
    simpa only [Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.gate_cons_iff, Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit.nil, and_true]
      using outerProduct_reflection_unitary (normalized_ket (none : Option (Fin n)))
  exact (hv.append hm).append hv.adjointCircuit

end
end Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
