/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.OperatorAccess.EncodedAccess.RectangularTagFilter
public import Qatlib.Concepts.QueryWordCore.AdjointCircuits
public import Qatlib.Concepts.BlockEncoding.Postselection

@[expose] public section
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.OperatorAccess.EncodedAccess Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.MatrixAccess.CircuitPipeline

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {I M O J K : Type} [Fintype I] [DecidableEq I] [Fintype M] [DecidableEq M]
  [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]

noncomputable def rectLiftStepLeft (s : AdjointStep (J × RectangularData I M O)) :
    AdjointStep (RectangularWorkspace I M O J K) :=
  match s with
  | .gate G => .gate (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftLeft G))
  | .forward => .forward
  | .backward => .backward

noncomputable def rectLiftStepRight (s : AdjointStep (K × RectangularData I M O)) :
    AdjointStep (RectangularWorkspace I M O J K) :=
  match s with
  | .gate G => .gate (TensorGate (1 : Matrix Bool Bool ℂ) (independentLiftRight G))
  | .forward => .forward
  | .backward => .backward

noncomputable def rectLiftLeftCircuit (C : List (AdjointStep (J × RectangularData I M O))) :
    List (AdjointStep (RectangularWorkspace I M O J K)) := C.map rectLiftStepLeft

noncomputable def rectLiftRightCircuit (C : List (AdjointStep (K × RectangularData I M O))) :
    List (AdjointStep (RectangularWorkspace I M O J K)) := C.map rectLiftStepRight

noncomputable def rectProductCircuit (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O))) :
    List (AdjointStep (RectangularWorkspace I M O J K)) :=
  rectLiftRightCircuit C_B ++ [.gate (rectMiddleFilter (I := I) (M := M) (O := O))] ++
    rectLiftLeftCircuit C_A

/-- The independent left workspace lift preserves the identity matrix. -/
theorem independentLiftLeft_one :
    independentLiftLeft (K := K)
        (1 : Matrix (J × RectangularData I M O) (J × RectangularData I M O) ℂ) = 1 := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  simp only [independentLiftLeft, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : uj = wj <;> by_cases h2 : uk = wk <;> by_cases h3 : d = d' <;> simp [h1, h2, h3]

/-- The independent right workspace lift preserves the identity matrix. -/
theorem independentLiftRight_one :
    independentLiftRight (J := J)
        (1 : Matrix (K × RectangularData I M O) (K × RectangularData I M O) ℂ) = 1 := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  simp only [independentLiftRight, Matrix.of_apply, Matrix.one_apply]
  by_cases h1 : uj = wj <;> by_cases h2 : uk = wk <;> by_cases h3 : d = d' <;> simp [h1, h2, h3]

/-- Cyclically rotates three finite summations of a complex valued function. -/
theorem sum_rotate {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z] (F : X → Y → Z → ℂ) :
    (∑ x : X, ∑ y : Y, ∑ z : Z, F x y z) = ∑ y : Y, ∑ z : Z, ∑ x : X, F x y z := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_comm

/-- The independent left workspace lift preserves matrix multiplication. -/
theorem independentLiftLeft_mul (X Y : Matrix (J × RectangularData I M O)
    (J × RectangularData I M O) ℂ) :
    independentLiftLeft (K := K) (X * Y)
      = independentLiftLeft (K := K) X * independentLiftLeft (K := K) Y := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  have hL : (independentLiftLeft (K := K) (X * Y)) ((uj, uk), d) ((wj, wk), d') =
      (∑ z : J × RectangularData I M O, X (uj, d) z * Y z (wj, d')) *
        (if uk = wk then (1 : ℂ) else 0) := by
    simp only [independentLiftLeft, Matrix.of_apply]
    rw [show ((X * Y) (uj, d) (wj, d')) =
      ∑ z : J × RectangularData I M O, X (uj, d) z * Y z (wj, d') from rfl]
  have hR : (independentLiftLeft (K := K) X * independentLiftLeft (K := K) Y)
      ((uj, uk), d) ((wj, wk), d') =
      ∑ t : (J × K) × RectangularData I M O,
        (X (uj, d) (t.1.1, t.2) * (if uk = t.1.2 then (1 : ℂ) else 0)) *
          (Y (t.1.1, t.2) (wj, d') * (if t.1.2 = wk then (1 : ℂ) else 0)) := by
    rw [show (independentLiftLeft (K := K) X * independentLiftLeft (K := K) Y)
        ((uj, uk), d) ((wj, wk), d') =
      ∑ t : (J × K) × RectangularData I M O,
        independentLiftLeft (K := K) X ((uj, uk), d) t *
        independentLiftLeft (K := K) Y t ((wj, wk), d') from rfl]
    simp only [independentLiftLeft, Matrix.of_apply]
  rw [hL, hR]
  by_cases huk : uk = wk
  · subst huk
    rw [ite_eq_left (rfl : uk = uk), mul_one]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    (try dsimp only)
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_comm]
    have hsingle : ∀ (j : J) (dd : RectangularData I M O),
        (∑ k : K, (X (uj, d) (j, dd) * (if uk = k then (1 : ℂ) else 0)) *
            (Y (j, dd) (wj, d') * (if k = uk then (1 : ℂ) else 0))) =
          X (uj, d) (j, dd) * Y (j, dd) (wj, d') := by
      intro j dd
      rw [Finset.sum_eq_single uk]
      · simp
      · intro b _ hb
        rw [ite_eq_right (Ne.symm hb), mul_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ uk) h
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun dd _ => hsingle j dd]
  · rw [ite_eq_right huk, mul_zero]
    rw [Finset.sum_eq_zero]
    intro t _
    by_cases h1 : uk = t.1.2
    · have h2 : ¬(t.1.2 = wk) := fun h => huk (h1.trans h)
      simp [h1, h2]
    · simp [h1]

/-- The independent right workspace lift preserves matrix multiplication. -/
theorem independentLiftRight_mul (X Y : Matrix (K × RectangularData I M O)
    (K × RectangularData I M O) ℂ) :
    independentLiftRight (J := J) (X * Y)
      = independentLiftRight (J := J) X * independentLiftRight (J := J) Y := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  have hL : (independentLiftRight (J := J) (X * Y)) ((uj, uk), d) ((wj, wk), d') =
      (if uj = wj then (1 : ℂ) else 0) *
        (∑ z : K × RectangularData I M O, X (uk, d) z * Y z (wk, d')) := by
    simp only [independentLiftRight, Matrix.of_apply]
    rw [show ((X * Y) (uk, d) (wk, d')) =
      ∑ z : K × RectangularData I M O, X (uk, d) z * Y z (wk, d') from rfl]
  have hR : (independentLiftRight (J := J) X * independentLiftRight (J := J) Y)
      ((uj, uk), d) ((wj, wk), d') =
      ∑ t : (J × K) × RectangularData I M O,
        ((if uj = t.1.1 then (1 : ℂ) else 0) * X (uk, d) (t.1.2, t.2)) *
          ((if t.1.1 = wj then (1 : ℂ) else 0) * Y (t.1.2, t.2) (wk, d')) := by
    rw [show (independentLiftRight (J := J) X * independentLiftRight (J := J) Y)
        ((uj, uk), d) ((wj, wk), d') =
      ∑ t : (J × K) × RectangularData I M O,
        independentLiftRight (J := J) X ((uj, uk), d) t *
        independentLiftRight (J := J) Y t ((wj, wk), d') from rfl]
    simp only [independentLiftRight, Matrix.of_apply]
  rw [hL, hR]
  by_cases huj : uj = wj
  · subst huj
    rw [ite_eq_left rfl, one_mul]
    rw [Fintype.sum_prod_type, sum_aux_split, Fintype.sum_prod_type]
    (try dsimp only)
    rw [sum_rotate]
    have hsingle : ∀ (k : K) (dd : RectangularData I M O),
        (∑ j : J, ((if uj = j then (1 : ℂ) else 0) * X (uk, d) (k, dd)) *
            ((if j = uj then (1 : ℂ) else 0) * Y (k, dd) (wk, d'))) =
          X (uk, d) (k, dd) * Y (k, dd) (wk, d') := by
      intro k dd
      rw [Finset.sum_eq_single uj]
      · simp
      · intro b _ hb
        rw [ite_eq_right (Ne.symm hb), zero_mul, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ uj) h
    rw [Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun dd _ => hsingle k dd]
  · rw [ite_eq_right huj, zero_mul]
    rw [Finset.sum_eq_zero]
    intro t _
    by_cases h1 : uj = t.1.1
    · have h2 : ¬(t.1.1 = wj) := fun h => huj (h1.trans h)
      simp [h1, h2]
    · simp [h1]

/-- The left lift extends a data oracle to the combined independent workspace. -/
theorem independentLiftLeft_oracle (O_D : Matrix (RectangularData I M O)
    (RectangularData I M O) ℂ) :
    independentLiftLeft (TensorGate (1 : Matrix J J ℂ) O_D) =
      TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  simp only [independentLiftLeft, Matrix.of_apply, TensorGate, Matrix.kronecker_apply,
    Matrix.one_apply]
  by_cases h1 : uj = wj <;> by_cases h2 : uk = wk <;> simp [h1, h2]

/-- The right lift extends a data oracle to the combined independent workspace. -/
theorem independentLiftRight_oracle (O_D : Matrix (RectangularData I M O)
    (RectangularData I M O) ℂ) :
    independentLiftRight (TensorGate (1 : Matrix K K ℂ) O_D) =
      TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D := by
  ext u w
  obtain ⟨⟨uj, uk⟩, d⟩ := u
  obtain ⟨⟨wj, wk⟩, d'⟩ := w
  simp only [independentLiftRight, Matrix.of_apply, TensorGate, Matrix.kronecker_apply,
    Matrix.one_apply]
  by_cases h1 : uj = wj <;> by_cases h2 : uk = wk <;> simp [h1, h2]

/-- The left circuit lift sends the empty circuit to the empty circuit. -/
theorem rectLiftLeftCircuit_nil :
    rectLiftLeftCircuit ([] : List (AdjointStep (J × RectangularData I M O))) =
      ([] : List (AdjointStep (RectangularWorkspace I M O J K))) := rfl

/-- The left circuit lift maps the first step and recursively lifts the remaining circuit. -/
theorem rectLiftLeftCircuit_cons (s : AdjointStep (J × RectangularData I M O))
    (C : List (AdjointStep (J × RectangularData I M O))) :
    rectLiftLeftCircuit (s :: C) =
      (rectLiftStepLeft (K := K) s : AdjointStep (RectangularWorkspace I M O J K)) ::
        rectLiftLeftCircuit C := rfl

/-- The right circuit lift sends the empty circuit to the empty circuit. -/
theorem rectLiftRightCircuit_nil :
    rectLiftRightCircuit ([] : List (AdjointStep (K × RectangularData I M O))) =
      ([] : List (AdjointStep (RectangularWorkspace I M O J K))) := rfl

/-- The right circuit lift maps the first step and recursively lifts the remaining circuit. -/
theorem rectLiftRightCircuit_cons (s : AdjointStep (K × RectangularData I M O))
    (C : List (AdjointStep (K × RectangularData I M O))) :
    rectLiftRightCircuit (s :: C) =
      (rectLiftStepRight (J := J) s : AdjointStep (RectangularWorkspace I M O J K)) ::
        rectLiftRightCircuit C := rfl

/-- Evaluating the left lifted circuit equals the independent left lift of its evaluation,
tensored with the identity on the filter bit. -/
theorem evaluate_rectLiftLeftCircuit (O_D : Matrix (RectangularData I M O)
    (RectangularData I M O) ℂ) (C : List (AdjointStep (J × RectangularData I M O))) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectLiftLeftCircuit C) =
      TensorGate (1 : Matrix Bool Bool ℂ)
        (independentLiftLeft (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C)) := by
  induction C with
  | nil =>
    simp only [rectLiftLeftCircuit_nil, evaluate, independentLiftLeft_one, tensorGate_one]
  | cons s cs ih =>
    cases s with
    | gate G =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft, evaluate, instructionMatrix, ih]
      rw [tensorGate_mul, Matrix.one_mul, ← independentLiftLeft_mul]
    | forward =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft, evaluate, instructionMatrix, ih]
      rw [independentLiftLeft_mul, independentLiftLeft_oracle, tensorGate_mul,
        Matrix.one_mul]
    | backward =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft, evaluate, instructionMatrix, ih]
      rw [independentLiftLeft_mul,
        show (TensorGate (1 : Matrix J J ℂ) O_D)ᴴ =
            TensorGate (1 : Matrix J J ℂ) O_Dᴴ from by
          rw [tensorGate_conjTranspose, Matrix.conjTranspose_one],
        independentLiftLeft_oracle,
        show (TensorGate (1 : Matrix Bool Bool ℂ)
              (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D))ᴴ =
            TensorGate (1 : Matrix Bool Bool ℂ)
              (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_Dᴴ) from by
          rw [tensorGate_conjTranspose, Matrix.conjTranspose_one,
            tensorGate_conjTranspose, Matrix.conjTranspose_one],
        tensorGate_mul, Matrix.one_mul]

/-- Evaluating the right lifted circuit equals the independent right lift of its evaluation,
tensored with the identity on the filter bit. -/
theorem evaluate_rectLiftRightCircuit (O_D : Matrix (RectangularData I M O)
    (RectangularData I M O) ℂ) (C : List (AdjointStep (K × RectangularData I M O))) :
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectLiftRightCircuit C) =
      TensorGate (1 : Matrix Bool Bool ℂ)
        (independentLiftRight (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C)) := by
  induction C with
  | nil =>
    simp only [rectLiftRightCircuit_nil, evaluate, independentLiftRight_one, tensorGate_one]
  | cons s cs ih =>
    cases s with
    | gate G =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight, evaluate, instructionMatrix, ih]
      rw [tensorGate_mul, Matrix.one_mul, ← independentLiftRight_mul]
    | forward =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight, evaluate, instructionMatrix, ih]
      rw [independentLiftRight_mul, independentLiftRight_oracle, tensorGate_mul,
        Matrix.one_mul]
    | backward =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight, evaluate, instructionMatrix, ih]
      rw [independentLiftRight_mul,
        show (TensorGate (1 : Matrix K K ℂ) O_D)ᴴ =
            TensorGate (1 : Matrix K K ℂ) O_Dᴴ from by
          rw [tensorGate_conjTranspose, Matrix.conjTranspose_one],
        independentLiftRight_oracle,
        show (TensorGate (1 : Matrix Bool Bool ℂ)
              (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D))ᴴ =
            TensorGate (1 : Matrix Bool Bool ℂ)
              (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_Dᴴ) from by
          rw [tensorGate_conjTranspose, Matrix.conjTranspose_one,
            tensorGate_conjTranspose, Matrix.conjTranspose_one],
        tensorGate_mul, Matrix.one_mul]

/-- The left circuit lift preserves the adjoint query count. -/
theorem adjointQueryCount_rectLiftLeftCircuit (C : List (AdjointStep (J × RectangularData I M O))) :
    adjointQueryCount (rectLiftLeftCircuit (K := K) C) = adjointQueryCount C := by
  induction C with
  | nil => rfl
  | cons s cs ih =>
    rw [rectLiftLeftCircuit_cons]
    cases s with
    | gate G =>
      show adjointQueryCount (rectLiftLeftCircuit (K := K) cs) = adjointQueryCount cs
      exact ih
    | forward =>
      show adjointQueryCount (rectLiftLeftCircuit (K := K) cs) + 1 = adjointQueryCount cs + 1
      rw [ih]
    | backward =>
      show adjointQueryCount (rectLiftLeftCircuit (K := K) cs) + 1 = adjointQueryCount cs + 1
      rw [ih]

/-- The left circuit lift preserves the adjoint gate count. -/
theorem adjointGateCount_rectLiftLeftCircuit (C : List (AdjointStep (J × RectangularData I M O))) :
    adjointGateCount (rectLiftLeftCircuit (K := K) C) = adjointGateCount C := by
  induction C with
  | nil => rfl
  | cons s cs ih =>
    rw [rectLiftLeftCircuit_cons]
    cases s with
    | gate G =>
      show adjointGateCount (rectLiftLeftCircuit (K := K) cs) + 1 = adjointGateCount cs + 1
      rw [ih]
    | forward =>
      show adjointGateCount (rectLiftLeftCircuit (K := K) cs) = adjointGateCount cs
      exact ih
    | backward =>
      show adjointGateCount (rectLiftLeftCircuit (K := K) cs) = adjointGateCount cs
      exact ih

/-- The right circuit lift preserves the adjoint query count. -/
theorem adjointQueryCount_rectLiftRightCircuit
    (C : List (AdjointStep (K × RectangularData I M O))) :
    adjointQueryCount (rectLiftRightCircuit (J := J) C) = adjointQueryCount C := by
  induction C with
  | nil => rfl
  | cons s cs ih =>
    rw [rectLiftRightCircuit_cons]
    cases s with
    | gate G =>
      show adjointQueryCount (rectLiftRightCircuit (J := J) cs) = adjointQueryCount cs
      exact ih
    | forward =>
      show adjointQueryCount (rectLiftRightCircuit (J := J) cs) + 1 = adjointQueryCount cs + 1
      rw [ih]
    | backward =>
      show adjointQueryCount (rectLiftRightCircuit (J := J) cs) + 1 = adjointQueryCount cs + 1
      rw [ih]

/-- The right circuit lift preserves the adjoint gate count. -/
theorem adjointGateCount_rectLiftRightCircuit
    (C : List (AdjointStep (K × RectangularData I M O))) :
    adjointGateCount (rectLiftRightCircuit (J := J) C) = adjointGateCount C := by
  induction C with
  | nil => rfl
  | cons s cs ih =>
    rw [rectLiftRightCircuit_cons]
    cases s with
    | gate G =>
      show adjointGateCount (rectLiftRightCircuit (J := J) cs) + 1 = adjointGateCount cs + 1
      rw [ih]
    | forward =>
      show adjointGateCount (rectLiftRightCircuit (J := J) cs) = adjointGateCount cs
      exact ih
    | backward =>
      show adjointGateCount (rectLiftRightCircuit (J := J) cs) = adjointGateCount cs
      exact ih

/-- The left workspace lift preserves well formedness of an adjoint circuit. -/
theorem WellFormedAdjointCircuit.rectLiftLeft
    {C : List (AdjointStep (J × RectangularData I M O))} (hC : WellFormedAdjointCircuit C) :
    WellFormedAdjointCircuit (rectLiftLeftCircuit (K := K) C) := by
  induction C with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons s cs ih =>
    cases s with
    | gate G =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft,
        WellFormedAdjointCircuit.gate_cons_iff] at hC ⊢
      exact ⟨tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
        (independentLiftLeft_unitary hC.1), ih hC.2⟩
    | forward =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft,
        WellFormedAdjointCircuit.forward_cons_iff] at hC ⊢
      exact ih hC
    | backward =>
      simp only [rectLiftLeftCircuit_cons, rectLiftStepLeft,
        WellFormedAdjointCircuit.backward_cons_iff] at hC ⊢
      exact ih hC

/-- The right workspace lift preserves well formedness of an adjoint circuit. -/
theorem WellFormedAdjointCircuit.rectLiftRight
    {C : List (AdjointStep (K × RectangularData I M O))} (hC : WellFormedAdjointCircuit C) :
    WellFormedAdjointCircuit (rectLiftRightCircuit (J := J) C) := by
  induction C with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons s cs ih =>
    cases s with
    | gate G =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight,
        WellFormedAdjointCircuit.gate_cons_iff] at hC ⊢
      exact ⟨tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem
        (independentLiftRight_unitary hC.1), ih hC.2⟩
    | forward =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight,
        WellFormedAdjointCircuit.forward_cons_iff] at hC ⊢
      exact ih hC
    | backward =>
      simp only [rectLiftRightCircuit_cons, rectLiftStepRight,
        WellFormedAdjointCircuit.backward_cons_iff] at hC ⊢
      exact ih hC

/-- The rectangular filtered circuit realizes the filtered product with a shared data oracle,
additive query counts, and one extra gate, preserving well formedness and the same counts
under adjoint. -/
theorem rectangularFilteredCircuit_same_oracle_semantics_and_cost
    (O_D : Matrix (RectangularData I M O) (RectangularData I M O) ℂ)
    (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O))) :
    rectProductCircuit C_A C_B = rectLiftRightCircuit C_B ++
      [.gate (rectMiddleFilter (I := I) (M := M) (O := O))] ++ rectLiftLeftCircuit C_A ∧
    evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B) =
      rectFilteredProduct (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C_A)
        (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C_B) ∧
    adjointQueryCount (rectProductCircuit C_A C_B) =
      adjointQueryCount C_A + adjointQueryCount C_B ∧
    adjointGateCount (rectProductCircuit C_A C_B) =
      adjointGateCount C_A + adjointGateCount C_B + 1 ∧
    (WellFormedAdjointCircuit C_A → WellFormedAdjointCircuit C_B →
      WellFormedAdjointCircuit (rectProductCircuit C_A C_B)) ∧
    adjointQueryCount (adjointCircuit (rectProductCircuit C_A C_B)) =
      adjointQueryCount C_A + adjointQueryCount C_B ∧
    adjointGateCount (adjointCircuit (rectProductCircuit C_A C_B)) =
      adjointGateCount C_A + adjointGateCount C_B + 1 := by
  have hqc : adjointQueryCount (rectProductCircuit C_A C_B) =
      adjointQueryCount C_A + adjointQueryCount C_B := by
    rw [rectProductCircuit, adjointQueryCount_append, adjointQueryCount_append,
      adjointQueryCount_rectLiftRightCircuit, adjointQueryCount_rectLiftLeftCircuit]
    simp only [adjointQueryCount]
    omega
  have hgc : adjointGateCount (rectProductCircuit C_A C_B) =
      adjointGateCount C_A + adjointGateCount C_B + 1 := by
    rw [rectProductCircuit, adjointGateCount_append, adjointGateCount_append,
      adjointGateCount_rectLiftRightCircuit, adjointGateCount_rectLiftLeftCircuit]
    simp only [adjointGateCount]
    omega
  refine ⟨rfl, ?_, hqc, hgc, ?_, by rw [adjointQueryCount_adjointCircuit]; exact hqc,
    by rw [adjointGateCount_adjointCircuit]; exact hgc⟩
  · rw [rectProductCircuit, evaluate_append, evaluate_append]
    simp only [evaluate, instructionMatrix, Matrix.mul_one,
      evaluate_rectLiftRightCircuit O_D C_B, evaluate_rectLiftLeftCircuit O_D C_A]
    rw [rectFilteredProduct]
  · intro hA hB
    rw [rectProductCircuit]
    exact WellFormedAdjointCircuit.append
      (WellFormedAdjointCircuit.append (WellFormedAdjointCircuit.rectLiftRight hB)
        (by
          simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil,
            and_true]
          exact (rectangularTagFilter_reversible_flag_semantics
            (I := I) (M := M) (O := O) (J := J) (K := K)).1))
      (WellFormedAdjointCircuit.rectLiftLeft hA)

set_option maxHeartbeats 4000000 in

/-- The rectangular circuit success probability is its Born event probability, and its
postselected vector is the product of the compressed factors applied to the input. Under
unitary and normalization assumptions this probability lies between zero and one. -/
theorem rectangularFilteredCircuit_actual_branch_and_born (j₀ : J) (k₀ : K)
    (O_D : Matrix (RectangularData I M O) (RectangularData I M O) ℂ)
    (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O))) (ψ : QState I) :
    let W := evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B)
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ =
      MeasureProb (ApplyGate W (rectInputFrame j₀ k₀ *ᵥ ψ)) (rectSuccessEvent j₀ k₀) ∧
    Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector W (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ =
      (Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber k₀ * rectOutputTagFrame)
        (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C_B)
        (encodingFiber k₀ * rectMiddleTagFrame) *
       Qatlib.Concepts.Execution.WorkspaceCP.compress (encodingFiber j₀ * rectMiddleTagFrame)
        (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C_A)
        (encodingFiber j₀ * rectInputTagFrame)) *ᵥ ψ ∧
    (O_D ∈ Matrix.unitaryGroup (RectangularData I M O) ℂ →
      WellFormedAdjointCircuit C_A → WellFormedAdjointCircuit C_B → Normalized ψ →
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ ∈
        Set.Icc (0 : ℝ) 1) := by
  intro W
  have hG1 := rectangularTagFilter_frames_and_projector (I := I) (M := M) (O := O) j₀ k₀
  refine ⟨?_, ?_, ?_⟩
  · simp only [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability, ProjectiveBranchMass, hG1.2.2.2.2.2,
    projectiveBranch_projector, measureProb_collapse, Finset.inter_univ]
  · show Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
      (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ = _
    rw [rectProductCircuit, evaluate_append, evaluate_append]
    simp only [evaluate, instructionMatrix, Matrix.mul_one,
      evaluate_rectLiftRightCircuit O_D C_B, evaluate_rectLiftLeftCircuit O_D C_A]
    rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionVector, ← rectFilteredProduct,
      (rectangularTagFilter_exact_compressed_product j₀ k₀ _ _).1]
  · intro hOD hA hB hψ
    have hWu : (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B)) ∈
        Matrix.unitaryGroup (RectangularWorkspace I M O J K) ℂ := by
      rw [rectProductCircuit, evaluate_append, evaluate_append]
      simp only [evaluate, instructionMatrix, Matrix.mul_one,
        evaluate_rectLiftRightCircuit O_D C_B, evaluate_rectLiftLeftCircuit O_D C_A]
      rw [← rectFilteredProduct]
      exact (rectangularTagFilter_exact_compressed_product j₀ k₀ _ _).2
        (WellFormedAdjointCircuit.evaluate_unitary hA
          (tensorGate_unitary (Matrix.unitaryGroup J ℂ).one_mem hOD))
        (WellFormedAdjointCircuit.evaluate_unitary hB
          (tensorGate_unitary (Matrix.unitaryGroup K ℂ).one_mem hOD))
    have hn : Normalized (ApplyGate
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
          (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
        (rectInputFrame j₀ k₀ *ᵥ ψ)) :=
      normalized_applyGate hWu (Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.normalized_mulVec hG1.2.2.2.1 hψ)
    show 0 ≤ Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
          (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
        (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ ∧
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability
        (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
          (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
        (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ ≤ 1
    constructor
    · rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability, ProjectiveBranchMass, hG1.2.2.2.2.2,
      projectiveBranch_projector]
      exact measureProb_nonneg _ _
    · rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability, ProjectiveBranchMass, hG1.2.2.2.2.2,
      projectiveBranch_projector, measureProb_collapse, Finset.inter_univ]
      exact measureProb_le_one hn _

/-- Composing the rectangular block encodings gives a block encoding of `B * A` with scale `α *
β` and error `β * ε + α * η + ε * η`. -/
private theorem rect_program_blockEncoding (j₀ : J) (k₀ : K)
    (O_D : Matrix (RectangularData I M O) (RectangularData I M O) ℂ)
    (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O)))
    (A : Matrix M I ℂ) (B : Matrix O M ℂ) (α β ε η : ℝ)
    (h1 : Qatlib.Concepts.BlockEncoding.BlockEncoding A (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C_A)
      (encodingFiber j₀ * rectMiddleTagFrame) (encodingFiber j₀ * rectInputTagFrame) α ε)
    (h2 : Qatlib.Concepts.BlockEncoding.BlockEncoding B (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C_B)
      (encodingFiber k₀ * rectOutputTagFrame) (encodingFiber k₀ * rectMiddleTagFrame) β η) :
    Qatlib.Concepts.BlockEncoding.BlockEncoding (B * A)
      (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
        (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
      (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) (α * β) (β * ε + α * η + ε * η) := by
  have h := rectangularTagFilter_approximate_block_product j₀ k₀ A B _ _ α β ε η h1 h2
  show Qatlib.Concepts.BlockEncoding.BlockEncoding (B * A)
    (evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B))
    (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) (α * β) (β * ε + α * η + ε * η)
  rw [rectProductCircuit, evaluate_append, evaluate_append]
  simp only [evaluate, instructionMatrix, Matrix.mul_one,
    evaluate_rectLiftRightCircuit O_D C_B, evaluate_rectLiftLeftCircuit O_D C_A]
  rw [← rectFilteredProduct]
  exact h

set_option maxHeartbeats 1000000 in

/-- Bounds the scaled success probability error for the rectangular product and gives a success
probability lower bound when the product output norm dominates the encoding error. -/
theorem rectangularFilteredCircuit_probability_error_and_lower (j₀ : J) (k₀ : K)
    (O_D : Matrix (RectangularData I M O) (RectangularData I M O) ℂ)
    (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O)))
    (A : Matrix M I ℂ) (B : Matrix O M ℂ) (α β ε η : ℝ) (ψ : QState I)
    (h1 : Qatlib.Concepts.BlockEncoding.BlockEncoding A (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C_A)
      (encodingFiber j₀ * rectMiddleTagFrame) (encodingFiber j₀ * rectInputTagFrame) α ε)
    (h2 : Qatlib.Concepts.BlockEncoding.BlockEncoding B (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C_B)
      (encodingFiber k₀ * rectOutputTagFrame) (encodingFiber k₀ * rectMiddleTagFrame) β η)
    (hψ : Normalized ψ) :
    let W := evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B)
    let τ := β * ε + α * η + ε * η
    let r := ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector ((B * A) *ᵥ ψ)‖
    let p :=
        Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W
        (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ
    |(α * β)^2 * p - r^2| ≤ τ * (2*r + τ) ∧
    (τ ≤ r → ((r - τ) / (α * β))^2 ≤ p) := by
  intro W τ r p
  have hBE := rect_program_blockEncoding j₀ k₀ O_D C_A C_B A B α β ε η h1 h2
  exact ⟨Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_error hBE hψ,
    fun hgap => Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_probability_lower hBE hψ hgap⟩

set_option maxHeartbeats 1000000 in

/-- If the product output norm exceeds the encoding error, the rectangular circuit has positive
success probability and a normalized conditional output with the stated approximation bound. -/
theorem rectangularFilteredCircuit_gap_actual_normalized_output (j₀ : J) (k₀ : K)
    (O_D : Matrix (RectangularData I M O) (RectangularData I M O) ℂ)
    (C_A : List (AdjointStep (J × RectangularData I M O)))
    (C_B : List (AdjointStep (K × RectangularData I M O)))
    (A : Matrix M I ℂ) (B : Matrix O M ℂ) (α β ε η : ℝ) (ψ : QState I)
    (h1 : Qatlib.Concepts.BlockEncoding.BlockEncoding A (evaluate (TensorGate (1 : Matrix J J ℂ) O_D) C_A)
      (encodingFiber j₀ * rectMiddleTagFrame) (encodingFiber j₀ * rectInputTagFrame) α ε)
    (h2 : Qatlib.Concepts.BlockEncoding.BlockEncoding B (evaluate (TensorGate (1 : Matrix K K ℂ) O_D) C_B)
      (encodingFiber k₀ * rectOutputTagFrame) (encodingFiber k₀ * rectMiddleTagFrame) β η)
    (hψ : Normalized ψ) :
    let W := evaluate (TensorGate (1 : Matrix Bool Bool ℂ)
      (TensorGate (1 : Matrix (J × K) (J × K) ℂ) O_D)) (rectProductCircuit C_A C_B)
    let τ := β * ε + α * η + ε * η
    let r := ‖Qatlib.Concepts.BlockEncoding.Postselection.stateVector ((B * A) *ᵥ ψ)‖
    τ < r →
      0 < Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionProbability W (rectOutputFrame j₀ k₀) (rectInputFrame j₀ k₀) ψ ∧
      ∃ φ : QState O, Qatlib.Concepts.BlockEncoding.Postselection.Encoding.postselectionOutput W (rectOutputFrame j₀ k₀)
          (rectInputFrame j₀ k₀) ψ = some φ ∧
        Qatlib.Concepts.BlockEncoding.Postselection.IsNormalizedApplication (B * A) ψ φ (2*τ/r) ∧
        ProjectiveConditionalState (Qatlib.Concepts.Execution.WorkspaceCP.rangeProjector (rectOutputFrame j₀ k₀)) true
          (ApplyGate W (rectInputFrame j₀ k₀ *ᵥ ψ)) = some (rectOutputFrame j₀ k₀ *ᵥ φ) := by
  intro W τ r hgap
  have hBE := rect_program_blockEncoding j₀ k₀ O_D C_A C_B A B α β ε η h1 h2
  obtain ⟨hpos, φ, hφ, hnorm⟩ :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_output_of_gap hBE hψ hgap
  refine ⟨hpos, φ, hφ, hnorm, ?_⟩
  have hL : IsIsometry (rectOutputFrame (I := I) (M := M) (O := O) j₀ k₀) :=
    (rectangularTagFilter_frames_and_projector (I := I) (M := M) (O := O) j₀ k₀).2.2.2.2.1
  rw [Qatlib.Concepts.BlockEncoding.Postselection.Encoding.projectiveConditionalState_eq_postselection hL _ _ _, hφ]
  simp

end Qatlib.Concepts.MatrixAccess.CircuitPipeline
