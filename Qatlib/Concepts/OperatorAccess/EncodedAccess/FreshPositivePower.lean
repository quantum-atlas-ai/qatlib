/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OperatorAccess.EncodedAccess
import Mathlib.LinearAlgebra.Matrix.Reindex
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.EncodingCore Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.Phase

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-! Fresh-slot unitary gate lifting and positive power block-encoding circuits. -/
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.CopyEvolution.Discriminate Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LinearCombination

namespace Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
variable {K I : Type*} [Fintype K] [DecidableEq K] [Fintype I] [DecidableEq I]

/-- Lift a gate on `K × I` to act on slot `j` of `(Fin m → K) × I` and as the identity on other slots. -/
noncomputable def freshLift {m : ℕ} (j : Fin m) (V : Matrix (K × I) (K × I) ℂ) :
    Matrix ((Fin m → K) × I) ((Fin m → K) × I) ℂ :=
  Matrix.of (fun x y => (if ∀ k : Fin m, k ≠ j → x.1 k = y.1 k then (1:ℂ) else 0) *
    V (x.1 j,x.2) (y.1 j,y.2))

/-- Explicit gate circuit applying a macro gate list sequentially across `m` fresh slots. -/
noncomputable def freshPowerCircuit (m : ℕ) (gs : List (Matrix (K × I) (K × I) ℂ)) :
    Circuit ((Fin m → K) × I) :=
  (List.ofFn (fun j : Fin m => gs.map (fun V => Step.gate (freshLift j V)))).flatten

/-- Ordered matrix product of a list of macro gates. -/
noncomputable def macroListMatrix (gs : List (Matrix (K × I) (K × I) ℂ)) : Matrix (K × I) (K × I) ℂ :=
  gs.foldl (fun acc V => V*acc) 1

/-- Overall unitary matrix implemented by `freshPowerCircuit`. -/
noncomputable def freshPowerMatrix (m : ℕ) (gs : List (Matrix (K × I) (K × I) ℂ)) :
    Matrix ((Fin m → K) × I) ((Fin m → K) × I) ℂ :=
  (freshPowerCircuit m gs).foldl (fun acc g => match g with
    | .gate V => V*acc
    | .query => acc) 1

/-- Coordinate equivalence isolating slot `j` from the remaining `m - 1` slots. -/
noncomputable def freshSlotEquiv {m : ℕ} (j : Fin m) :
    ((K × I) × ({k : Fin m // k ≠ j} → K)) ≃ ((Fin m → K) × I) where
  toFun x := ((Equiv.funSplitAt j K).symm (x.1.1,x.2),x.1.2)
  invFun y := (((Equiv.funSplitAt j K y.1).1,y.2),(Equiv.funSplitAt j K y.1).2)
  left_inv x := by
    rcases x with ⟨⟨a,i⟩,r⟩
    (try dsimp only)
    rw [Equiv.apply_symm_apply]
  right_inv y := by
    rcases y with ⟨f,i⟩
    (try dsimp only)
    rw [Equiv.symm_apply_apply]

/-- A fresh lift is the relabeling of the original gate tensored with the identity on the other
slots. -/
theorem freshLift_reindex {m : ℕ} (j : Fin m) (V : Matrix (K × I) (K × I) ℂ) :
    freshLift j V = relabelGate (freshSlotEquiv (K := K) (I := I) j)
      (TensorGate V (1 : Matrix ({k : Fin m // k ≠ j} → K) ({k : Fin m // k ≠ j} → K) ℂ)) := by
  ext ⟨f,i⟩ ⟨g,k⟩
  have he : (fun x : {l : Fin m // l ≠ j} => f x) =
      (fun x : {l : Fin m // l ≠ j} => g x) ↔ ∀ l : Fin m, l ≠ j → f l = g l := by
    constructor
    · intro h l hl; exact congrFun h ⟨l,hl⟩
    · intro h; funext l; exact h l l.property
  change (if ∀ l : Fin m, l ≠ j → f l = g l then (1:ℂ) else 0) * V (f j,i) (g j,k) =
    V (f j,i) (g j,k) * (if (fun l : {l : Fin m // l ≠ j} => f l) =
      (fun l : {l : Fin m // l ≠ j} => g l) then (1:ℂ) else 0)
  simp only [he, mul_comm]

/-- Lifting a unitary gate to a fresh slot preserves unitarity. -/
theorem freshLift_unitary {m : ℕ} (j : Fin m) {V : Matrix (K × I) (K × I) ℂ}
    (hV : V ∈ Matrix.unitaryGroup (K × I) ℂ) :
    freshLift j V ∈ Matrix.unitaryGroup ((Fin m → K) × I) ℂ := by
  rw [freshLift_reindex]
  exact relabelGate_mem_unitary (tensorGate_unitary hV (Submonoid.one_mem _)) _

/-- The fresh lift of the identity matrix is the identity matrix. -/
theorem freshLift_one {m : ℕ} (j : Fin m) :
    freshLift (K := K) (I := I) j 1 = 1 := by
  rw [freshLift_reindex]
  simp only [TensorGate, Matrix.one_kronecker_one, relabelGate]
  exact (Matrix.reindexAlgEquiv ℂ ℂ (freshSlotEquiv (K := K) (I := I) j)).map_one

/-- Fresh lifting preserves matrix multiplication. -/
theorem freshLift_mul {m : ℕ} (j : Fin m) (V W : Matrix (K × I) (K × I) ℂ) :
    freshLift j (V*W) = freshLift j V * freshLift j W := by
  simp only [freshLift_reindex]
  have h := (Matrix.reindexAlgEquiv ℂ ℂ (freshSlotEquiv (K := K) (I := I) j)).map_mul
    (TensorGate V (1 : Matrix ({k : Fin m // k ≠ j} → K) ({k : Fin m // k ≠ j} → K) ℂ))
    (TensorGate W (1 : Matrix ({k : Fin m // k ≠ j} → K) ({k : Fin m // k ≠ j} → K) ℂ))
  simpa only [Matrix.reindexAlgEquiv_apply, relabelGate, tensorGate_mul, Matrix.one_mul] using! h

/-- A left fold by left multiplication factors an arbitrary initial accumulator onto the right
of the identity-started fold. -/
theorem positiveMacro_fold_acc {X : Type*} [Fintype X] [DecidableEq X]
    (gs : List (Matrix X X ℂ)) (V : Matrix X X ℂ) :
    gs.foldl (fun acc W => W*acc) V = (gs.foldl (fun acc W => W*acc) 1)*V := by
  induction gs generalizing V with
  | nil => simp
  | cons W gs ih =>
    simp only [List.foldl_cons]
    rw [ih (W*V), ih (W*1)]
    simp [Matrix.mul_assoc]

/-- The matrix of an empty macro list is the identity. -/
@[simp] theorem macroListMatrix_nil : macroListMatrix ([] : List (Matrix (K × I) (K × I) ℂ)) = 1 := rfl

/-- The matrix of a nonempty macro list is the tail matrix multiplied by the head gate. -/
theorem macroListMatrix_cons (V : Matrix (K × I) (K × I) ℂ)
    (gs : List (Matrix (K × I) (K × I) ℂ)) :
    macroListMatrix (V::gs) = macroListMatrix gs * V := by
  simpa [macroListMatrix] using! positiveMacro_fold_acc gs V

/-- Multiplying all fresh lifts of a macro body equals the fresh lift of its matrix. -/
theorem freshLift_whole_body {m : ℕ} (j : Fin m)
    (gs : List (Matrix (K × I) (K × I) ℂ)) :
    (gs.map (freshLift j)).foldl (fun acc V => V*acc) 1 = freshLift j (macroListMatrix gs) := by
  induction gs with
  | nil => simp [freshLift_one]
  | cons V gs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [positiveMacro_fold_acc, Matrix.mul_one, ih, macroListMatrix_cons, freshLift_mul]

/-- Predicate stating that a matrix acts diagonally on slot `j`. -/
def FreshPreserves {m : ℕ} (j : Fin m)
    (V : Matrix ((Fin m → K) × I) ((Fin m → K) × I) ℂ) : Prop :=
  ∀ x y, x.1 j ≠ y.1 j → V x y = 0

/-- The identity matrix satisfies `FreshPreserves` for every slot. -/
theorem FreshPreserves.one {m : ℕ} (j : Fin m) :
    FreshPreserves (K := K) (I := I) j 1 := by
  intro x y h
  simp only [Matrix.one_apply]
  exact if_neg (fun he => h (congrArg (fun z => z.1 j) he))

/-- The product of two matrices satisfying `FreshPreserves` for a slot also satisfies it. -/
theorem FreshPreserves.mul {m : ℕ} {j : Fin m}
    {U V : Matrix ((Fin m → K) × I) ((Fin m → K) × I) ℂ}
    (hU : FreshPreserves j U) (hV : FreshPreserves j V) : FreshPreserves j (U*V) := by
  intro x y h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro z _
  by_cases hx : x.1 j = z.1 j
  · rw [hV z y (by intro hy; exact h (hx.trans hy)), mul_zero]
  · rw [hU x z hx, zero_mul]

/-- A gate lifted to one slot preserves every distinct slot. -/
theorem freshLift_preserves {m : ℕ} (j l : Fin m) (hjl : j ≠ l)
    (V : Matrix (K × I) (K × I) ℂ) : FreshPreserves j (freshLift l V) := by
  intro x y h
  change (if ∀ k : Fin m, k ≠ l → x.1 k = y.1 k then (1:ℂ) else 0) * _ = 0
  rw [if_neg (fun hh => h (hh j hjl)), zero_mul]

/-- The matrix fold of an appended list is the fold of the second list multiplied by that of the
first. -/
theorem positiveMacro_append {X : Type*} [Fintype X] [DecidableEq X]
    (gs hs : List (Matrix X X ℂ)) :
    (gs++hs).foldl (fun acc V => V*acc) 1 =
      (hs.foldl (fun acc V => V*acc) 1)*(gs.foldl (fun acc V => V*acc) 1) := by
  rw [List.foldl_append, positiveMacro_fold_acc]

/-- Folding a flattened list of gate lists equals folding the list of their individual matrix
folds. -/
theorem positiveMacro_flatten {X : Type*} [Fintype X] [DecidableEq X]
    (gss : List (List (Matrix X X ℂ))) :
    gss.flatten.foldl (fun acc V => V*acc) 1 =
      (gss.map (fun gs => gs.foldl (fun acc V => V*acc) 1)).foldl (fun acc V => V*acc) 1 := by
  induction gss with
  | nil => rfl
  | cons gs gss ih =>
    simp only [List.flatten_cons, List.map_cons, List.foldl_cons]
    rw [positiveMacro_append, ih]
    simp only [Matrix.mul_one]
    exact (positiveMacro_fold_acc (gss.map (fun hs => hs.foldl (fun acc W => W*acc) 1))
      (gs.foldl (fun acc W => W*acc) 1)).symm

/-- The fresh power circuit consists of the flattened slotwise fresh lifts, each interpreted as
a gate step. -/
theorem freshPowerCircuit_gates (m : ℕ) (gs : List (Matrix (K × I) (K × I) ℂ)) :
    freshPowerCircuit m gs =
      ((List.ofFn (fun j : Fin m => gs.map (freshLift j))).flatten).map Step.gate := by
  simp only [freshPowerCircuit, List.map_flatten, List.map_ofFn, Function.comp_def, List.map_map]

/-- The fresh power matrix is the ordered product of the whole macro body lifted to each slot. -/
theorem freshPowerMatrix_whole_bodies (m : ℕ) (gs : List (Matrix (K × I) (K × I) ℂ)) :
    freshPowerMatrix m gs = (List.ofFn (fun j : Fin m => freshLift j (macroListMatrix gs))).foldl
      (fun acc V => V*acc) 1 := by
  unfold freshPowerMatrix
  rw [freshPowerCircuit_gates, List.foldl_map]
  change ((List.ofFn (fun j : Fin m => gs.map (freshLift j))).flatten).foldl
    (fun acc V => V*acc) 1 = _
  rw [positiveMacro_flatten]
  simp only [List.map_ofFn, Function.comp_def, freshLift_whole_body]

/-- A product of lifts to slots excluding `j` satisfies `FreshPreserves j`. -/
theorem freshProduct_preserves {m : ℕ} (j : Fin m) (js : List (Fin m))
    (hj : j ∉ js) (V : Matrix (K × I) (K × I) ℂ) :
    FreshPreserves j ((js.map (fun l => freshLift l V)).foldl (fun acc W => W*acc) 1) := by
  induction js with
  | nil => exact FreshPreserves.one j
  | cons l js ih =>
    have hjl : j ≠ l := by intro he; subst l; exact hj List.mem_cons_self
    have htail : j ∉ js := fun h => hj (List.mem_cons_of_mem l h)
    simp only [List.map_cons, List.foldl_cons]
    rw [positiveMacro_fold_acc, Matrix.mul_one]
    exact (ih htail).mul (freshLift_preserves j l hjl V)

/-- Compression of a preserving matrix followed by a fresh lift factors into the two compressed
matrices. -/
theorem fresh_corner_product {m : ℕ} (j : Fin m) (seed : K)
    (T : Matrix ((Fin m → K) × I) ((Fin m → K) × I) ℂ)
    (V : Matrix (K × I) (K × I) ℂ) (hT : FreshPreserves j T) :
    compress (encodingFiber (fun _ : Fin m => seed)) (T*freshLift j V)
      (encodingFiber (fun _ : Fin m => seed)) =
      compress (encodingFiber (fun _ : Fin m => seed)) T
        (encodingFiber (fun _ : Fin m => seed)) * compress (encodingFiber seed) V (encodingFiber seed) := by
  ext i k
  rw [compress_encodingFiber_eq, Matrix.mul_apply, Matrix.mul_apply]
  simp only [compress_encodingFiber_eq]
  let f : Fin m → K := fun _ => seed
  have he (y : (Fin m → K) × I) : T (f,i) y * freshLift j V y (f,k) =
      (if y.1=f then (1:ℂ) else 0)*(T (f,i) (f,y.2)*V (seed,y.2) (seed,k)) := by
    rcases y with ⟨g,b⟩
    by_cases hg : g=f
    · subst g
      simp [freshLift, f]
    · have hz : T (f,i) (g,b)*freshLift j V (g,b) (f,k) = 0 := by
        by_cases hgj : g j = seed
        · have ho : ¬(∀ l : Fin m, l ≠ j → g l = f l) := by
            intro ho
            apply hg
            funext l
            by_cases hl : l=j
            · subst l; exact hgj
            · exact ho l hl
          simp only [freshLift, Matrix.of_apply, if_neg ho, zero_mul, mul_zero]
        · rw [hT (f,i) (g,b) (by simpa [f] using! Ne.symm hgj), zero_mul]
      simp only [hz, if_neg hg, zero_mul]
  change (∑ y : (Fin m → K) × I, T (f,i) y * freshLift j V y (f,k)) =
    ∑ b : I, T (f,i) (f,b)*V (seed,b) (seed,k)
  calc
    _ = ∑ y : (Fin m → K) × I, (if y.1=f then (1:ℂ) else 0)*
        (T (f,i) (f,y.2)*V (seed,y.2) (seed,k)) := Finset.sum_congr rfl (fun y _ => he y)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ g : Fin m → K, (if g=f then (1:ℂ) else 0)*
            (∑ b : I, T (f,i) (f,b)*V (seed,b) (seed,k)) :=
          Finset.sum_congr rfl (fun g _ => (Finset.mul_sum _ _ _).symm)
        _ = _ := sum_fiber_mul_left f (fun g => ∑ b : I, T (f,i) (f,b)*V (seed,b) (seed,k))

/-- Compression of lifts to distinct slots is the corresponding power of the original compressed
matrix. -/
theorem fresh_product_corner {m : ℕ} (js : List (Fin m)) (hn : js.Nodup) (seed : K)
    (V : Matrix (K × I) (K × I) ℂ) :
    compress (encodingFiber (fun _ : Fin m => seed))
      ((js.map (fun j => freshLift j V)).foldl (fun acc W => W*acc) 1)
      (encodingFiber (fun _ : Fin m => seed)) =
      (compress (encodingFiber seed) V (encodingFiber seed))^js.length := by
  induction js with
  | nil =>
    simpa [compress] using! encodingFiber_isIsometry (I := I) (fun _ : Fin m => seed)
  | cons j js ih =>
    have hnot := (List.nodup_cons.mp hn).1
    have htail := (List.nodup_cons.mp hn).2
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [positiveMacro_fold_acc, Matrix.mul_one, fresh_corner_product j seed _ V
      (freshProduct_preserves j js hnot V), ih htail, pow_succ]

/-- An ordered product of unitary macro gates is unitary. -/
theorem positiveMacro_unitary {X : Type*} [Fintype X] [DecidableEq X]
    (gs : List (Matrix X X ℂ)) (hgs : ∀ V ∈ gs, V ∈ Matrix.unitaryGroup X ℂ) :
    gs.foldl (fun acc V => V*acc) 1 ∈ Matrix.unitaryGroup X ℂ := by
  induction gs with
  | nil => exact Submonoid.one_mem _
  | cons V gs ih =>
    simp only [List.foldl_cons]
    rw [positiveMacro_fold_acc, Matrix.mul_one]
    exact Submonoid.mul_mem _ (ih (fun W hW => hgs W (List.mem_cons_of_mem V hW)))
      (hgs V List.mem_cons_self)

/-- A circuit containing only explicit macro gates has zero queries and one gate per list entry. -/
theorem positiveMacro_gate_cost {X : Type*} [Fintype X] [DecidableEq X]
    (gs : List (Matrix X X ℂ)) :
    QueryCount (gs.map Step.gate) = 0 ∧ GateCount (gs.map Step.gate) = gs.length := by
  induction gs with
  | nil => exact ⟨rfl,rfl⟩
  | cons V gs ih => simp [ih]

/-- A list of unitary macro gates defines a unitary circuit. -/
theorem positiveMacro_circuit_unitary {X : Type*} [Fintype X] [DecidableEq X]
    (gs : List (Matrix X X ℂ)) (hgs : ∀ V ∈ gs, V ∈ Matrix.unitaryGroup X ℂ) :
    IsUnitaryCircuit (gs.map Step.gate) := by
  intro V hV
  obtain ⟨W,hW,he⟩ := List.mem_map.mp hV
  cases Step.gate.inj he
  exact hgs V hW

/-- Running an explicit macro circuit applies its ordered matrix product to the input state. -/
theorem positiveMacro_run {X : Type*} [Fintype X] [DecidableEq X]
    (gs : List (Matrix X X ℂ)) (O : Matrix X X ℂ) (psi : QState X) :
    Run O (gs.map Step.gate) psi = ApplyGate (gs.foldl (fun acc V => V*acc) 1) psi := by
  induction gs generalizing psi with
  | nil => simp [ApplyGate]
  | cons V gs ih =>
    simp only [List.map_cons, Run, List.foldl_cons]
    rw [ih, positiveMacro_fold_acc gs (V*1), Matrix.mul_one]
    simp only [ApplyGate, Matrix.mulVec_mulVec]

/-- Repeating a unitary macro body on fresh slots exactly encodes the corresponding power, with
zero queries and the stated gate count and execution semantics. -/
theorem fresh_positive_actual_power_word : ∀ (m : ℕ) (seed : K) (gs : List (Matrix (K × I) (K × I) ℂ))
    (B : Matrix I I ℂ), (∀ V ∈ gs, V ∈ Matrix.unitaryGroup (K × I) ℂ) →
    compress (encodingFiber seed) (macroListMatrix gs) (encodingFiber seed) = B →
    ProjectedUnitaryEncoding (B^m) (freshPowerMatrix m gs)
      (encodingFiber (fun _ : Fin m => seed)) (encodingFiber (fun _ : Fin m => seed)) ∧
    IsUnitaryCircuit (freshPowerCircuit m gs) ∧ QueryCount (freshPowerCircuit m gs) = 0 ∧
    GateCount (freshPowerCircuit m gs) = m*gs.length ∧
    (∀ psi : QState ((Fin m → K) × I), Run 1 (freshPowerCircuit m gs) psi =
      ApplyGate (freshPowerMatrix m gs) psi)
 := by
  intro m seed gs B hgs hc
  let Vs := ((List.ofFn (fun j : Fin m => gs.map (freshLift j))).flatten)
  have hall : ∀ V ∈ Vs, V ∈ Matrix.unitaryGroup ((Fin m → K) × I) ℂ := by
    intro V hV
    obtain ⟨block,hblock,hV⟩ := List.mem_flatten.mp hV
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hblock
    obtain ⟨W,hW,rfl⟩ := List.mem_map.mp hV
    exact freshLift_unitary j (hgs W hW)
  have hword := positiveMacro_circuit_unitary Vs hall
  have hcost := positiveMacro_gate_cost Vs
  have hlen : Vs.length = m*gs.length := by
    simp only [Vs, List.length_flatten, List.map_ofFn, Function.comp_def, List.length_map]
    rw [List.ofFn_const, List.sum_replicate_nat]
  have hmat : freshPowerMatrix m gs ∈ Matrix.unitaryGroup ((Fin m → K) × I) ℂ := by
    rw [freshPowerMatrix_whole_bodies]
    apply positiveMacro_unitary
    intro V hV
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hV
    exact freshLift_unitary j (positiveMacro_unitary gs hgs)
  have hcorner : compress (encodingFiber (fun _ : Fin m => seed)) (freshPowerMatrix m gs)
      (encodingFiber (fun _ : Fin m => seed)) = B^m := by
    rw [freshPowerMatrix_whole_bodies]
    have he := fresh_product_corner (List.ofFn (fun j : Fin m => j))
      (List.nodup_ofFn.mpr Function.injective_id) seed (macroListMatrix gs)
    simp only [List.map_ofFn, Function.comp_def, List.length_ofFn, hc] at he
    exact he
  refine ⟨⟨hmat, encodingFiber_isIsometry _, encodingFiber_isIsometry _, hcorner⟩, ?_, ?_, ?_, ?_⟩
  · rw [freshPowerCircuit_gates]
    exact hword
  · rw [freshPowerCircuit_gates]
    exact hcost.1
  · rw [freshPowerCircuit_gates]
    exact hcost.2.trans hlen
  · intro psi
    letI : DecidableEq (Fin m → K) := @Fintype.decidablePiFintype (Fin m)
      (fun _ : Fin m => K) (fun _ => inferInstance) (Fin.fintype m)
    letI : DecidableEq ((Fin m → K) × I) := instDecidableEqProd
    unfold freshPowerMatrix
    simp only [freshPowerCircuit_gates, List.foldl_map]
    change Run _ (Vs.map Step.gate) psi = ApplyGate (Vs.foldl (fun acc V => V*acc) 1) psi
    exact positiveMacro_run Vs _ psi

/-- The sum of squared norms of the images of basis states equals the real part of the Gram
matrix trace. -/
theorem positiveAccess_trace_gram (V : Matrix I I ℂ) :
    (∑ i : I, ‖stateVector (V *ᵥ Ket i)‖^2) = (Matrix.trace (Vᴴ*V)).re := by
  have hv (z : ℂ) : ((starRingEnd ℂ) z*z).re = ‖z‖^2 := by
    rw [mul_comm, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp only [stateVector_norm_sq, MeasureProb, BornProb, mulVec_ket_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (hv (V j i)).symm

/-- For a Hermitian encoded matrix, the average fresh-power postselection probability is its
even-power trace divided by the dimension. -/
theorem positive_power_actual_purity_mass : ∀ (m : ℕ) (seed : K) (gs : List (Matrix (K × I) (K × I) ℂ))
    (rho : Matrix I I ℂ), (∀ V ∈ gs, V ∈ Matrix.unitaryGroup (K × I) ℂ) →
    compress (encodingFiber seed) (macroListMatrix gs) (encodingFiber seed) = rho →
    rho.IsHermitian → 0 < Fintype.card I →
    (∑ i : I, postselectionProbability (freshPowerMatrix m gs)
      (encodingFiber (fun _ : Fin m => seed)) (encodingFiber (fun _ : Fin m => seed)) (Ket i)) /
      (Fintype.card I : ℝ) = (Matrix.trace (rho^(2*m))).re / (Fintype.card I : ℝ)
 := by
  intro m seed gs rho hgs hc hrho _hcard
  have h := (fresh_positive_actual_power_word m seed gs rho hgs hc).1
  have hp (i : I) : postselectionProbability (freshPowerMatrix m gs)
      (encodingFiber (fun _ : Fin m => seed)) (encodingFiber (fun _ : Fin m => seed)) (Ket i) =
      ‖stateVector (rho^m *ᵥ Ket i)‖^2 := by
    rw [postselectionProbability_eq_norm_sq h.left_isometry]
    simp only [postselectionVector, h.encoded]
  simp_rw [hp]
  rw [positiveAccess_trace_gram, Matrix.conjTranspose_pow, hrho.eq, ← pow_add,
    show m+m=2*m by omega]

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- Explicit schedule of `(slot, step)` indices for fresh-slot purification powers. -/
def freshPurificationAccessWord (m : ℕ) : List (Fin m × Fin 3) :=
  (List.ofFn (fun j : Fin m => [(j,0),(j,1),(j,2)])).flatten
/-- Gate assigned to each step of `freshPurificationAccessWord`. -/
noncomputable def freshPurificationAccessGate (m : ℕ)
    (U : Matrix (A × I) (A × I) ℂ) (g : Fin m × Fin 3) :
    Matrix ((Fin m → A × I) × I) ((Fin m → A × I) × I) ℂ :=
  freshLift g.1 (if g.2 = 0 then TensorGate U (1 : Matrix I I ℂ)
    else if g.2 = 1 then purificationSwap else TensorGate Uᴴ (1 : Matrix I I ℂ))

/-- The fresh purification circuit uses the specified access word, with one forward access,
adjoint access, and swap per power step. -/
theorem fresh_purification_same_word_access_ledger : ∀ (m : ℕ) (U : Matrix (A × I) (A × I) ℂ),
  let gs := [TensorGate U (1 : Matrix I I ℂ), purificationSwap (A := A) (I := I),
    TensorGate Uᴴ (1 : Matrix I I ℂ)]
  freshPowerCircuit m gs = (freshPurificationAccessWord m).map
    (fun g => Step.gate (freshPurificationAccessGate m U g)) ∧
  (freshPurificationAccessWord m).countP (fun g => g.2 == 0) = m ∧
  (freshPurificationAccessWord m).countP (fun g => g.2 == 2) = m ∧
  (freshPurificationAccessWord m).countP (fun g => g.2 == 1) = m ∧
  (freshPurificationAccessWord m).length = 3*m

 := by
  intro m U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [freshPowerCircuit, freshPurificationAccessWord, List.map_flatten,
      List.map_ofFn, Function.comp_def]
    congr 1
  · simp [freshPurificationAccessWord, List.countP_flatten, List.map_ofFn,
      Function.comp_def, List.ofFn_const]
  · simp [freshPurificationAccessWord, List.countP_flatten, List.map_ofFn,
      Function.comp_def, List.ofFn_const]
  · simp [freshPurificationAccessWord, List.countP_flatten, List.map_ofFn,
      Function.comp_def, List.ofFn_const]
  · simp [freshPurificationAccessWord, List.length_flatten, List.map_ofFn,
      Function.comp_def, List.ofFn_const, Nat.mul_comm]

end Qatlib.Concepts.OperatorAccess.EncodedAccess
