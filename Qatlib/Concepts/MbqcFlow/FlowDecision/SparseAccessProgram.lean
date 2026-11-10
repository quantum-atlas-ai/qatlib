/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessRefined
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.MatrixAccess.RitzPipeline

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.TableAccess.LookupCompile
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

structure SparseRecord (p v : ℕ) where
  row : ℕ
  slot : ℕ
  position : Reg p
  value : Reg v

def recordAddress (slots row slot : ℕ) : ℕ := row * slots + slot

def recordIndex {rows slots : ℕ} (row : Fin rows) (slot : Fin slots) : Fin (rows * slots) :=
  ⟨recordAddress slots row.val slot.val, by
    calc
      recordAddress slots row.val slot.val < row.val * slots + slots := by
        exact Nat.add_lt_add_left slot.isLt _
      _ = (row.val + 1) * slots := by simp [Nat.add_mul]
      _ ≤ rows * slots := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt row.isLt)⟩

@[simp] theorem recordIndex_val {rows slots : ℕ} (row : Fin rows) (slot : Fin slots) :
    (recordIndex row slot).val = recordAddress slots row.val slot.val := rfl

def outputWord {p v : ℕ} (position : Reg p) (value : Reg v) : Reg (p + v) :=
  Fin.append position value

def outputPosition {p v : ℕ} (word : Reg (p + v)) : Reg p :=
  fun i => word (Fin.castAdd v i)

def outputValue {p v : ℕ} (word : Reg (p + v)) : Reg v :=
  fun i => word (Fin.natAdd p i)

@[simp] theorem outputPosition_outputWord {p v : ℕ} (position : Reg p) (value : Reg v) :
    outputPosition (outputWord position value) = position := by
  funext i
  simp [outputPosition, outputWord, Fin.append_left]

@[simp] theorem outputValue_outputWord {p v : ℕ} (position : Reg p) (value : Reg v) :
    outputValue (outputWord position value) = value := by
  funext i
  simp [outputValue, outputWord, Fin.append_right]

def resolvedRecord {p v : ℕ} (slots : ℕ) (es : List (SparseRecord p v)) (address : ℕ) :
    Reg p × Reg v :=
  es.foldl (fun acc e =>
    if recordAddress slots e.row e.slot = address then (e.position, e.value) else acc)
    ((fun _ => false), (fun _ => false))

theorem resolvedRecord_lastWrite {p v slots : ℕ} (es : List (SparseRecord p v))
    (e : SparseRecord p v) (pre post : List (SparseRecord p v))
    (hes : es = pre ++ e :: post)
    (hnoLater : ∀ later ∈ post,
      recordAddress slots later.row later.slot ≠ recordAddress slots e.row e.slot) :
    resolvedRecord slots es (recordAddress slots e.row e.slot) = (e.position, e.value) := by
  subst es
  simp only [resolvedRecord, List.foldl_append, List.foldl_cons, ↓reduceIte]
  revert hnoLater
  induction post with
  | nil => intro _; rfl
  | cons later tail ih =>
      intro hnoLater
      rw [List.foldl_cons, if_neg (hnoLater later (by simp))]
      exact ih (fun other hother => hnoLater other (by simp [hother]))

def sparseTableBit {p v : ℕ} (slots : ℕ) (es : List (SparseRecord p v))
    {a : ℕ} (r : Fin (2 ^ a)) (j : Fin (p + v)) : Bool :=
  let record := resolvedRecord slots es r.val
  outputWord record.1 record.2 j

def sparseEntriesLegal {p v : ℕ} (rows slots : ℕ) (es : List (SparseRecord p v)) : Prop :=
  ∀ e ∈ es, e.row < rows ∧ e.slot < slots

def carriesSparseTable (a p v rows slots : ℕ) (es : List (SparseRecord p v))
    (x : Reg (inputs a (p + v))) : Prop :=
  sparseEntriesLegal rows slots es ∧
    ∀ (r : Fin (2 ^ a)) (j : Fin (p + v)),
      x (tableWire a (p + v) r j) = sparseTableBit slots es r j

def loadRecordIndex (a p v : ℕ) {rows slots : ℕ} (row : Fin rows) (slot : Fin slots)
    (x : Reg (inputs a (p + v))) : Reg (inputs a (p + v)) :=
  loadIndex a (p + v) (recordIndex row slot) x

theorem loadRecordIndex_bits (a p v : ℕ) {rows slots : ℕ} (row : Fin rows) (slot : Fin slots)
    (x : Reg (inputs a (p + v))) :
    loadedIndexBits a (p + v) (recordIndex row slot) (loadRecordIndex a p v row slot x) := by
  exact loadIndex_bits a (p + v) (recordIndex row slot) x

theorem checkedLookup_sparse (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a)
    (es : List (SparseRecord p v)) (x : Reg (inputs a (p + v)))
    (row : Fin rows) (slot : Fin slots)
    (hx : ∀ i : Fin a,
      x (addressWire a (p + v) i) = (recordIndex row slot).val.testBit i.val)
    (htable : carriesSparseTable a p v rows slots es x) (j : Fin (p + v)) :
    eval (checkedLookupExpr a (p + v) (rows * slots) hD j) x =
      (x (enableWire a (p + v)) &&
        outputWord (resolvedRecord slots es (recordIndex row slot).val).1
          (resolvedRecord slots es (recordIndex row slot).val).2 j) := by
  have h := checkedLookup_value a (p + v) (rows * slots) hD x
    (Fin.castLE hD (recordIndex row slot)) j hx
  rw [h, if_pos (show (Fin.castLE hD (recordIndex row slot)).val < rows * slots from
    (recordIndex row slot).isLt), htable.2]
  rfl

theorem checkedLookup_sparse_loaded (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a)
    (es : List (SparseRecord p v)) (x : Reg (inputs a (p + v)))
    (row : Fin rows) (slot : Fin slots)
    (htable : carriesSparseTable a p v rows slots es x) (j : Fin (p + v)) :
    eval (checkedLookupExpr a (p + v) (rows * slots) hD j)
        (loadRecordIndex a p v row slot x) =
      (x (enableWire a (p + v)) &&
        outputWord (resolvedRecord slots es (recordIndex row slot).val).1
          (resolvedRecord slots es (recordIndex row slot).val).2 j) := by
  rw [loadRecordIndex, checkedLookup_loaded a (p + v) hD (recordIndex row slot) j x, htable.2]
  rfl

theorem checkedLookup_sparse_decode (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a)
    (es : List (SparseRecord p v)) (x : Reg (inputs a (p + v)))
    (row : Fin rows) (slot : Fin slots)
    (htable : carriesSparseTable a p v rows slots es x)
    (henable : x (enableWire a (p + v)) = true) :
    outputPosition (fun j => eval (checkedLookupExpr a (p + v) (rows * slots) hD j)
        (loadRecordIndex a p v row slot x)) =
      (resolvedRecord slots es (recordIndex row slot).val).1 ∧
    outputValue (fun j => eval (checkedLookupExpr a (p + v) (rows * slots) hD j)
        (loadRecordIndex a p v row slot x)) =
      (resolvedRecord slots es (recordIndex row slot).val).2 := by
  have hword : (fun j => eval (checkedLookupExpr a (p + v) (rows * slots) hD j)
      (loadRecordIndex a p v row slot x)) =
      outputWord (resolvedRecord slots es (recordIndex row slot).val).1
        (resolvedRecord slots es (recordIndex row slot).val).2 := by
    funext j
    rw [checkedLookup_sparse_loaded a p v rows slots hD es x row slot htable j, henable]
    simp
  rw [hword]
  exact ⟨outputPosition_outputWord _ _, outputValue_outputWord _ _⟩

theorem checkedLookup_sparse_reject (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a)
    (x : Reg (inputs a (p + v))) (r : Fin (2 ^ a))
    (hr : rows * slots ≤ r.val)
    (hx : ∀ i : Fin a, x (addressWire a (p + v) i) = r.val.testBit i.val)
    (j : Fin (p + v)) :
    eval (checkedLookupExpr a (p + v) (rows * slots) hD j) x = false := by
  rw [checkedLookup_value a (p + v) (rows * slots) hD x r j hx, if_neg (by omega)]

theorem sparseLookup_word (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a) :
    ∃ (k : ℕ) (g : BooleanDAG (inputs a (p + v)) k)
      (out : Fin (p + v) → Fin (inputs a (p + v) + k)),
      k ≤ (p + v) * (1 + rows * slots * (2 * a + 5)) ∧
      reflectionLegal (booleanDAGSteps g out) ∧
      QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
      GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + (p + v) ∧
      (∀ (ψ : QState (Reg (inputs a (p + v)) × Reg (p + v))),
        Run (1 : Matrix (Reg (inputs a (p + v) + k + (p + v)))
          (Reg (inputs a (p + v) + k + (p + v))) ℂ)
          (reflectionCompile (booleanDAGSteps g out))
          (booleanDAGEmbed (inputs a (p + v)) k (p + v) ψ) =
          ∑ xy, ψ xy • Qatlib.Foundations.PureStateMath.Ket (booleanDAGInput (inputs a (p + v)) k (p + v) xy.1
            (fun j => xy.2 j ^^
              eval (checkedLookupExpr a (p + v) (rows * slots) hD j) xy.1))) ∧
      (∀ (ψ : QState (Reg (inputs a (p + v)) × Reg (p + v))),
        Run (1 : Matrix (Reg (inputs a (p + v) + k + (p + v)))
          (Reg (inputs a (p + v) + k + (p + v))) ℂ)
          ((reflectionCompile (booleanDAGSteps g out)) ++
            (reflectionCompile (booleanDAGSteps g out)))
          (booleanDAGEmbed (inputs a (p + v)) k (p + v) ψ) =
          booleanDAGEmbed (inputs a (p + v)) k (p + v) ψ) := by
  exact checkedLookup_word a (p + v) (rows * slots) hD

theorem frontier1 (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a) :
    (∀ (row : Fin rows) (slot : Fin slots),
      (recordIndex row slot).val = row.val * slots + slot.val) ∧
    (∀ (es : List (SparseRecord p v)) (e : SparseRecord p v)
      (pre post : List (SparseRecord p v)),
      es = pre ++ e :: post →
      (∀ later ∈ post,
        recordAddress slots later.row later.slot ≠ recordAddress slots e.row e.slot) →
      resolvedRecord slots es (recordAddress slots e.row e.slot) = (e.position, e.value)) ∧
    (∀ (position : Reg p) (value : Reg v),
      outputPosition (outputWord position value) = position ∧
        outputValue (outputWord position value) = value) ∧
    (∀ (es : List (SparseRecord p v)) (x : Reg (inputs a (p + v)))
      (row : Fin rows) (slot : Fin slots) (j : Fin (p + v)),
      carriesSparseTable a p v rows slots es x →
      eval (checkedLookupExpr a (p + v) (rows * slots) hD j)
          (loadRecordIndex a p v row slot x) =
        (x (enableWire a (p + v)) &&
          outputWord (resolvedRecord slots es (recordIndex row slot).val).1
            (resolvedRecord slots es (recordIndex row slot).val).2 j)) ∧
    (∀ (x : Reg (inputs a (p + v))) (r : Fin (2 ^ a)) (j : Fin (p + v)),
      rows * slots ≤ r.val →
      (∀ i : Fin a, x (addressWire a (p + v) i) = r.val.testBit i.val) →
      eval (checkedLookupExpr a (p + v) (rows * slots) hD j) x = false) ∧
    (∃ (k : ℕ) (g : BooleanDAG (inputs a (p + v)) k)
      (out : Fin (p + v) → Fin (inputs a (p + v) + k)),
      k ≤ (p + v) * (1 + rows * slots * (2 * a + 5)) ∧
      reflectionLegal (booleanDAGSteps g out) ∧
      QueryCount (reflectionCompile (booleanDAGSteps g out)) = 0 ∧
      GateCount (reflectionCompile (booleanDAGSteps g out)) ≤ 30 * k + (p + v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro row slot
    rfl
  · intro es e pre post hes hnoLater
    exact resolvedRecord_lastWrite es e pre post hes hnoLater
  · intro position value
    exact ⟨outputPosition_outputWord position value, outputValue_outputWord position value⟩
  · intro es x row slot j htable
    exact checkedLookup_sparse_loaded a p v rows slots hD es x row slot htable j
  · intro x r j hr hx
    exact checkedLookup_sparse_reject a p v rows slots hD x r hr hx j
  · obtain ⟨k, g, out, hk, hlegal, hquery, hgate, _, _⟩ :=
      sparseLookup_word a p v rows slots hD
    exact ⟨k, g, out, hk, hlegal, hquery, hgate⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram
