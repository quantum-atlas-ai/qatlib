/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessRefined

/-!
# Sparse record lookup and reversible compilation

Defines `SparseRecord`, row-major record addresses, and a last-write resolution rule for sparse
position-value entries. It encodes resolved records as Boolean table words and proves
correctness, decoding, and out-of-range rejection for checked lookup expressions.

The theorem `sparseLookup_word` constructs a Boolean DAG and a reversible XOR lookup circuit
with explicit size and gate bounds, zero queries, and restoration after two applications on the
embedded input space. The reversible-circuit background is described in [NielsenChuang2010].

## Main statements

* `resolvedRecord_lastWrite`: the last write to an address determines the resolved record.
* `checkedLookup_sparse_decode`: enabled lookup returns the stored position and value.
* `sparseLookup_word`: bounded reversible compilation of the lookup word.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
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

/-- A sparse record containing a row, a slot, a `p`-bit position, and a `v`-bit value. -/
structure SparseRecord (p v : ℕ) where
  row : ℕ
  slot : ℕ
  position : Reg p
  value : Reg v

/-- The row-major address `row * slots + slot` of a record. -/
def recordAddress (slots row slot : ℕ) : ℕ := row * slots + slot

/-- The bounded row-major index of a valid row and slot in a table with `rows * slots` entries. -/
def recordIndex {rows slots : ℕ} (row : Fin rows) (slot : Fin slots) : Fin (rows * slots) :=
  ⟨recordAddress slots row.val slot.val, by
    calc
      recordAddress slots row.val slot.val < row.val * slots + slots := by
        exact Nat.add_lt_add_left slot.isLt _
      _ = (row.val + 1) * slots := by simp [Nat.add_mul]
      _ ≤ rows * slots := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt row.isLt)⟩

/-- The underlying natural number of `recordIndex` equals its row-major record address. -/
@[simp] theorem recordIndex_val {rows slots : ℕ} (row : Fin rows) (slot : Fin slots) :
    (recordIndex row slot).val = recordAddress slots row.val slot.val := rfl

/-- Concatenates a position register and a value register into one output word. -/
def outputWord {p v : ℕ} (position : Reg p) (value : Reg v) : Reg (p + v) :=
  Fin.append position value

/-- Extracts the first `p` bits of a position-value output word. -/
def outputPosition {p v : ℕ} (word : Reg (p + v)) : Reg p :=
  fun i => word (Fin.castAdd v i)

/-- Extracts the final `v` bits of a position-value output word. -/
def outputValue {p v : ℕ} (word : Reg (p + v)) : Reg v :=
  fun i => word (Fin.natAdd p i)

/-- Extracting the position from a concatenated output word recovers the original position
register. -/
@[simp] theorem outputPosition_outputWord {p v : ℕ} (position : Reg p) (value : Reg v) :
    outputPosition (outputWord position value) = position := by
  funext i
  simp [outputPosition, outputWord, Fin.append_left]

/-- Extracting the value from a concatenated output word recovers the original value register. -/
@[simp] theorem outputValue_outputWord {p v : ℕ} (position : Reg p) (value : Reg v) :
    outputValue (outputWord position value) = value := by
  funext i
  simp [outputValue, outputWord, Fin.append_right]

/-- Resolves a record address by scanning entries in order and keeping the last matching
position-value pair, defaulting to two zero registers. -/
def resolvedRecord {p v : ℕ} (slots : ℕ) (es : List (SparseRecord p v)) (address : ℕ) :
    Reg p × Reg v :=
  es.foldl (fun acc e =>
    if recordAddress slots e.row e.slot = address then (e.position, e.value) else acc)
    ((fun _ => false), (fun _ => false))

/-- If no entry after `e` writes to its address, resolving that address returns the position and
value of `e`. -/
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

/-- The selected bit of the concatenated position-value word resolved at a table address. -/
def sparseTableBit {p v : ℕ} (slots : ℕ) (es : List (SparseRecord p v))
    {a : ℕ} (r : Fin (2 ^ a)) (j : Fin (p + v)) : Bool :=
  let record := resolvedRecord slots es r.val
  outputWord record.1 record.2 j

/-- Every entry has row and slot indices within the specified table bounds. -/
def sparseEntriesLegal {p v : ℕ} (rows slots : ℕ) (es : List (SparseRecord p v)) : Prop :=
  ∀ e ∈ es, e.row < rows ∧ e.slot < slots

/-- The entries are legal and every table wire contains the corresponding bit of the resolved
sparse table. -/
def carriesSparseTable (a p v rows slots : ℕ) (es : List (SparseRecord p v))
    (x : Reg (inputs a (p + v))) : Prop :=
  sparseEntriesLegal rows slots es ∧
    ∀ (r : Fin (2 ^ a)) (j : Fin (p + v)),
      x (tableWire a (p + v) r j) = sparseTableBit slots es r j

/-- Loads a valid row-slot record index into the lookup address wires. -/
def loadRecordIndex (a p v : ℕ) {rows slots : ℕ} (row : Fin rows) (slot : Fin slots)
    (x : Reg (inputs a (p + v))) : Reg (inputs a (p + v)) :=
  loadIndex a (p + v) (recordIndex row slot) x

/-- Loading a record index gives the address-bit predicate for that index. -/
theorem loadRecordIndex_bits (a p v : ℕ) {rows slots : ℕ} (row : Fin rows) (slot : Fin slots)
    (x : Reg (inputs a (p + v))) :
    loadedIndexBits a (p + v) (recordIndex row slot) (loadRecordIndex a p v row slot x) := by
  exact loadIndex_bits a (p + v) (recordIndex row slot) x

/-- For an input carrying the sparse table and the specified record address, checked lookup
returns the resolved output bit conjoined with the enable bit. -/
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

/-- After loading a valid record index, checked lookup on an input carrying the sparse table
returns the resolved output bit conjoined with the original enable bit. -/
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

/-- When enabled, checked lookup after loading a valid record index decodes to the resolved
position and value. -/
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

/-- Checked lookup returns `false` on every output bit when the represented address is at least
`rows * slots`. -/
theorem checkedLookup_sparse_reject (a p v rows slots : ℕ) (hD : rows * slots ≤ 2 ^ a)
    (x : Reg (inputs a (p + v))) (r : Fin (2 ^ a))
    (hr : rows * slots ≤ r.val)
    (hx : ∀ i : Fin a, x (addressWire a (p + v) i) = r.val.testBit i.val)
    (j : Fin (p + v)) :
    eval (checkedLookupExpr a (p + v) (rows * slots) hD j) x = false := by
  rw [checkedLookup_value a (p + v) (rows * slots) hD x r j hx, if_neg (by omega)]

/-- Constructs a bounded-size Boolean DAG whose legal reversible compilation XORs the checked
lookup word into the output register with zero queries and gate count at most `30 * k + (p +
v)`. Two applications restore every input in the specified embedded state space. -/
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

/-- Collects row-major addressing, last-write resolution, output decoding, valid-address lookup,
out-of-range rejection, and bounded reversible compilation for sparse record tables. -/
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
