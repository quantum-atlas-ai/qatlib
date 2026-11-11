/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding
import Qatlib.Concepts.BlockEncoding.Basic
import Qatlib.Concepts.BlockEncoding.EncodingCore.PrepareUnitary
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# Sparse access data and query accounting

`SparseAccess` records row and column position maps and complex matrix entries, while
`SparseAccessLegal` specifies their support, injectivity, padding, and entry bounds. The module
defines padded address spaces, preparation vectors, and the normalization used in sparse block
encoding.

`SparseAccessStep` and `PointUsage` provide a symbolic query and gate ledger. Legal nonzero
entries occur once in each position map, and the encoding word uses one row query, one column
query, two value queries, and three gate steps. See [GilyenSuLowWiebe2019].

## Main statements

* `rowLegalCount_eq` and `colLegalCount_eq`: characterize support multiplicities.
* `pointUsage_eq_encodingWordUsage`: match nonzero-entry usage to the encoding word.
* `encodingWord_ledger`: compute the symbolic resource counts.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {sr sc : ℕ}

/-- The disjoint union of column indices and `sr` padding slots. -/
abbrev ColAddr (O : Type*) (sr : ℕ) := O ⊕ Fin sr

/-- The disjoint union of row indices and `sc` padding slots. -/
abbrev RowAddr (I : Type*) (sc : ℕ) := I ⊕ Fin sc

/-- The product of the padded column and row address types. -/
abbrev SparseAddr (I O : Type*) (sr sc : ℕ) := ColAddr O sr × RowAddr I sc

/-- The padded column address, padded row address, and Boolean amplitude-flag workspace. -/
abbrev SparseWorkspace (I O : Type*) (sr sc : ℕ) :=
  ColAddr O sr × (RowAddr I sc × Bool)

/-- The initial padded column address with slot index zero. -/
def colStart (O : Type*) (sr : ℕ) [NeZero sr] : ColAddr O sr := .inr 0

/-- The initial padded row address with slot index zero. -/
def rowStart (I : Type*) (sc : ℕ) [NeZero sc] : RowAddr I sc := .inr 0

/-- The pair of initial padded column and row addresses. -/
def addrStart (I O : Type*) (sr sc : ℕ) [NeZero sr] [NeZero sc] : SparseAddr I O sr sc :=
  (colStart O sr, rowStart I sc)

/-- Row and column slot-position maps together with the complex entries of a matrix indexed by
`I` and `O`. -/
structure SparseAccess (I O : Type*) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (sr sc : ℕ) where

  rowPos : I → Fin sr → ColAddr O sr

  colPos : Fin sc → O → RowAddr I sc

  entry : I → O → ℂ

/-- Injective position maps enumerating exactly the nonzero entries, entry norms bounded by one,
and the specified row and column padding identities. -/
structure SparseAccessLegal (D : SparseAccess I O sr sc) : Prop where

  rowInjective : ∀ (i : I), Function.Injective (D.rowPos i)

  colInjective : ∀ (j : O), Function.Injective (fun c => D.colPos c j)

  rowLegal : ∀ (i : I) (k : Fin sr) (o : O), D.rowPos i k = .inl o → D.entry i o ≠ 0

  rowComplete : ∀ (i : I) (o : O), D.entry i o ≠ 0 → ∃ k, D.rowPos i k = .inl o

  colLegal : ∀ (j : O) (c : Fin sc) (i : I), D.colPos c j = .inl i → D.entry i j ≠ 0

  colComplete : ∀ (j : O) (i : I), D.entry i j ≠ 0 → ∃ c, D.colPos c j = .inl i

  entryBound : ∀ (i : I) (o : O), ‖D.entry i o‖ ≤ 1

  rowPad : ∀ (i : I) (k k' : Fin sr), D.rowPos i k = .inr k' → D.rowPos i k' = .inr k

  colPad : ∀ (j : O) (c c' : Fin sc), D.colPos c j = .inr c' → D.colPos c' j = .inr c'

/-- The complex matrix whose entries are those of the sparse-access data. -/
noncomputable def SparseAccess.matrix (D : SparseAccess I O sr sc) : Matrix I O ℂ :=
  fun i o => D.entry i o

/-- The real normalization factor `sqrt sr * sqrt sc` for sparse matrix encoding. -/
noncomputable def sparseAlpha (sr sc : ℕ) : ℝ := (Real.sqrt sr) * (Real.sqrt sc)

/-- The product of the complex embeddings of `sqrt sr` and `sqrt sc`. -/
noncomputable def sparseAlphaComplex (sr sc : ℕ) : ℂ :=
  (Real.sqrt sr : ℂ) * (Real.sqrt sc : ℂ)

/-- The sparse-access matrix divided entrywise by `sparseAlphaComplex sr sc`. -/
noncomputable def SparseAccess.encoded (D : SparseAccess I O sr sc) : Matrix I O ℂ :=
  fun i o => D.entry i o / sparseAlphaComplex sr sc

/-- The complex normalization equals the complex embedding of the real normalization. -/
theorem sparseAlphaComplex_eq (sr sc : ℕ) :
    sparseAlphaComplex sr sc = (sparseAlpha sr sc : ℂ) := by
  simp [sparseAlphaComplex, sparseAlpha, Complex.ofReal_mul]

/-- The number of row slots whose position map equals the given padded column address. -/
def rowSlotCount (D : SparseAccess I O sr sc) (i : I) (c : ColAddr O sr) : ℕ :=
  ∑ k, if D.rowPos i k = c then 1 else 0

/-- The number of column slots whose position map equals the given padded row address. -/
def colSlotCount (D : SparseAccess I O sr sc) (j : O) (r : RowAddr I sc) : ℕ :=
  ∑ c, if D.colPos c j = r then 1 else 0

/-- The column-address vector with amplitude `1 / sqrt sr` on each padding slot and zero on
actual column indices. -/
noncomputable def rowSlotUniform (O : Type*) (sr : ℕ) : ColAddr O sr → ℂ :=
  fun c => match c with
    | .inl _ => 0
    | .inr _ => (Real.sqrt sr : ℂ)⁻¹

/-- The row-address vector with amplitude `1 / sqrt sc` on each padding slot and zero on actual
row indices. -/
noncomputable def colSlotUniform (I : Type*) (sc : ℕ) : RowAddr I sc → ℂ :=
  fun r => match r with
    | .inl _ => 0
    | .inr _ => (Real.sqrt sc : ℂ)⁻¹

/-- The vector of row slot multiplicities scaled by `1 / sqrt sr`. -/
noncomputable def rowAddressVector (D : SparseAccess I O sr sc) (i : I) : ColAddr O sr → ℂ :=
  fun c => (Real.sqrt sr : ℂ)⁻¹ * ((rowSlotCount D i c : ℝ) : ℂ)

/-- The vector of column slot multiplicities scaled by `1 / sqrt sc`. -/
noncomputable def colAddressVector (D : SparseAccess I O sr sc) (j : O) : RowAddr I sc → ℂ :=
  fun r => (Real.sqrt sc : ℂ)⁻¹ * ((colSlotCount D j r : ℝ) : ℂ)

/-- The Boolean amplitude pair consisting of the matrix entry and its real square-root
complement on legal row addresses, and `(0, 1)` on padding. -/
noncomputable def colAmp (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc → Bool → ℂ :=
  fun r f => match r with
    | .inl i => if f then (Real.sqrt (1 - ‖D.entry i j‖ ^ 2) : ℂ) else D.entry i j
    | .inr _ => if f then 1 else 0

/-- The column slot multiplicity times the selected Boolean amplitude, scaled by `1 / sqrt sc`. -/
noncomputable def colValueSuperposition (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc × Bool → ℂ :=
  fun rf => match rf with
    | (r, f) => (Real.sqrt sc : ℂ)⁻¹ * ((colSlotCount D j r : ℝ) : ℂ) * (colAmp D j r f)

/-- The matrix entry associated with two actual indices, extended by zero whenever either
address is padded. -/
noncomputable def addrEntry (D : SparseAccess I O sr sc) (a : SparseAddr I O sr sc) : ℂ :=
  match a with
  | (.inl o, .inl i) => D.entry i o
  | _ => 0

/-- The predicate identifying actual column indices rather than padding slots. -/
def ColAddr.IsLegal {O : Type*} {sr : ℕ} : ColAddr O sr → Prop
  | .inl _ => True
  | .inr _ => False

/-- The predicate identifying actual row indices rather than padding slots. -/
def RowAddr.IsLegal {I : Type*} {sc : ℕ} : RowAddr I sc → Prop
  | .inl _ => True
  | .inr _ => False

/-- The number of row slots pointing to the specified actual column index. -/
def rowLegalCount (D : SparseAccess I O sr sc) (i : I) (o : O) : ℕ :=
  ∑ k, if D.rowPos i k = .inl o then 1 else 0

/-- The number of column slots pointing to the specified actual row index. -/
def colLegalCount (D : SparseAccess I O sr sc) (j : O) (i : I) : ℕ :=
  ∑ c, if D.colPos c j = .inl i then 1 else 0

/-- For legal data, the row slot multiplicity of an actual column is zero for a zero entry and
one otherwise. -/
theorem rowLegalCount_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) : rowLegalCount D i o = if D.entry i o = 0 then 0 else 1 := by
  classical
  by_cases hz : D.entry i o = 0
  · have hne : ∀ k, D.rowPos i k ≠ .inl o := by
      intro k hk
      exact (hD.rowLegal i k o hk) (by rw [hz])
    simp [rowLegalCount, hne, hz]
  · have hex : ∃ k, D.rowPos i k = .inl o := hD.rowComplete i o hz
    obtain ⟨k, hk⟩ := hex
    have hne : ∀ k', D.rowPos i k' = .inl o → k' = k := by
      intro k' hk'
      exact hD.rowInjective i (by rw [hk, hk'])
    have hsum : (∑ k', if D.rowPos i k' = .inl o then 1 else 0) = 1 := by
      rw [Fintype.sum_eq_single k]
      · simp [hk]
      · intro k' hk'
        rw [if_neg (fun e => hk' (hne k' e))]
    simp [rowLegalCount, hsum, hz]

/-- For legal data, the column slot multiplicity of an actual row is zero for a zero entry and
one otherwise. -/
theorem colLegalCount_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) : colLegalCount D j i = if D.entry i j = 0 then 0 else 1 := by
  classical
  by_cases hz : D.entry i j = 0
  · have hne : ∀ c, D.colPos c j ≠ .inl i := by
      intro c hc
      exact (hD.colLegal j c i hc) (by rw [hz])
    simp [colLegalCount, hne, hz]
  · have hex : ∃ c, D.colPos c j = .inl i := hD.colComplete j i hz
    obtain ⟨c, hc⟩ := hex
    have hne : ∀ c', D.colPos c' j = .inl i → c' = c := by
      intro c' hc'
      exact hD.colInjective j (by show D.colPos c' j = D.colPos c j; rw [hc', hc])
    have hsum : (∑ c', if D.colPos c' j = .inl i then 1 else 0) = 1 := by
      rw [Fintype.sum_eq_single c]
      · simp [hc]
      · intro c' hc'
        rw [if_neg (fun e => hc' (hne c' e))]
    simp [colLegalCount, hsum, hz]

/-- Every padded column address occurs in at most one row slot for legal data. -/
theorem rowSlotCount_le_one (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (c : ColAddr O sr) : rowSlotCount D i c ≤ 1 := by
  classical
  by_cases hex : ∃ k : Fin sr, D.rowPos i k = c
  · obtain ⟨k, hk⟩ := hex
    have hne : ∀ k' : Fin sr, D.rowPos i k' = c → k' = k := by
      intro k' hk'
      exact hD.rowInjective i (by rw [hk, hk'])
    have hpoint : ∀ k' : Fin sr, (if D.rowPos i k' = c then 1 else 0)
        = (if k' = k then 1 else 0) := by
      intro k'
      by_cases h : k' = k
      · simp [h, hk]
      · have hne' : ¬(D.rowPos i k' = c) := by
          intro e
          exact h (hne k' e)
        simp [hne', h]
    rw [rowSlotCount]
    simp only [hpoint]
    rw [Fintype.sum_eq_single k]
    · simp
    · intro k' hk'
      rw [if_neg hk']
  · have hpoint : ∀ k' : Fin sr, (if D.rowPos i k' = c then 1 else 0) = 0 := by
      intro k'
      have hne' : ¬(D.rowPos i k' = c) := by
        intro e
        exact hex ⟨k', e⟩
      simp [hne']
    rw [rowSlotCount]
    simp only [hpoint]
    simp

/-- Every padded row address occurs in at most one column slot for legal data. -/
theorem colSlotCount_le_one (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (r : RowAddr I sc) : colSlotCount D j r ≤ 1 := by
  classical
  by_cases hex : ∃ c : Fin sc, D.colPos c j = r
  · obtain ⟨c, hc⟩ := hex
    have hne : ∀ c' : Fin sc, D.colPos c' j = r → c' = c := by
      intro c' hc'
      exact hD.colInjective j (by show D.colPos c' j = D.colPos c j; rw [hc', hc])
    have hpoint : ∀ c' : Fin sc, (if D.colPos c' j = r then 1 else 0)
        = (if c' = c then 1 else 0) := by
      intro c'
      by_cases h : c' = c
      · simp [h, hc]
      · have hne' : ¬(D.colPos c' j = r) := by
          intro e
          exact h (hne c' e)
        simp [hne', h]
    rw [colSlotCount]
    simp only [hpoint]
    rw [Fintype.sum_eq_single c]
    · simp
    · intro c' hc'
      rw [if_neg hc']
  · have hpoint : ∀ c' : Fin sc, (if D.colPos c' j = r then 1 else 0) = 0 := by
      intro c'
      have hne' : ¬(D.colPos c' j = r) := by
        intro e
        exact hex ⟨c', e⟩
      simp [hne']
    rw [colSlotCount]
    simp only [hpoint]
    simp

/-- The total of the row slot multiplicities over all padded column addresses is `sr`. -/
theorem sum_rowSlotCount (D : SparseAccess I O sr sc) (i : I) :
    (∑ c : ColAddr O sr, rowSlotCount D i c) = sr := by
  classical
  have hsum : (∑ c : ColAddr O sr, ∑ k : Fin sr, (if D.rowPos i k = c then 1 else 0))
      = ∑ k : Fin sr, ∑ c : ColAddr O sr, (if D.rowPos i k = c then 1 else 0) := by
    exact Finset.sum_comm
  have hmain : (∑ c : ColAddr O sr, rowSlotCount D i c)
      = ∑ c : ColAddr O sr, ∑ k : Fin sr, (if D.rowPos i k = c then 1 else 0) := by
    congr 1
  rw [hmain, hsum]
  have h1 : ∀ k : Fin sr, (∑ c : ColAddr O sr, (if D.rowPos i k = c then 1 else 0)) = 1 := by
    intro k
    rw [Fintype.sum_eq_single (D.rowPos i k)]
    · simp
    · intro c hc
      rw [if_neg (fun e => hc e.symm)]
  rw [Fintype.sum_congr _ _ h1]
  simp

/-- The total of the column slot multiplicities over all padded row addresses is `sc`. -/
theorem sum_colSlotCount (D : SparseAccess I O sr sc) (j : O) :
    (∑ r : RowAddr I sc, colSlotCount D j r) = sc := by
  classical
  have hsum : (∑ r : RowAddr I sc, ∑ c : Fin sc, (if D.colPos c j = r then 1 else 0))
      = ∑ c : Fin sc, ∑ r : RowAddr I sc, (if D.colPos c j = r then 1 else 0) := by
    exact Finset.sum_comm
  have hmain : (∑ r : RowAddr I sc, colSlotCount D j r)
      = ∑ r : RowAddr I sc, ∑ c : Fin sc, (if D.colPos c j = r then 1 else 0) := by
    congr 1
  rw [hmain, hsum]
  have h1 : ∀ c : Fin sc, (∑ r : RowAddr I sc, (if D.colPos c j = r then 1 else 0)) = 1 := by
    intro c
    rw [Fintype.sum_eq_single (D.colPos c j)]
    · simp
    · intro r hr
      rw [if_neg (fun e => hr e.symm)]
  rw [Fintype.sum_congr _ _ h1]
  simp

/-- The symbolic uniform-preparation, position-oracle, value-oracle, inverse-oracle, and
amplitude-gate steps used in sparse access. -/
inductive SparseAccessStep where

  | rowUniform : SparseAccessStep

  | rowOracle : SparseAccessStep

  | rowOracleInv : SparseAccessStep

  | colUniform : SparseAccessStep

  | colOracle : SparseAccessStep

  | colOracleInv : SparseAccessStep

  | valueQuery : SparseAccessStep

  | valueUnquery : SparseAccessStep

  | amplitudeGate : SparseAccessStep

/-- The row-oracle query cost of a step, equal to one for a row query or its inverse and zero
otherwise. -/
def SparseAccessStep.rowQueries : SparseAccessStep → ℕ
  | .rowOracle => 1
  | .rowOracleInv => 1
  | _ => 0

/-- The column-oracle query cost of a step, equal to one for a column query or its inverse and
zero otherwise. -/
def SparseAccessStep.colQueries : SparseAccessStep → ℕ
  | .colOracle => 1
  | .colOracleInv => 1
  | _ => 0

/-- The value-oracle query cost of a step, counting both a query and its inverse. -/
def SparseAccessStep.valueQueries : SparseAccessStep → ℕ
  | .valueQuery => 1
  | .valueUnquery => 1
  | _ => 0

/-- The gate-step cost, counting row and column uniform preparations and the amplitude gate. -/
def SparseAccessStep.gateCount : SparseAccessStep → ℕ
  | .rowUniform => 1
  | .colUniform => 1
  | .amplitudeGate => 1
  | _ => 0

/-- The symbolic left preparation consisting of a row-uniform step followed by a row-oracle
query. -/
def leftPrepWord : List SparseAccessStep := [.rowUniform, .rowOracle]

/-- The symbolic inverse left preparation consisting of an inverse row query followed by the
row-uniform step. -/
def leftPrepWordInv : List SparseAccessStep := [.rowOracleInv, .rowUniform]

/-- The symbolic right preparation consisting of column preparation and query, value query,
amplitude gate, and value unquery. -/
def rightPrepWord : List SparseAccessStep :=
  [.colUniform, .colOracle, .valueQuery, .amplitudeGate, .valueUnquery]

/-- The concatenation of the inverse left preparation word and the right preparation word. -/
def encodingWord : List SparseAccessStep := leftPrepWordInv ++ rightPrepWord

/-- The total row-oracle query cost of a sparse-access word. -/
def rowQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.rowQueries + rowQueryCount ss

/-- The total column-oracle query cost of a sparse-access word. -/
def colQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.colQueries + colQueryCount ss

/-- The total value-oracle query and unquery cost of a sparse-access word. -/
def valueQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.valueQueries + valueQueryCount ss

/-- The total uniform-preparation and amplitude-gate step count of a sparse-access word. -/
def gateStepCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.gateCount + gateStepCount ss

/-- A record of row-query, column-query, value-query, and gate counts. -/
structure PointUsage where

  rowQueries : ℕ

  colQueries : ℕ

  valueQueries : ℕ

  gateCount : ℕ
  deriving DecidableEq, Repr

/-- Choose the row slot that points to a given nonzero matrix entry using completeness of legal
sparse-access data. -/
noncomputable def rowSlotOf (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) : Fin sr :=
  Classical.choose (hD.rowComplete i j hne)

/-- The chosen row slot points to the column index of the specified nonzero entry. -/
theorem rowSlotOf_pos (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    D.rowPos i (rowSlotOf D hD i j hne) = .inl j :=
  Classical.choose_spec (hD.rowComplete i j hne)

/-- Every row slot pointing to the given nonzero entry equals the chosen row slot. -/
theorem rowSlotOf_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) (k : Fin sr) (hk : D.rowPos i k = .inl j) :
    k = rowSlotOf D hD i j hne := by
  refine hD.rowInjective i ?_
  rw [hk, rowSlotOf_pos D hD i j hne]

/-- Choose the column slot that points to a given nonzero matrix entry using completeness of
legal sparse-access data. -/
noncomputable def colSlotOf (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) : Fin sc :=
  Classical.choose (hD.colComplete j i hne)

/-- The chosen column slot points to the row index of the specified nonzero entry. -/
theorem colSlotOf_pos (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) :
    D.colPos (colSlotOf D hD j i hne) j = .inl i :=
  Classical.choose_spec (hD.colComplete j i hne)

/-- Every column slot pointing to the given nonzero entry equals the chosen column slot. -/
theorem colSlotOf_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) (c : Fin sc) (hc : D.colPos c j = .inl i) :
    c = colSlotOf D hD j i hne := by
  refine hD.colInjective j ?_
  show D.colPos c j = D.colPos (colSlotOf D hD j i hne) j
  rw [hc, colSlotOf_pos D hD j i hne]

/-- The entrywise usage record computed from legal-address multiplicities, with two base gate
steps and an additional amplitude step when the row multiplicity is nonzero. -/
def pointUsage (D : SparseAccess I O sr sc) (i : I) (j : O) :
    PointUsage where
  rowQueries := rowLegalCount D i j
  colQueries := colLegalCount D j i
  valueQueries := 2 * (if rowLegalCount D i j = 0 then 0 else 1)
  gateCount := 2 + (if rowLegalCount D i j = 0 then 0 else 1)

/-- The resource record with one row query, one column query, two value queries, and three gate
steps. -/
def encodingWordUsage : PointUsage where
  rowQueries := 1
  colQueries := 1
  valueQueries := 2
  gateCount := 3

/-- Each field of `encodingWordUsage` equals the corresponding resource count computed from
`encodingWord`. -/
theorem encodingWord_usage_counts :
    (encodingWordUsage).rowQueries = rowQueryCount encodingWord ∧
      (encodingWordUsage).colQueries = colQueryCount encodingWord ∧
      (encodingWordUsage).valueQueries = valueQueryCount encodingWord ∧
      (encodingWordUsage).gateCount = gateStepCount encodingWord := by
  decide

/-- For a nonzero entry of legal sparse-access data, the entrywise usage equals
`encodingWordUsage`. -/
theorem pointUsage_eq_encodingWordUsage (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    pointUsage D i j = encodingWordUsage := by
  have hrow := rowLegalCount_eq D hD i j
  have hcol := colLegalCount_eq D hD j i
  simp [pointUsage, encodingWordUsage, hrow, hcol, hne]

/-- For a zero entry of legal sparse-access data, the entrywise usage has no queries and two
gate steps. -/
theorem pointUsage_eq_zero (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hz : D.entry i j = 0) :
    pointUsage D i j = ⟨0, 0, 0, 2⟩ := by
  have hrow := rowLegalCount_eq D hD i j
  have hcol := colLegalCount_eq D hD j i
  simp [pointUsage, hrow, hcol, hz]

/-- For a legal nonzero entry, its usage agrees with the encoding-word record and all four
fields agree with the word's computed counts. -/
theorem encodingWord_ledger_eq_pointUsage (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    pointUsage D i j = encodingWordUsage ∧
      (encodingWordUsage).rowQueries = rowQueryCount encodingWord ∧
      (encodingWordUsage).colQueries = colQueryCount encodingWord ∧
      (encodingWordUsage).valueQueries = valueQueryCount encodingWord ∧
      (encodingWordUsage).gateCount = gateStepCount encodingWord := by
  refine ⟨pointUsage_eq_encodingWordUsage D hD i j hne, ?_, ?_, ?_, ?_⟩
  all_goals decide

/-- For a legal nonzero entry, the chosen row and column slots return its two indices, and its
value remains nonzero. -/
theorem point_oracle_answers (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    D.rowPos i (rowSlotOf D hD i j hne) = .inl j ∧
      D.colPos (colSlotOf D hD j i hne) j = .inl i ∧
      D.entry i j ≠ 0 :=
  ⟨rowSlotOf_pos D hD i j hne, colSlotOf_pos D hD j i hne, hne⟩

/-- The left preparation word uses exactly one row-oracle query. -/
theorem leftPrepWord_rowQueries : rowQueryCount leftPrepWord = 1 := by
  rfl

/-- The right preparation word uses exactly one column-oracle query. -/
theorem rightPrepWord_colQueries : colQueryCount rightPrepWord = 1 := by
  rfl

/-- The right preparation word uses exactly two value-oracle queries, including the unquery. -/
theorem rightPrepWord_valueQueries : valueQueryCount rightPrepWord = 2 := by
  rfl

/-- The encoding word has one row query, one column query, two value queries, and three gate
steps. -/
theorem encodingWord_ledger :
    rowQueryCount encodingWord = 1 ∧ colQueryCount encodingWord = 1 ∧
      valueQueryCount encodingWord = 2 ∧ gateStepCount encodingWord = 3 := by
  decide

end Qatlib.Concepts.QsvtCore.PhaseExistence
