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
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

set_option autoImplicit false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {sr sc : ℕ}

abbrev ColAddr (O : Type*) (sr : ℕ) := O ⊕ Fin sr

abbrev RowAddr (I : Type*) (sc : ℕ) := I ⊕ Fin sc

abbrev SparseAddr (I O : Type*) (sr sc : ℕ) := ColAddr O sr × RowAddr I sc

abbrev SparseWorkspace (I O : Type*) (sr sc : ℕ) :=
  ColAddr O sr × (RowAddr I sc × Bool)

def colStart (O : Type*) (sr : ℕ) [NeZero sr] : ColAddr O sr := .inr 0

def rowStart (I : Type*) (sc : ℕ) [NeZero sc] : RowAddr I sc := .inr 0

def addrStart (I O : Type*) (sr sc : ℕ) [NeZero sr] [NeZero sc] : SparseAddr I O sr sc :=
  (colStart O sr, rowStart I sc)

structure SparseAccess (I O : Type*) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (sr sc : ℕ) where

  rowPos : I → Fin sr → ColAddr O sr

  colPos : Fin sc → O → RowAddr I sc

  entry : I → O → ℂ

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

noncomputable def SparseAccess.matrix (D : SparseAccess I O sr sc) : Matrix I O ℂ :=
  fun i o => D.entry i o

noncomputable def sparseAlpha (sr sc : ℕ) : ℝ := (Real.sqrt sr) * (Real.sqrt sc)

noncomputable def sparseAlphaComplex (sr sc : ℕ) : ℂ :=
  (Real.sqrt sr : ℂ) * (Real.sqrt sc : ℂ)

noncomputable def SparseAccess.encoded (D : SparseAccess I O sr sc) : Matrix I O ℂ :=
  fun i o => D.entry i o / sparseAlphaComplex sr sc

theorem sparseAlphaComplex_eq (sr sc : ℕ) :
    sparseAlphaComplex sr sc = (sparseAlpha sr sc : ℂ) := by
  simp [sparseAlphaComplex, sparseAlpha, Complex.ofReal_mul]

def rowSlotCount (D : SparseAccess I O sr sc) (i : I) (c : ColAddr O sr) : ℕ :=
  ∑ k, if D.rowPos i k = c then 1 else 0

def colSlotCount (D : SparseAccess I O sr sc) (j : O) (r : RowAddr I sc) : ℕ :=
  ∑ c, if D.colPos c j = r then 1 else 0

noncomputable def rowSlotUniform (O : Type*) (sr : ℕ) : ColAddr O sr → ℂ :=
  fun c => match c with
    | .inl _ => 0
    | .inr _ => (Real.sqrt sr : ℂ)⁻¹

noncomputable def colSlotUniform (I : Type*) (sc : ℕ) : RowAddr I sc → ℂ :=
  fun r => match r with
    | .inl _ => 0
    | .inr _ => (Real.sqrt sc : ℂ)⁻¹

noncomputable def rowAddressVector (D : SparseAccess I O sr sc) (i : I) : ColAddr O sr → ℂ :=
  fun c => (Real.sqrt sr : ℂ)⁻¹ * ((rowSlotCount D i c : ℝ) : ℂ)

noncomputable def colAddressVector (D : SparseAccess I O sr sc) (j : O) : RowAddr I sc → ℂ :=
  fun r => (Real.sqrt sc : ℂ)⁻¹ * ((colSlotCount D j r : ℝ) : ℂ)

noncomputable def colAmp (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc → Bool → ℂ :=
  fun r f => match r with
    | .inl i => if f then (Real.sqrt (1 - ‖D.entry i j‖ ^ 2) : ℂ) else D.entry i j
    | .inr _ => if f then 1 else 0

noncomputable def colValueSuperposition (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc × Bool → ℂ :=
  fun rf => match rf with
    | (r, f) => (Real.sqrt sc : ℂ)⁻¹ * ((colSlotCount D j r : ℝ) : ℂ) * (colAmp D j r f)

noncomputable def addrEntry (D : SparseAccess I O sr sc) (a : SparseAddr I O sr sc) : ℂ :=
  match a with
  | (.inl o, .inl i) => D.entry i o
  | _ => 0

def ColAddr.IsLegal {O : Type*} {sr : ℕ} : ColAddr O sr → Prop
  | .inl _ => True
  | .inr _ => False

def RowAddr.IsLegal {I : Type*} {sc : ℕ} : RowAddr I sc → Prop
  | .inl _ => True
  | .inr _ => False

def rowLegalCount (D : SparseAccess I O sr sc) (i : I) (o : O) : ℕ :=
  ∑ k, if D.rowPos i k = .inl o then 1 else 0

def colLegalCount (D : SparseAccess I O sr sc) (j : O) (i : I) : ℕ :=
  ∑ c, if D.colPos c j = .inl i then 1 else 0

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

def SparseAccessStep.rowQueries : SparseAccessStep → ℕ
  | .rowOracle => 1
  | .rowOracleInv => 1
  | _ => 0

def SparseAccessStep.colQueries : SparseAccessStep → ℕ
  | .colOracle => 1
  | .colOracleInv => 1
  | _ => 0

def SparseAccessStep.valueQueries : SparseAccessStep → ℕ
  | .valueQuery => 1
  | .valueUnquery => 1
  | _ => 0

def SparseAccessStep.gateCount : SparseAccessStep → ℕ
  | .rowUniform => 1
  | .colUniform => 1
  | .amplitudeGate => 1
  | _ => 0

def leftPrepWord : List SparseAccessStep := [.rowUniform, .rowOracle]

def leftPrepWordInv : List SparseAccessStep := [.rowOracleInv, .rowUniform]

def rightPrepWord : List SparseAccessStep :=
  [.colUniform, .colOracle, .valueQuery, .amplitudeGate, .valueUnquery]

def encodingWord : List SparseAccessStep := leftPrepWordInv ++ rightPrepWord

def rowQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.rowQueries + rowQueryCount ss

def colQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.colQueries + colQueryCount ss

def valueQueryCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.valueQueries + valueQueryCount ss

def gateStepCount : List SparseAccessStep → ℕ
  | [] => 0
  | s :: ss => s.gateCount + gateStepCount ss

structure PointUsage where

  rowQueries : ℕ

  colQueries : ℕ

  valueQueries : ℕ

  gateCount : ℕ
  deriving DecidableEq, Repr

noncomputable def rowSlotOf (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) : Fin sr :=
  Classical.choose (hD.rowComplete i j hne)

theorem rowSlotOf_pos (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    D.rowPos i (rowSlotOf D hD i j hne) = .inl j :=
  Classical.choose_spec (hD.rowComplete i j hne)

theorem rowSlotOf_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) (k : Fin sr) (hk : D.rowPos i k = .inl j) :
    k = rowSlotOf D hD i j hne := by
  refine hD.rowInjective i ?_
  rw [hk, rowSlotOf_pos D hD i j hne]

noncomputable def colSlotOf (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) : Fin sc :=
  Classical.choose (hD.colComplete j i hne)

theorem colSlotOf_pos (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) :
    D.colPos (colSlotOf D hD j i hne) j = .inl i :=
  Classical.choose_spec (hD.colComplete j i hne)

theorem colSlotOf_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) (c : Fin sc) (hc : D.colPos c j = .inl i) :
    c = colSlotOf D hD j i hne := by
  refine hD.colInjective j ?_
  show D.colPos c j = D.colPos (colSlotOf D hD j i hne) j
  rw [hc, colSlotOf_pos D hD j i hne]

def pointUsage (D : SparseAccess I O sr sc) (i : I) (j : O) :
    PointUsage where
  rowQueries := rowLegalCount D i j
  colQueries := colLegalCount D j i
  valueQueries := 2 * (if rowLegalCount D i j = 0 then 0 else 1)
  gateCount := 2 + (if rowLegalCount D i j = 0 then 0 else 1)

def encodingWordUsage : PointUsage where
  rowQueries := 1
  colQueries := 1
  valueQueries := 2
  gateCount := 3

theorem encodingWord_usage_counts :
    (encodingWordUsage).rowQueries = rowQueryCount encodingWord ∧
      (encodingWordUsage).colQueries = colQueryCount encodingWord ∧
      (encodingWordUsage).valueQueries = valueQueryCount encodingWord ∧
      (encodingWordUsage).gateCount = gateStepCount encodingWord := by
  decide

theorem pointUsage_eq_encodingWordUsage (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    pointUsage D i j = encodingWordUsage := by
  have hrow := rowLegalCount_eq D hD i j
  have hcol := colLegalCount_eq D hD j i
  simp [pointUsage, encodingWordUsage, hrow, hcol, hne]

theorem pointUsage_eq_zero (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hz : D.entry i j = 0) :
    pointUsage D i j = ⟨0, 0, 0, 2⟩ := by
  have hrow := rowLegalCount_eq D hD i j
  have hcol := colLegalCount_eq D hD j i
  simp [pointUsage, hrow, hcol, hz]

theorem encodingWord_ledger_eq_pointUsage (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    pointUsage D i j = encodingWordUsage ∧
      (encodingWordUsage).rowQueries = rowQueryCount encodingWord ∧
      (encodingWordUsage).colQueries = colQueryCount encodingWord ∧
      (encodingWordUsage).valueQueries = valueQueryCount encodingWord ∧
      (encodingWordUsage).gateCount = gateStepCount encodingWord := by
  refine ⟨pointUsage_eq_encodingWordUsage D hD i j hne, ?_, ?_, ?_, ?_⟩
  all_goals decide

theorem point_oracle_answers (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (j : O) (hne : D.entry i j ≠ 0) :
    D.rowPos i (rowSlotOf D hD i j hne) = .inl j ∧
      D.colPos (colSlotOf D hD j i hne) j = .inl i ∧
      D.entry i j ≠ 0 :=
  ⟨rowSlotOf_pos D hD i j hne, colSlotOf_pos D hD j i hne, hne⟩

theorem leftPrepWord_rowQueries : rowQueryCount leftPrepWord = 1 := by
  rfl

theorem rightPrepWord_colQueries : colQueryCount rightPrepWord = 1 := by
  rfl

theorem rightPrepWord_valueQueries : valueQueryCount rightPrepWord = 2 := by
  rfl

theorem encodingWord_ledger :
    rowQueryCount encodingWord = 1 ∧ colQueryCount encodingWord = 1 ∧
      valueQueryCount encodingWord = 2 ∧ gateStepCount encodingWord = 3 := by
  decide

end Qatlib.Concepts.QsvtCore.PhaseExistence
