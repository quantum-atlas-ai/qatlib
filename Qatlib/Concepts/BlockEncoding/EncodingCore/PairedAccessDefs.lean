/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.PairedPrepareAccess
import Qatlib.Concepts.OperatorAccess.EncodedAccess
import Qatlib.Concepts.QsvtCore.PhaseExistence.SparseAccessConstruction
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {sr sc : ℕ}

theorem colSlot_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) (j : O)
    (c c' : Fin sc) (h : D.colPos c j = D.colPos c' j) : c = c' :=
  hD.colInjective j h

theorem rowSlot_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) (i : I)
    (k k' : Fin sr) (h : D.rowPos i k = D.rowPos i k') : k = k' :=
  hD.rowInjective i h

noncomputable def rowSlotOfAddr (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) : Fin sr :=
  Classical.choose h

@[simp] theorem rowSlotOfAddr_pos (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) :
    D.rowPos i (rowSlotOfAddr D i o h) = .inl o :=
  Classical.choose_spec h

theorem rowSlotOfAddr_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) (k : Fin sr)
    (hk : D.rowPos i k = .inl o) : k = rowSlotOfAddr D i o h := by
  refine hD.rowInjective i ?_
  rw [hk, rowSlotOfAddr_pos D i o h]

noncomputable def rowTableFun (D : SparseAccess I O sr sc) (i : I) :
    ColAddr O sr → ColAddr O sr
  | .inl o =>
      if h : ∃ kx : Fin sr, D.rowPos i kx = .inl o then .inr (rowSlotOfAddr D i o h)
      else .inl o
  | .inr k => D.rowPos i k

@[simp] theorem rowTableFun_inr (D : SparseAccess I O sr sc) (i : I) (k : Fin sr) :
    rowTableFun D i (.inr k) = D.rowPos i k := rfl

theorem rowTableFun_inl (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) :
    rowTableFun D i (.inl o) = .inr (rowSlotOfAddr D i o h) := by
  simp [rowTableFun, dif_pos h]

theorem rowTableFun_inl_of_not (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ¬ (∃ kx : Fin sr, D.rowPos i kx = .inl o)) :
    rowTableFun D i (.inl o) = .inl o := by
  simp [rowTableFun, dif_neg h]

theorem rowPad_reciprocal (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (k k' : Fin sr) (hk : D.rowPos i k = .inr k') :
    D.rowPos i k' = .inr k := hD.rowPad i k k' hk

theorem rowTableFun_injective (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) : Function.Injective (rowTableFun D i) := by
  intro x y hxy
  cases x with
  | inl o =>
    cases y with
    | inl o' =>
      by_cases h : ∃ kx : Fin sr, D.rowPos i kx = .inl o
      · by_cases h' : ∃ kx : Fin sr, D.rowPos i kx = .inl o'
        · rw [rowTableFun_inl D i o h, rowTableFun_inl D i o' h'] at hxy
          injection hxy with hslot
          have hpos := rowSlotOfAddr_pos D i o h
          have hpos' := rowSlotOfAddr_pos D i o' h'
          rw [hslot] at hpos
          have h2 : (.inl o : ColAddr O sr) = .inl o' := hpos.symm.trans hpos'
          injection h2 with h2
          exact congrArg Sum.inl h2
        · rw [rowTableFun_inl D i o h, rowTableFun_inl_of_not D i o' h'] at hxy
          exact absurd hxy (by simp)
      · by_cases h' : ∃ kx : Fin sr, D.rowPos i kx = .inl o'
        · rw [rowTableFun_inl_of_not D i o h, rowTableFun_inl D i o' h'] at hxy
          exact absurd hxy (by simp)
        · rw [rowTableFun_inl_of_not D i o h, rowTableFun_inl_of_not D i o' h'] at hxy
          exact hxy
    | inr k' =>
      by_cases h : ∃ kx : Fin sr, D.rowPos i kx = .inl o
      · rw [rowTableFun_inl D i o h, rowTableFun_inr] at hxy
        have hk' : D.rowPos i k' = .inr (rowSlotOfAddr D i o h) := hxy.symm
        have hrec := rowPad_reciprocal D hD i k' (rowSlotOfAddr D i o h) hk'
        have hpos := rowSlotOfAddr_pos D i o h
        rw [hrec] at hpos
        exact absurd hpos (by simp)
      · rw [rowTableFun_inl_of_not D i o h, rowTableFun_inr] at hxy
        exact absurd hxy.symm (fun hk => h ⟨k', hk⟩)
  | inr k =>
    cases y with
    | inl o' =>
      by_cases h : ∃ kx : Fin sr, D.rowPos i kx = .inl o'
      · rw [rowTableFun_inr, rowTableFun_inl D i o' h] at hxy
        have hk : D.rowPos i k = .inr (rowSlotOfAddr D i o' h) := hxy
        have hrec := rowPad_reciprocal D hD i k (rowSlotOfAddr D i o' h) hk
        have hpos := rowSlotOfAddr_pos D i o' h
        rw [hrec] at hpos
        exact absurd hpos (by simp)
      · rw [rowTableFun_inr, rowTableFun_inl_of_not D i o' h] at hxy
        exact absurd hxy (fun hk => h ⟨k, hk⟩)
    | inr k' =>
      rw [rowTableFun_inr, rowTableFun_inr] at hxy
      exact congrArg Sum.inr (rowSlot_eq D hD i k k' hxy)

theorem rowTableFun_surjective (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) : Function.Surjective (rowTableFun D i) := by
  intro y
  cases y with
  | inl o =>
    by_cases h : ∃ kx : Fin sr, D.rowPos i kx = .inl o
    · refine ⟨.inr (rowSlotOfAddr D i o h), ?_⟩
      rw [rowTableFun_inr, rowSlotOfAddr_pos D i o h]
    · refine ⟨.inl o, ?_⟩
      exact rowTableFun_inl_of_not D i o h
  | inr k =>
    by_cases h : ∃ kx : Fin sr, D.rowPos i kx = .inr k
    · obtain ⟨kx, hkx⟩ := h
      refine ⟨.inr kx, ?_⟩
      rw [rowTableFun_inr, hkx]
    · by_cases h2 : ∃ o : O, D.rowPos i k = .inl o
      · obtain ⟨o, hko⟩ := h2
        refine ⟨.inl o, ?_⟩
        rw [rowTableFun_inl D i o ⟨k, hko⟩]
        have hslot : rowSlotOfAddr D i o ⟨k, hko⟩ = k :=
          (rowSlotOfAddr_unique D hD i o ⟨k, hko⟩ k hko).symm
        rw [hslot]
      · exfalso
        have hk' : ∃ kx : Fin sr, D.rowPos i k = .inr kx := by
          cases hk : D.rowPos i k with
          | inl o => exact absurd hk (fun ho => h2 ⟨o, ho⟩)
          | inr kx => exact ⟨kx, rfl⟩
        obtain ⟨kx, hkx⟩ := hk'
        have hrec := rowPad_reciprocal D hD i k kx hkx
        exact absurd ⟨kx, hrec⟩ h

noncomputable def rowTable (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) : ColAddr O sr ≃ ColAddr O sr :=
  Equiv.ofBijective (rowTableFun D i)
    ⟨rowTableFun_injective D hD i, rowTableFun_surjective D hD i⟩

noncomputable def colSlotOfAddr (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) : Fin sc :=
  Classical.choose h

@[simp] theorem colSlotOfAddr_pos (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) :
    D.colPos (colSlotOfAddr D j i h) j = .inl i :=
  Classical.choose_spec h

theorem colSlotOfAddr_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) (c : Fin sc)
    (hc : D.colPos c j = .inl i) : c = colSlotOfAddr D j i h := by
  refine colSlot_eq D hD j c (colSlotOfAddr D j i h) ?_
  rw [hc, colSlotOfAddr_pos D j i h]

noncomputable def colTableFun (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc → RowAddr I sc
  | .inl i =>
      if h : ∃ cx : Fin sc, D.colPos cx j = .inl i then .inr (colSlotOfAddr D j i h)
      else .inl i
  | .inr c => D.colPos c j

@[simp] theorem colTableFun_inr (D : SparseAccess I O sr sc) (j : O) (c : Fin sc) :
    colTableFun D j (.inr c) = D.colPos c j := rfl

theorem colTableFun_inl (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) :
    colTableFun D j (.inl i) = .inr (colSlotOfAddr D j i h) := by
  simp [colTableFun, dif_pos h]

theorem colTableFun_inl_of_not (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ¬ (∃ cx : Fin sc, D.colPos cx j = .inl i)) :
    colTableFun D j (.inl i) = .inl i := by
  simp [colTableFun, dif_neg h]

theorem colPad_fixed (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (c c' : Fin sc) (hc : D.colPos c j = .inr c') : D.colPos c j = .inr c := by
  have hrec := hD.colPad j c c' hc
  have hinj : c = c' := colSlot_eq D hD j c c' (by rw [hc, hrec])
  rw [← hinj] at hc
  exact hc

theorem colTableFun_injective (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) : Function.Injective (colTableFun D j) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl i' =>
      by_cases h : ∃ cx : Fin sc, D.colPos cx j = .inl i
      · by_cases h' : ∃ cx : Fin sc, D.colPos cx j = .inl i'
        · rw [colTableFun_inl D j i h, colTableFun_inl D j i' h'] at hxy
          injection hxy with hslot
          have hpos := colSlotOfAddr_pos D j i h
          have hpos' := colSlotOfAddr_pos D j i' h'
          rw [hslot] at hpos
          have h2 : (.inl i : RowAddr I sc) = .inl i' := hpos.symm.trans hpos'
          injection h2 with h2
          exact congrArg Sum.inl h2
        · rw [colTableFun_inl D j i h, colTableFun_inl_of_not D j i' h'] at hxy
          exact absurd hxy (by simp)
      · by_cases h' : ∃ cx : Fin sc, D.colPos cx j = .inl i'
        · rw [colTableFun_inl_of_not D j i h, colTableFun_inl D j i' h'] at hxy
          exact absurd hxy (by simp)
        · rw [colTableFun_inl_of_not D j i h, colTableFun_inl_of_not D j i' h'] at hxy
          exact hxy
    | inr c' =>
      by_cases h : ∃ cx : Fin sc, D.colPos cx j = .inl i
      · rw [colTableFun_inl D j i h, colTableFun_inr] at hxy
        have hc' : D.colPos c' j = .inr (colSlotOfAddr D j i h) := hxy.symm
        have hfix := colPad_fixed D hD j c' (colSlotOfAddr D j i h) hc'
        have hslot : colSlotOfAddr D j i h = c' := by
          injection hfix.symm.trans hc' with hslot
          exact hslot.symm
        have hpos := colSlotOfAddr_pos D j i h
        rw [hslot] at hpos
        exact absurd (hc'.symm.trans hpos) (by simp)
      · rw [colTableFun_inl_of_not D j i h, colTableFun_inr] at hxy
        exact absurd hxy.symm (fun hk => h ⟨c', hk⟩)
  | inr c =>
    cases y with
    | inl i' =>
      by_cases h : ∃ cx : Fin sc, D.colPos cx j = .inl i'
      · rw [colTableFun_inr, colTableFun_inl D j i' h] at hxy
        have hc : D.colPos c j = .inr (colSlotOfAddr D j i' h) := hxy
        have hfix := colPad_fixed D hD j c (colSlotOfAddr D j i' h) hc
        have hslot : colSlotOfAddr D j i' h = c := by
          injection hfix.symm.trans hc with hslot
          exact hslot.symm
        have hpos := colSlotOfAddr_pos D j i' h
        rw [hslot] at hpos
        exact absurd (hc.symm.trans hpos) (by simp)
      · rw [colTableFun_inr, colTableFun_inl_of_not D j i' h] at hxy
        exact absurd hxy (fun hk => h ⟨c, hk⟩)
    | inr c' =>
      rw [colTableFun_inr, colTableFun_inr] at hxy
      exact congrArg Sum.inr (colSlot_eq D hD j c c' hxy)

theorem colTableFun_surjective (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) : Function.Surjective (colTableFun D j) := by
  intro y
  cases y with
  | inl i =>
    by_cases h : ∃ cx : Fin sc, D.colPos cx j = .inl i
    · refine ⟨.inr (colSlotOfAddr D j i h), ?_⟩
      rw [colTableFun_inr, colSlotOfAddr_pos D j i h]
    · refine ⟨.inl i, ?_⟩
      exact colTableFun_inl_of_not D j i h
  | inr c =>
    by_cases h : ∃ cx : Fin sc, D.colPos cx j = .inr c
    · obtain ⟨cx, hcx⟩ := h
      refine ⟨.inr cx, ?_⟩
      rw [colTableFun_inr, hcx]
    · by_cases h2 : ∃ i : I, D.colPos c j = .inl i
      · obtain ⟨i, hci⟩ := h2
        refine ⟨.inl i, ?_⟩
        rw [colTableFun_inl D j i ⟨c, hci⟩]
        have hslot : colSlotOfAddr D j i ⟨c, hci⟩ = c :=
          (colSlotOfAddr_unique D hD j i ⟨c, hci⟩ c hci).symm
        rw [hslot]
      · exfalso
        have hc' : ∃ cx : Fin sc, D.colPos c j = .inr cx := by
          cases hcx : D.colPos c j with
          | inl i => exact absurd hcx (fun hi => h2 ⟨i, hi⟩)
          | inr cx => exact ⟨cx, rfl⟩
        obtain ⟨cx, hcx⟩ := hc'
        have hfix := colPad_fixed D hD j c cx hcx
        exact absurd ⟨c, hfix⟩ h

noncomputable def colTable (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) : RowAddr I sc ≃ RowAddr I sc :=
  Equiv.ofBijective (colTableFun D j)
    ⟨colTableFun_injective D hD j, colTableFun_surjective D hD j⟩

def rowLookup (D : SparseAccess I O sr sc) (i : I) (k : Fin sr) : ColAddr O sr :=
  D.rowPos i k

noncomputable def rowUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) : Option (Fin sr) :=
  if h : D.entry i o = 0 then none
  else some (rowSlotOf D hD i o h)

def colLookup (D : SparseAccess I O sr sc) (j : O) (c : Fin sc) : RowAddr I sc :=
  D.colPos c j

noncomputable def colUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) : Option (Fin sc) :=
  if h : D.entry i j = 0 then none
  else some (colSlotOf D hD j i h)

noncomputable def rowUniformPrep {O : Type*} [Fintype O] (sr : ℕ) (hsr : 0 < sr) :
    Matrix (ColAddr O sr) (ColAddr O sr) ℂ :=
  complexPrepare (rowSlotUniform O sr) (colScratch O sr hsr)

noncomputable def colUniformPrep {I : Type*} [Fintype I] (sc : ℕ) (hsc : 0 < sc) :
    Matrix (RowAddr I sc) (RowAddr I sc) ℂ :=
  complexPrepare (colSlotUniform I sc) (rowScratch I sc hsc)

noncomputable def ampGateAt (D : SparseAccess I O sr sc) (j : O) (i : I) :
    Matrix Bool Bool ℂ :=
  ampGate (D.entry i j)

noncomputable def ampGateBlock (D : SparseAccess I O sr sc) (j : O) :
    Matrix (RowAddr I sc × Bool) (RowAddr I sc × Bool) ℂ :=
  blockDiagFirst (fun r => match r with
    | .inl i => ampGateAt D j i
    | .inr _ => ampGate 0)

noncomputable def colUniformOp (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun _ => TensorGate (colUniformPrep (I := I) sc hsc)
    (1 : Matrix Bool Bool ℂ))

noncomputable def colOracleOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => TensorGate (permMatrix (colTable D hD j)) (1 : Matrix Bool Bool ℂ)
    | .inr _ => 1)

noncomputable def ampGateOp (D : SparseAccess I O sr sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => ampGateBlock D j
    | .inr _ => 1)

noncomputable def colOracleInvOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => TensorGate (permMatrix (colTable D hD j).symm) (1 : Matrix Bool Bool ℂ)
    | .inr _ => 1)

noncomputable def rowUniformOp (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun _ => rowUniformPrep (O := O) sr hsr)

noncomputable def rowUniformInvOp (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun _ => (rowUniformPrep (O := O) sr hsr)ᴴ)

noncomputable def rowOracleOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun r => match r with
    | .inl i => permMatrix (rowTable D hD i)
    | .inr _ => 1)

noncomputable def rowOracleInvOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun r => match r with
    | .inl i => permMatrix (rowTable D hD i).symm
    | .inr _ => 1)

noncomputable def leftWordOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  rowOracleOp D hD * rowUniformOp hsr

noncomputable def rightWordOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  ampGateOp D * colOracleOp D hD * colUniformOp hsc

inductive PairedStepKind where

  | rowUniform

  | rowOracle

  | rowOracleInv

  | colUniform

  | colOracle

  | colOracleInv

  | valueQuery

  | amplitudeGate

def PairedStepKind.rowQueries : PairedStepKind → ℕ
  | .rowOracle => 1
  | .rowOracleInv => 1
  | _ => 0

def PairedStepKind.colQueries : PairedStepKind → ℕ
  | .colOracle => 1
  | .colOracleInv => 1
  | _ => 0

def PairedStepKind.valueQueries : PairedStepKind → ℕ
  | .valueQuery => 1
  | _ => 0

def PairedStepKind.gateCount : PairedStepKind → ℕ
  | .rowUniform => 1
  | .colUniform => 1
  | .amplitudeGate => 1
  | _ => 0

def rowQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.rowQueries + rowQueryCount ss

def colQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.colQueries + colQueryCount ss

def valueQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.valueQueries + valueQueryCount ss

def gateStepCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.gateCount + gateStepCount ss

def encodingWordKinds : List PairedStepKind :=
  [.colUniform, .colOracle, .valueQuery, .rowOracleInv, .rowUniform]

noncomputable def wordOperatorOf (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsr : 0 < sr) (hsc : 0 < sc) : PairedStepKind →
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  fun k => match k with
    | .colUniform => colUniformOp hsc
    | .colOracle => colOracleOp D hD
    | .colOracleInv => colOracleInvOp D hD
    | .valueQuery => ampGateOp D
    | .amplitudeGate => ampGateOp D
    | .rowUniform => rowUniformInvOp hsr
    | .rowOracle => rowOracleOp D hD
    | .rowOracleInv => rowOracleInvOp D hD

noncomputable def wordOperator (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsr : 0 < sr) (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  encodingWordKinds.foldl (fun M k => wordOperatorOf D hD hsr hsc k * M) 1

end Qatlib.Concepts.BlockEncoding.EncodingCore
