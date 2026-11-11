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

/-!
# Paired sparse-access tables and encoding words

`rowTable` and `colTable` extend legal sparse-position access to permutations of tagged address
spaces. Lookup helpers, uniform preparations, and entry-dependent amplitude gates provide the
components of the paired sparse-access construction.

`PairedStepKind` records the operations and their query or gate charges. `encodingWordKinds`
specifies a five-step word, and `wordOperator` evaluates it on `SparseWorkspace` in execution
order. For the sparse block-encoding framework, see [GilyenSuLowWiebe2019].

## Main statements

* `rowTable` and `colTable`: permutations extending legal row and column position access.
* `leftWordOp` and `rightWordOp`: preparation operators assembled from sparse-access components.
* `wordOperator`: the operator associated with the listed encoding steps.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

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

/-- Under legal sparse access, equal column-position addresses imply equal column slots. -/
theorem colSlot_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) (j : O)
    (c c' : Fin sc) (h : D.colPos c j = D.colPos c' j) : c = c' :=
  hD.colInjective j h

/-- Under legal sparse access, equal row-position addresses imply equal row slots. -/
theorem rowSlot_eq (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) (i : I)
    (k k' : Fin sr) (h : D.rowPos i k = D.rowPos i k') : k = k' :=
  hD.rowInjective i h

/-- Chooses a row slot mapping to the given column address when such a slot exists. -/
noncomputable def rowSlotOfAddr (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) : Fin sr :=
  Classical.choose h

/-- The chosen row slot maps to the specified column address. -/
@[simp] theorem rowSlotOfAddr_pos (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) :
    D.rowPos i (rowSlotOfAddr D i o h) = .inl o :=
  Classical.choose_spec h

/-- Under legal sparse access, every row slot mapping to the given column address equals the
chosen slot. -/
theorem rowSlotOfAddr_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) (k : Fin sr)
    (hk : D.rowPos i k = .inl o) : k = rowSlotOfAddr D i o h := by
  refine hD.rowInjective i ?_
  rw [hk, rowSlotOfAddr_pos D i o h]

/-- Extends row-position access to the full tagged address space by sending listed column
addresses back to their row slots and fixing unlisted addresses. -/
noncomputable def rowTableFun (D : SparseAccess I O sr sc) (i : I) :
    ColAddr O sr → ColAddr O sr
  | .inl o =>
      if h : ∃ kx : Fin sr, D.rowPos i kx = .inl o then .inr (rowSlotOfAddr D i o h)
      else .inl o
  | .inr k => D.rowPos i k

/-- On a tagged row slot, the extended row table agrees with `rowPos`. -/
@[simp] theorem rowTableFun_inr (D : SparseAccess I O sr sc) (i : I) (k : Fin sr) :
    rowTableFun D i (.inr k) = D.rowPos i k := rfl

/-- On a listed column address, the extended row table returns its chosen tagged row slot. -/
theorem rowTableFun_inl (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) :
    rowTableFun D i (.inl o) = .inr (rowSlotOfAddr D i o h) := by
  simp [rowTableFun, dif_pos h]

/-- The extended row table fixes a column address absent from the row-position list. -/
theorem rowTableFun_inl_of_not (D : SparseAccess I O sr sc) (i : I) (o : O)
    (h : ¬ (∃ kx : Fin sr, D.rowPos i kx = .inl o)) :
    rowTableFun D i (.inl o) = .inl o := by
  simp [rowTableFun, dif_neg h]

/-- Under legal sparse access, a row padding link from `k` to `k'` has the reverse link from
`k'` to `k`. -/
theorem rowPad_reciprocal (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (k k' : Fin sr) (hk : D.rowPos i k = .inr k') :
    D.rowPos i k' = .inr k := hD.rowPad i k k' hk

/-- The extended row table is injective under legal sparse access. -/
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

/-- The extended row table is surjective under legal sparse access. -/
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

/-- The permutation of tagged column addresses induced by a legal row-position table. -/
noncomputable def rowTable (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) : ColAddr O sr ≃ ColAddr O sr :=
  Equiv.ofBijective (rowTableFun D i)
    ⟨rowTableFun_injective D hD i, rowTableFun_surjective D hD i⟩

/-- Chooses a column slot mapping to the given row address when such a slot exists. -/
noncomputable def colSlotOfAddr (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) : Fin sc :=
  Classical.choose h

/-- The chosen column slot maps to the specified row address. -/
@[simp] theorem colSlotOfAddr_pos (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) :
    D.colPos (colSlotOfAddr D j i h) j = .inl i :=
  Classical.choose_spec h

/-- Under legal sparse access, every column slot mapping to the given row address equals the
chosen slot. -/
theorem colSlotOfAddr_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) (c : Fin sc)
    (hc : D.colPos c j = .inl i) : c = colSlotOfAddr D j i h := by
  refine colSlot_eq D hD j c (colSlotOfAddr D j i h) ?_
  rw [hc, colSlotOfAddr_pos D j i h]

/-- Extends column-position access to the full tagged address space by sending listed row
addresses back to their column slots and fixing unlisted addresses. -/
noncomputable def colTableFun (D : SparseAccess I O sr sc) (j : O) :
    RowAddr I sc → RowAddr I sc
  | .inl i =>
      if h : ∃ cx : Fin sc, D.colPos cx j = .inl i then .inr (colSlotOfAddr D j i h)
      else .inl i
  | .inr c => D.colPos c j

/-- On a tagged column slot, the extended column table agrees with `colPos`. -/
@[simp] theorem colTableFun_inr (D : SparseAccess I O sr sc) (j : O) (c : Fin sc) :
    colTableFun D j (.inr c) = D.colPos c j := rfl

/-- On a listed row address, the extended column table returns its chosen tagged column slot. -/
theorem colTableFun_inl (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) :
    colTableFun D j (.inl i) = .inr (colSlotOfAddr D j i h) := by
  simp [colTableFun, dif_pos h]

/-- The extended column table fixes a row address absent from the column-position list. -/
theorem colTableFun_inl_of_not (D : SparseAccess I O sr sc) (j : O) (i : I)
    (h : ¬ (∃ cx : Fin sc, D.colPos cx j = .inl i)) :
    colTableFun D j (.inl i) = .inl i := by
  simp [colTableFun, dif_neg h]

/-- Under legal sparse access, any column slot mapping to a padding address maps to its own
tagged slot. -/
theorem colPad_fixed (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (c c' : Fin sc) (hc : D.colPos c j = .inr c') : D.colPos c j = .inr c := by
  have hrec := hD.colPad j c c' hc
  have hinj : c = c' := colSlot_eq D hD j c c' (by rw [hc, hrec])
  rw [← hinj] at hc
  exact hc

/-- The extended column table is injective under legal sparse access. -/
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

/-- The extended column table is surjective under legal sparse access. -/
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

/-- The permutation of tagged row addresses induced by a legal column-position table. -/
noncomputable def colTable (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) : RowAddr I sc ≃ RowAddr I sc :=
  Equiv.ofBijective (colTableFun D j)
    ⟨colTableFun_injective D hD j, colTableFun_surjective D hD j⟩

/-- Looks up a row slot in the sparse row-position table. -/
def rowLookup (D : SparseAccess I O sr sc) (i : I) (k : Fin sr) : ColAddr O sr :=
  D.rowPos i k

/-- Returns no row slot for a zero matrix entry and a chosen row slot for a nonzero entry under
legal sparse access. -/
noncomputable def rowUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) : Option (Fin sr) :=
  if h : D.entry i o = 0 then none
  else some (rowSlotOf D hD i o h)

/-- Looks up a column slot in the sparse column-position table. -/
def colLookup (D : SparseAccess I O sr sc) (j : O) (c : Fin sc) : RowAddr I sc :=
  D.colPos c j

/-- Returns no column slot for a zero matrix entry and a chosen column slot for a nonzero entry
under legal sparse access. -/
noncomputable def colUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) : Option (Fin sc) :=
  if h : D.entry i j = 0 then none
  else some (colSlotOf D hD j i h)

/-- The preparation matrix for the uniform row-slot state relative to the designated
column-address scratch state. -/
noncomputable def rowUniformPrep {O : Type*} [Fintype O] (sr : ℕ) (hsr : 0 < sr) :
    Matrix (ColAddr O sr) (ColAddr O sr) ℂ :=
  complexPrepare (rowSlotUniform O sr) (colScratch O sr hsr)

/-- The preparation matrix for the uniform column-slot state relative to the designated
row-address scratch state. -/
noncomputable def colUniformPrep {I : Type*} [Fintype I] (sc : ℕ) (hsc : 0 < sc) :
    Matrix (RowAddr I sc) (RowAddr I sc) ℂ :=
  complexPrepare (colSlotUniform I sc) (rowScratch I sc hsc)

/-- The Boolean amplitude gate associated with the matrix entry at row `i` and column `j`. -/
noncomputable def ampGateAt (D : SparseAccess I O sr sc) (j : O) (i : I) :
    Matrix Bool Bool ℂ :=
  ampGate (D.entry i j)

/-- The block-diagonal amplitude gate for a fixed column, using its matrix entries on row
addresses and zero on padding addresses. -/
noncomputable def ampGateBlock (D : SparseAccess I O sr sc) (j : O) :
    Matrix (RowAddr I sc × Bool) (RowAddr I sc × Bool) ℂ :=
  blockDiagFirst (fun r => match r with
    | .inl i => ampGateAt D j i
    | .inr _ => ampGate 0)

/-- Lifts column-slot uniform preparation to the sparse workspace while preserving the Boolean
amplitude register. -/
noncomputable def colUniformOp (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun _ => TensorGate (colUniformPrep (I := I) sc hsc)
    (1 : Matrix Bool Bool ℂ))

/-- Applies the column-table permutation on each genuine column-address block and identity on
padding blocks. -/
noncomputable def colOracleOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => TensorGate (permMatrix (colTable D hD j)) (1 : Matrix Bool Bool ℂ)
    | .inr _ => 1)

/-- Applies entry-dependent amplitude gates on genuine column-address blocks and identity on
padding blocks. -/
noncomputable def ampGateOp (D : SparseAccess I O sr sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => ampGateBlock D j
    | .inr _ => 1)

/-- Applies the inverse column-table permutation on each genuine column-address block and
identity on padding blocks. -/
noncomputable def colOracleInvOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagFirst (fun c => match c with
    | .inl j => TensorGate (permMatrix (colTable D hD j).symm) (1 : Matrix Bool Bool ℂ)
    | .inr _ => 1)

/-- Lifts row-slot uniform preparation to the sparse workspace using the crossed block-diagonal
construction. -/
noncomputable def rowUniformOp (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun _ => rowUniformPrep (O := O) sr hsr)

/-- Lifts the conjugate transpose of row-slot uniform preparation to the sparse workspace. -/
noncomputable def rowUniformInvOp (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun _ => (rowUniformPrep (O := O) sr hsr)ᴴ)

/-- Applies the row-table permutation on each genuine row-address block and identity on padding
blocks. -/
noncomputable def rowOracleOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun r => match r with
    | .inl i => permMatrix (rowTable D hD i)
    | .inr _ => 1)

/-- Applies the inverse row-table permutation on each genuine row-address block and identity on
padding blocks. -/
noncomputable def rowOracleInvOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  blockDiagCross (fun r => match r with
    | .inl i => permMatrix (rowTable D hD i).symm
    | .inr _ => 1)

/-- The left preparation word operator, applying row uniform preparation followed by
row-position access. -/
noncomputable def leftWordOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsr : 0 < sr) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  rowOracleOp D hD * rowUniformOp hsr

/-- The right preparation word operator, applying column uniform preparation, column-position
access, and entry-dependent amplitude gates. -/
noncomputable def rightWordOp (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  ampGateOp D * colOracleOp D hD * colUniformOp hsc

/-- Step tags for paired sparse access, distinguishing preparation gates, forward and inverse
position queries, value queries, and amplitude gates. -/
inductive PairedStepKind where

  | rowUniform

  | rowOracle

  | rowOracleInv

  | colUniform

  | colOracle

  | colOracleInv

  | valueQuery

  | amplitudeGate

/-- Assigns one row query to a forward or inverse row-oracle step and zero to every other step. -/
def PairedStepKind.rowQueries : PairedStepKind → ℕ
  | .rowOracle => 1
  | .rowOracleInv => 1
  | _ => 0

/-- Assigns one column query to a forward or inverse column-oracle step and zero to every other
step. -/
def PairedStepKind.colQueries : PairedStepKind → ℕ
  | .colOracle => 1
  | .colOracleInv => 1
  | _ => 0

/-- Assigns one value query to a value-query step and zero to every other step. -/
def PairedStepKind.valueQueries : PairedStepKind → ℕ
  | .valueQuery => 1
  | _ => 0

/-- Assigns one gate to row preparation, column preparation, or an amplitude-gate step and zero
to every other step. -/
def PairedStepKind.gateCount : PairedStepKind → ℕ
  | .rowUniform => 1
  | .colUniform => 1
  | .amplitudeGate => 1
  | _ => 0

/-- Sums the row-query charges of a list of paired-access steps. -/
def rowQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.rowQueries + rowQueryCount ss

/-- Sums the column-query charges of a list of paired-access steps. -/
def colQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.colQueries + colQueryCount ss

/-- Sums the value-query charges of a list of paired-access steps. -/
def valueQueryCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.valueQueries + valueQueryCount ss

/-- Sums the gate charges of a list of paired-access steps. -/
def gateStepCount : List PairedStepKind → ℕ
  | [] => 0
  | s :: ss => s.gateCount + gateStepCount ss

/-- The five-step sparse encoding word: column preparation, column query, value query, inverse
row query, and row preparation tag. -/
def encodingWordKinds : List PairedStepKind :=
  [.colUniform, .colOracle, .valueQuery, .rowOracleInv, .rowUniform]

/-- Interprets paired-access step tags as workspace matrices, with the row preparation tag
denoting the inverse row preparation. -/
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

/-- Evaluates `encodingWordKinds` by left-multiplying its interpreted operators in execution
order. -/
noncomputable def wordOperator (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (hsr : 0 < sr) (hsc : 0 < sc) :
    Matrix (SparseWorkspace I O sr sc) (SparseWorkspace I O sr sc) ℂ :=
  encodingWordKinds.foldl (fun M k => wordOperatorOf D hD hsr hsc k * M) 1

end Qatlib.Concepts.BlockEncoding.EncodingCore
