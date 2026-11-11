/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.EncodingCore.PairedAccessDefs

/-!
# Paired sparse access and positive-operator access

This module proves inverse-lookup and padding identities for legal sparse access tables and
computes their permutation actions on basis states. It also records positivity and resource
counts for purification and measurement access, together with the impossibility of uniformly
identifying positive operators from a constant output. Sparse block encodings are treated in
[GilyenSuLowWiebe2019].

`WordCost` and `classicalBitCost` record the query, gate, and address-bit costs of the
paired-access construction.

## Main statements

* `rowLookup_rowUnlookup`: A nonzero entry is recovered from its row slot.
* `purification_access_realizable`: Purification produces a density operator with explicit word
  counts.
* `povm_measurement_bit_control`: Uniform measurement error yields an approximate block
  encoding.
* `encodingWord_ledger`: The encoding word uses one query of each access kind and two gate
  steps.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false

variable {I O : Type*} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
variable {sr sc : ℕ}

/-- A legal row table cannot address a column at which the matrix entry is zero. -/
theorem rowLookup_ne_of_entry_zero (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (hz : D.entry i o = 0) (k : Fin sr) : D.rowPos i k ≠ .inl o := by
  intro hk
  exact (hD.rowLegal i k o hk) hz

/-- A legal column table cannot address a row at which the matrix entry is zero. -/
theorem colLookup_ne_of_entry_zero (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hz : D.entry i j = 0) (c : Fin sc) : D.colPos c j ≠ .inl i := by
  intro hc
  exact (hD.colLegal j c i hc) hz

/-- Inverse row lookup returns `none` for a zero matrix entry. -/
theorem rowUnlookup_eq_none (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (hz : D.entry i o = 0) : rowUnlookup D hD i o = none := by
  simp [rowUnlookup, dif_pos hz]

/-- Inverse row lookup of a nonzero entry returns its canonical row slot. -/
theorem rowUnlookup_eq_some (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (hne : D.entry i o ≠ 0) :
    rowUnlookup D hD i o = some (rowSlotOf D hD i o hne) := by
  simp [rowUnlookup, dif_neg hne]

/-- Inverse column lookup returns `none` for a zero matrix entry. -/
theorem colUnlookup_eq_none (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hz : D.entry i j = 0) : colUnlookup D hD j i = none := by
  simp [colUnlookup, dif_pos hz]

/-- Inverse column lookup of a nonzero entry returns its canonical column slot. -/
theorem colUnlookup_eq_some (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) :
    colUnlookup D hD j i = some (colSlotOf D hD j i hne) := by
  simp [colUnlookup, dif_neg hne]

/-- Looking up the canonical row slot of a nonzero entry returns its column address. -/
theorem rowLookup_rowUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (hne : D.entry i o ≠ 0) :
    rowLookup D i (rowSlotOf D hD i o hne) = .inl o :=
  rowSlotOf_pos D hD i o hne

/-- Looking up the canonical column slot of a nonzero entry returns its row address. -/
theorem colLookup_colUnlookup (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) :
    colLookup D j (colSlotOf D hD j i hne) = .inl i :=
  colSlotOf_pos D hD j i hne

/-- Every row slot addressing a given nonzero entry equals its canonical row slot. -/
theorem rowUnlookup_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (hne : D.entry i o ≠ 0) (k : Fin sr) (hk : D.rowPos i k = .inl o) :
    k = rowSlotOf D hD i o hne :=
  rowSlotOf_unique D hD i o hne k hk

/-- Every column slot addressing a given nonzero entry equals its canonical column slot. -/
theorem colUnlookup_unique (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (hne : D.entry i j ≠ 0) (c : Fin sc) (hc : D.colPos c j = .inl i) :
    c = colSlotOf D hD j i hne :=
  colSlotOf_unique D hD j i hne c hc

/-- A row slot returned as a padding address does not itself address any legal column. -/
theorem rowLookup_padding_not_legal (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (k k' : Fin sr) (hk : D.rowPos i k = .inr k') :
    ¬ ∃ o : O, D.rowPos i k' = .inl o := by
  rintro ⟨o, ho⟩
  have hrec := hD.rowPad i k k' hk
  rw [ho] at hrec
  exact absurd hrec (by simp)

/-- The row-table image of a padding address is not legal. -/
theorem rowLookup_padding_not_legal' (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (k k' : Fin sr) (hk : D.rowPos i k = .inr k') :
    ¬ (D.rowPos i k').IsLegal := by
  intro hleg
  cases hpos : D.rowPos i k' with
  | inl o => exact (rowLookup_padding_not_legal D hD i k k' hk) ⟨o, hpos⟩
  | inr c => simp [ColAddr.IsLegal, hpos] at hleg

/-- A column slot returned as a padding address does not itself address any legal row. -/
theorem colLookup_padding_not_legal (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (c c' : Fin sc) (hc : D.colPos c j = .inr c') :
    ¬ ∃ i : I, D.colPos c' j = .inl i := by
  rintro ⟨i, hi⟩
  have hfix := hD.colPad j c c' hc
  rw [hi] at hfix
  exact absurd hfix (by simp)

/-- The column-table image of a padding address is not legal. -/
theorem colLookup_padding_not_legal' (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (c c' : Fin sc) (hc : D.colPos c j = .inr c') :
    ¬ (D.colPos c' j).IsLegal := by
  intro hleg
  cases hpos : D.colPos c' j with
  | inl i => exact (colLookup_padding_not_legal D hD j c c' hc) ⟨i, hpos⟩
  | inr c'' => simp [RowAddr.IsLegal, hpos] at hleg

/-- The row-table permutation sends a slot address to the corresponding value of `rowPos`. -/
theorem rowTable_apply_slot (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (k : Fin sr) : (rowTable D hD i) (.inr k) = D.rowPos i k := by
  rfl

/-- The column-table permutation sends a slot address to the corresponding value of `colPos`. -/
theorem colTable_apply_slot (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (c : Fin sc) : (colTable D hD j) (.inr c) = D.colPos c j := by
  rfl

/-- The inverse row-table permutation sends an addressed column to the slot selected by
`rowSlotOfAddr`. -/
theorem rowTable_symm_apply_inl (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (h : ∃ kx : Fin sr, D.rowPos i kx = .inl o) :
    (rowTable D hD i).symm (.inl o) = .inr (rowSlotOfAddr D i o h) := by
  have h1 : (rowTable D hD i) (.inr (rowSlotOfAddr D i o h)) = .inl o := by
    show rowTableFun D i (.inr (rowSlotOfAddr D i o h)) = .inl o
    rw [rowTableFun_inr, rowSlotOfAddr_pos D i o h]
  have h2 := (rowTable D hD i).symm_apply_apply (.inr (rowSlotOfAddr D i o h))
  rw [h1] at h2
  exact h2

/-- The inverse column-table permutation sends an addressed row to the slot selected by
`colSlotOfAddr`. -/
theorem colTable_symm_apply_inl (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (h : ∃ cx : Fin sc, D.colPos cx j = .inl i) :
    (colTable D hD j).symm (.inl i) = .inr (colSlotOfAddr D j i h) := by
  have h1 : (colTable D hD j) (.inr (colSlotOfAddr D j i h)) = .inl i := by
    show colTableFun D j (.inr (colSlotOfAddr D j i h)) = .inl i
    rw [colTableFun_inr, colSlotOfAddr_pos D j i h]
  have h2 := (colTable D hD j).symm_apply_apply (.inr (colSlotOfAddr D j i h))
  rw [h1] at h2
  exact h2

/-- The row-table permutation fixes every column address that is not addressed by a row slot. -/
theorem rowTable_inl_of_unaddressed (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (i : I) (o : O) (h : ¬ (∃ kx : Fin sr, D.rowPos i kx = .inl o)) :
    (rowTable D hD i) (.inl o) = .inl o :=
  rowTableFun_inl_of_not D i o h

/-- The column-table permutation fixes every row address that is not addressed by a column slot. -/
theorem colTable_inl_of_unaddressed (D : SparseAccess I O sr sc) (hD : SparseAccessLegal D)
    (j : O) (i : I) (h : ¬ (∃ cx : Fin sc, D.colPos cx j = .inl i)) :
    (colTable D hD j) (.inl i) = .inl i :=
  colTableFun_inl_of_not D j i h

/-- At the image of `y0` under an injective map, multiplying by its permutation matrix returns
the input coordinate at `y0`. -/
theorem permMatrix_mulVec_apply {J : Type*} [Fintype J] [DecidableEq J] (σ : J → J)
    (hσ : Function.Injective σ) (v : J → ℂ) (x : J) (y0 : J) (hy0 : σ y0 = x) :
    (permMatrix σ *ᵥ v) x = v y0 := by
  rw [Matrix.mulVec, dotProduct]
  simp only [permMatrix]
  calc ∑ j, (if x = σ j then 1 else 0) * v j = (if x = σ y0 then 1 else 0) * v y0 :=
      Fintype.sum_eq_single y0 (by
        intro j hj
        rw [if_neg (fun h => hj (hσ (h.symm.trans hy0.symm)))]
        simp)
    _ = v y0 := by rw [if_pos hy0.symm]; simp

/-- The cross-register block-diagonal matrix acts on a basis vector by the selected block and
preserves the block and spectator indices. -/
theorem blockDiagCross_mulVec_ket {A B C : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] [Fintype C] [DecidableEq C] (blk : A → Matrix B B ℂ) (b : B) (a : A)
    (c : C) (b' : B) (a' : A) (c' : C) :
    (blockDiagCross blk *ᵥ Ket (b, (a, c))) (b', (a', c')) =
      if a' = a ∧ c' = c then (blk a) b' b else 0 := by
  rw [Matrix.mulVec]
  simp only [dotProduct, blockDiagCross, Matrix.of_apply]
  calc ∑ x, (if a' = x.2.1 then if c' = x.2.2 then (blk a') b' x.1 else 0 else 0)
        * Ket (b, (a, c)) x
      = (if a' = (b, (a, c)).2.1 then if c' = (b, (a, c)).2.2
          then (blk a') b' (b, (a, c)).1 else 0 else 0)
        * Ket (b, (a, c)) (b, (a, c)) :=
      Fintype.sum_eq_single (b, (a, c)) (by
        intro x hx
        have hK : Qatlib.Foundations.PureStateMath.Ket (b, (a, c)) x = 0 := by
          show (if x = (b, (a, c)) then 1 else 0) = 0
          rw [if_neg hx]
        rw [hK]
        simp)
    _ = if a' = a ∧ c' = c then (blk a) b' b else 0 := by
      have hK : Qatlib.Foundations.PureStateMath.Ket (b, (a, c)) (b, (a, c)) = 1 := by
        show (if (b, (a, c)) = (b, (a, c)) then 1 else 0) = 1
        rw [if_pos rfl]
      rw [hK]
      by_cases ha : a' = a <;> by_cases hc : c' = c <;> simp [ha, hc]

/-- A block-diagonal matrix controlled by the first register applies its selected block to the
second-register basis vector. -/
theorem blockDiagFirst_mulVec_ket {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (blk : A → Matrix B B ℂ) (a : A) (b : B) (a' : A) (b' : B) :
    (blockDiagFirst blk *ᵥ Ket (a, b)) (a', b') =
      if a' = a then (blk a) b' b else 0 := by
  rw [Matrix.mulVec]
  simp only [dotProduct, blockDiagFirst, Matrix.of_apply]
  calc ∑ x, (if a' = x.1 then (blk a') b' x.2 else 0) * Ket (a, b) x
      = (if a' = (a, b).1 then (blk a') b' (a, b).2 else 0) * Ket (a, b) (a, b) :=
      Fintype.sum_eq_single (a, b) (by
        intro x hx
        have hK : Qatlib.Foundations.PureStateMath.Ket (a, b) x = 0 := by
          show (if x = (a, b) then 1 else 0) = 0
          rw [if_neg hx]
        rw [hK]
        simp)
    _ = if a' = a then (blk a) b' b else 0 := by
      have hK : Qatlib.Foundations.PureStateMath.Ket (a, b) (a, b) = 1 := by
        show (if (a, b) = (a, b) then 1 else 0) = 1
        rw [if_pos rfl]
      rw [hK]
      by_cases ha : a' = a <;> simp [ha]

/-- Row-slot preparation sends the designated column scratch basis state to the uniform row-slot
state. -/
theorem rowUniformPrep_mulVec_ket {O : Type*} [Fintype O] (sr : ℕ) (hsr : 0 < sr) :
    (rowUniformPrep (O := O) sr hsr) *ᵥ Ket (colScratch O sr hsr) = rowSlotUniform O sr :=
  complexPrepare_mulVec_ket _ _

/-- Column-slot preparation sends the designated row scratch basis state to the uniform
column-slot state. -/
theorem colUniformPrep_mulVec_ket {I : Type*} [Fintype I] (sc : ℕ) (hsc : 0 < sc) :
    (colUniformPrep (I := I) sc hsc) *ᵥ Ket (rowScratch I sc hsc) = colSlotUniform I sc :=
  complexPrepare_mulVec_ket _ _

/-- The access modes for a positive operator: purification access, copy access, a block oracle,
or no access. -/
inductive PositiveAccess where

  | purification

  | copy

  | blockOracle

  | noAccess

/-- The rank-one outer product of the basis state `Ket i` with itself. -/
noncomputable def rankOneEffect (I : Type*) [Fintype I] [DecidableEq I] (i : I) :
    Matrix I I ℂ :=
  outerProduct (Ket i)

/-- Every basis-state rank-one effect is positive semidefinite. -/
theorem rankOneEffect_posSemidef (I : Type*) [Fintype I] [DecidableEq I] (i : I) :
    (rankOneEffect I i).PosSemidef :=
  outerProduct_posSemidef (Ket i)

/-- Distinct basis indices determine distinct rank-one effects. -/
theorem rankOneEffect_ne (I : Type*) [Fintype I] [DecidableEq I] (i j : I) (hij : i ≠ j) :
    rankOneEffect I i ≠ rankOneEffect I j := by
  intro h
  have h11 := congrFun (congrFun h i) i
  have hK : Ket j i = 0 := by
    show (if i = j then 1 else 0) = 0
    rw [if_neg hij]
  have hL : Ket i i = 1 := by
    show (if i = i then 1 else 0) = 1
    rw [if_pos rfl]
  simp only [rankOneEffect, outerProduct_apply, hK, hL] at h11
  norm_num at h11

/-- If the index type has two distinct elements, no function can both recover every positive
semidefinite matrix and have constant output on all such matrices. -/
theorem noAccess_unidentifiable (I : Type*) [Fintype I] [DecidableEq I]
    (i j : I) (hij : i ≠ j) :
    ¬ ∃ (f : Matrix I I ℂ → Matrix I I ℂ),
      (∀ D : Matrix I I ℂ, D.PosSemidef → f D = D) ∧
      (∀ D D' : Matrix I I ℂ, D.PosSemidef → D'.PosSemidef → f D' = f D) := by
  rintro ⟨f, hcorrect, hconst⟩
  have hD0 : (rankOneEffect I i).PosSemidef := rankOneEffect_posSemidef I i
  have hD1 : (rankOneEffect I j).PosSemidef := rankOneEffect_posSemidef I j
  have hne : rankOneEffect I i ≠ rankOneEffect I j := rankOneEffect_ne I i j hij
  have h1 : rankOneEffect I j = rankOneEffect I i := by
    calc rankOneEffect I j = f (rankOneEffect I j) := (hcorrect _ hD1).symm
      _ = f (rankOneEffect I i) := hconst _ _ hD0 hD1
      _ = rankOneEffect I i := hcorrect _ hD0
  exact hne h1.symm

/-- A unitary-prepared purification gives a positive semidefinite density matrix of trace one;
its purification word has query count two and gate count one. -/
theorem purification_access_realizable {A I : Type*} [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] (U : Matrix (A × I) (A × I) ℂ) (seed : A × I)
    (hU : U ∈ Matrix.unitaryGroup (A × I) ℂ) :
    (purifiedDensity (U *ᵥ Ket seed)).PosSemidef ∧
      Matrix.trace (purifiedDensity (U *ᵥ Ket seed)) = 1 ∧
      adjointQueryCount (purificationWord (A := A) (I := I)) = 2 ∧
      adjointGateCount (purificationWord (A := A) (I := I)) = 1 := by
  have hp := purification_actual_positive_block_and_cost U seed hU
  exact ⟨hp.1, hp.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

/-- A unitary measurement produces an effect with positive semidefinite complement; its outcome
word has query count two and gate count two. -/
theorem povm_access_realizable {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J)
    (hM : M ∈ Matrix.unitaryGroup (J × I) ℂ) :
    (outcomeEffect M j0 S).PosSemidef ∧
      ((1 : Matrix I I ℂ) - outcomeEffect M j0 S).PosSemidef ∧
      adjointQueryCount (outcomeWord (I := I) S) = 2 ∧
      adjointGateCount (outcomeWord (I := I) S) = 2 := by
  have hp := povm_actual_effect_block_and_cost M j0 S hM
  exact ⟨hp.1, hp.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

/-- A Hermitian operator whose normalized-state expectations approximate the measurement
probabilities within `2 ^ (-b)` has a block encoding with scale one and that error. -/
theorem povm_measurement_bit_control {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] (M : Matrix (J × I) (J × I) ℂ) (j0 : J) (S : Finset J)
    (B : Matrix I I ℂ) (b : ℕ) (hM : M ∈ Matrix.unitaryGroup (J × I) ℂ)
    (hB : B.IsHermitian)
    (herror : ∀ psi : QState I, Normalized psi →
      |(Qatlib.Foundations.PureStateMath.Inner psi (B *ᵥ psi)).re - MeasureProb (M *ᵥ (encodingFiber j0 *ᵥ psi))
        {x | x.1 ∈ S}| ≤ (2 : ℝ) ^ (-(b : ℝ))) :
    BlockEncoding B (outcomeBody M S) (outcomeFrame j0) (outcomeFrame j0) 1 ((2 : ℝ) ^ (-(b : ℝ))) := by
  exact povm_expectation_absolute_error_encoding M j0 S B ((2 : ℝ) ^ (-(b : ℝ))) hM hB
    (by positivity) herror

/-- The row-query, column-query, value-query, and gate-step counts of a paired-access word. -/
structure WordCost where

  rowQueries : ℕ

  colQueries : ℕ

  valueQueries : ℕ

  gateCount : ℕ
  deriving DecidableEq, Repr

/-- Counts the three kinds of oracle queries and the gate steps in a list of paired step kinds. -/
def wordCost (steps : List PairedStepKind) : WordCost where
  rowQueries := rowQueryCount steps
  colQueries := colQueryCount steps
  valueQueries := valueQueryCount steps
  gateCount := gateStepCount steps

/-- The encoding word uses one row query, one column query, one value query, and two gate steps. -/
theorem encodingWord_ledger :
    wordCost encodingWordKinds =
      { rowQueries := 1, colQueries := 1, valueQueries := 1, gateCount := 2 } := by
  decide

/-- The bit budget `Nat.log2 (Fintype.card O + sr) + 1` for the augmented column-address space. -/
def colAddressBits (O : Type*) [Fintype O] (sr : ℕ) : ℕ :=
  Nat.log2 (Fintype.card O + sr) + 1

/-- The bit budget `Nat.log2 (Fintype.card I + sc) + 1` for the augmented row-address space. -/
def rowAddressBits (I : Type*) [Fintype I] (sc : ℕ) : ℕ :=
  Nat.log2 (Fintype.card I + sc) + 1

/-- The sum of the bit budgets for the augmented column and row address spaces. -/
def classicalBitCost (I O : Type*) [Fintype I] [Fintype O] (sr sc : ℕ) : ℕ :=
  colAddressBits O sr + rowAddressBits I sc

/-- The classical bit cost is the sum of `colAddressBits` and `rowAddressBits`. -/
theorem classicalBitCost_eq (I O : Type*) [Fintype I] [Fintype O] (sr sc : ℕ) :
    classicalBitCost I O sr sc = colAddressBits O sr + rowAddressBits I sc := rfl

end Qatlib.Concepts.AdversaryBounds.AdvDuality
