/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator

/-!
# Toffoli block ledgers for multi-control synthesis

`ToffBlock` separates relative and exact Toffoli cores from single-wire gates, and
`toffBlocksGates` expands block words into elementary gates. The constructions `prefixBlocks`,
`packedBlocks`, and `cor74Blocks` provide a block ledger for the multi-control synthesis of
[BarencoEtAl1995].

The census theorems track relative blocks, exact blocks, and list lengths through adjoints and
commutators. For at least five controls, `cor74Word_length` gives the exact length of the
expanded elementary word.

## Main statements

* `cor74Blocks_census`: Counts of relative and exact blocks in the Corollary 7.4 construction.
* `cor74Word_length`: The exact elementary length `48 * m - 109`.
* `toffBlocksGates_adj`: Compatibility of block expansion with adjoints.

## References

* [Barenco et al., 1995][BarencoEtAl1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CircuitImpl.MultiControl.CountCompressedLadders
open Qatlib.Concepts.CircuitImpl.MultiControl.CountFramedBorrowed
open Qatlib.Concepts.CircuitImpl.MultiControl.CountToffoliFrames
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.CircuitImpl.MultiControl

open Matrix
open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator

/-- Blocks representing a relative Toffoli core, an exact Toffoli core or its adjoint, or a
single-wire matrix. -/
inductive ToffBlock (N : ℕ) where

  | rel : Fin N → Fin N → Fin N → ToffBlock N

  | exact : Fin N → Fin N → Fin N → ToffBlock N

  | exactAdj : Fin N → Fin N → Fin N → ToffBlock N

  | single : Fin N → Matrix Bool Bool ℂ → ToffBlock N

/-- Expands a Toffoli block into its elementary reflection-gate word. -/
noncomputable def ToffBlock.gates {N : ℕ} : ToffBlock N → List (ReflectionGate N)
  | .rel a b t => sourceRelativeMiddle a b t
  | .exact a b t => sourceToffoliMiddle a b t
  | .exactAdj a b t => reflectionAdjoint (sourceToffoliMiddle a b t)
  | .single w U => [.inl (w, U)]

/-- Concatenates the elementary gate expansions of a list of Toffoli blocks. -/
noncomputable def toffBlocksGates {N : ℕ} (bs : List (ToffBlock N)) :
    List (ReflectionGate N) := bs.flatMap ToffBlock.gates

/-- The adjoint block operation, interchanging exact cores with their adjoints, fixing relative
cores, and taking the conjugate transpose of single-wire matrices. -/
def ToffBlock.adj {N : ℕ} : ToffBlock N → ToffBlock N
  | .rel a b t => .rel a b t
  | .exact a b t => .exactAdj a b t
  | .exactAdj a b t => .exact a b t
  | .single w U => .single w Uᴴ

/-- Forms the adjoint block word by reversing the list and taking the adjoint of each block. -/
def toffBlocksAdj {N : ℕ} (bs : List (ToffBlock N)) : List (ToffBlock N) :=
  (bs.map ToffBlock.adj).reverse

/-- Taking the adjoint of an elementary reflection gate twice returns the original gate. -/
theorem reflectionGateAdjoint_involutive {N : ℕ} (g : ReflectionGate N) :
    reflectionGateAdjoint (reflectionGateAdjoint g) = g := by
  rcases g with ⟨w, U⟩ | ⟨c, t⟩
  · simp [reflectionGateAdjoint, Matrix.conjTranspose_conjTranspose]
  · simp [reflectionGateAdjoint]

/-- The adjoint of an appended gate word is the append of the adjoint words in reverse order. -/
theorem reflectionAdjoint_append' {N : ℕ} (X Y : List (ReflectionGate N)) :
    reflectionAdjoint (X ++ Y) = reflectionAdjoint Y ++ reflectionAdjoint X := by
  simp [reflectionAdjoint, List.reverse_append, List.map_append]

/-- Taking the adjoint of a reflection-gate word twice returns the original word. -/
theorem reflectionAdjoint_involutive {N : ℕ} (gs : List (ReflectionGate N)) :
    reflectionAdjoint (reflectionAdjoint gs) = gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have h1 : reflectionAdjoint (g :: gs) = reflectionAdjoint gs ++ [reflectionGateAdjoint g] := by
      simp [reflectionAdjoint, List.reverse_cons, List.map_append]
    have h2 : reflectionAdjoint [reflectionGateAdjoint g] = [g] := by
      simp [reflectionAdjoint, reflectionGateAdjoint_involutive]
    rw [h1, reflectionAdjoint_append', h2, ih]
    rfl

/-- The relative Toffoli middle word is equal to its syntactic adjoint. -/
theorem sourceRelativeMiddle_selfAdjoint {N : ℕ} (a b t : Fin N) :
    reflectionAdjoint (sourceRelativeMiddle a b t) = sourceRelativeMiddle a b t := by
  simp [sourceRelativeMiddle, reflectionAdjoint, reflectionGateAdjoint,
    Matrix.conjTranspose_conjTranspose]

/-- Expanding an adjoint block gives the adjoint of the expanded block. -/
theorem toffBlockGates_adj {N : ℕ} (b : ToffBlock N) :
    reflectionAdjoint (ToffBlock.gates b) = ToffBlock.gates b.adj := by
  rcases b with ⟨a, b, t⟩ | ⟨a, b, t⟩ | ⟨a, b, t⟩ | ⟨w, U⟩
  · exact sourceRelativeMiddle_selfAdjoint a b t
  · rfl
  · exact reflectionAdjoint_involutive _
  · rfl

/-- Expanding an empty block list gives an empty gate list. -/
theorem toffBlocksGates_nil {N : ℕ} : toffBlocksGates ([] : List (ToffBlock N)) = [] := rfl

/-- Expanding a block followed by a block list concatenates their gate expansions. -/
theorem toffBlocksGates_cons {N : ℕ} (b : ToffBlock N) (bs : List (ToffBlock N)) :
    toffBlocksGates (b :: bs) = ToffBlock.gates b ++ toffBlocksGates bs :=
  List.flatMap_cons

/-- Block expansion preserves list append. -/
theorem toffBlocksGates_append {N : ℕ} (as bs : List (ToffBlock N)) :
    toffBlocksGates (as ++ bs) = toffBlocksGates as ++ toffBlocksGates bs :=
  List.flatMap_append

/-- Expanding the adjoint of a block list gives the adjoint of its expanded gate word. -/
theorem toffBlocksGates_adj {N : ℕ} (bs : List (ToffBlock N)) :
    toffBlocksGates (toffBlocksAdj bs) = reflectionAdjoint (toffBlocksGates bs) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have h1 : toffBlocksAdj (b :: bs) = toffBlocksAdj bs ++ [b.adj] := by
      simp [toffBlocksAdj]
    rw [h1, toffBlocksGates_append, ih]
    simp only [toffBlocksGates_cons, toffBlocksGates_nil, List.append_nil,
      ← toffBlockGates_adj b, toffBlocksGates_cons, reflectionAdjoint_append']

/-- Counts the relative Toffoli blocks in a block list. -/
def relCount {N : ℕ} : List (ToffBlock N) → ℕ
  | [] => 0
  | .rel _ _ _ :: bs => relCount bs + 1
  | _ :: bs => relCount bs

/-- Counts exact Toffoli blocks and their adjoints in a block list. -/
def exactCount {N : ℕ} : List (ToffBlock N) → ℕ
  | [] => 0
  | .exact _ _ _ :: bs => exactCount bs + 1
  | .exactAdj _ _ _ :: bs => exactCount bs + 1
  | _ :: bs => exactCount bs

/-- The total count of relative and exact Toffoli blocks, including adjoint exact blocks. -/
def toffCount {N : ℕ} (bs : List (ToffBlock N)) : ℕ := relCount bs + exactCount bs

/-- Taking the adjoint of a block list preserves its length. -/
theorem toffBlocksAdj_length {N : ℕ} (bs : List (ToffBlock N)) :
    (toffBlocksAdj bs).length = bs.length := by
  simp [toffBlocksAdj]

/-- The relative Toffoli count is additive under append. -/
theorem relCount_append {N : ℕ} (as bs : List (ToffBlock N)) :
    relCount (as ++ bs) = relCount as + relCount bs := by
  induction as with
  | nil => simp [relCount]
  | cons a as ih =>
      cases a <;> simp only [relCount, List.cons_append, ih]
      all_goals omega

/-- The exact Toffoli count is additive under append. -/
theorem exactCount_append {N : ℕ} (as bs : List (ToffBlock N)) :
    exactCount (as ++ bs) = exactCount as + exactCount bs := by
  induction as with
  | nil => simp [exactCount]
  | cons a as ih =>
      cases a <;> simp only [exactCount, List.cons_append, ih]
      all_goals omega

/-- Taking the adjoint of a block list preserves its relative Toffoli count. -/
theorem relCount_toffBlocksAdj {N : ℕ} (bs : List (ToffBlock N)) :
    relCount (toffBlocksAdj bs) = relCount bs := by
  induction bs with
  | nil => simp [toffBlocksAdj, relCount]
  | cons b bs ih =>
    have h1 : toffBlocksAdj (b :: bs) = toffBlocksAdj bs ++ [b.adj] := by
      simp [toffBlocksAdj]
    rw [h1, relCount_append, ih]
    cases b <;> simp [relCount, ToffBlock.adj]

/-- Taking the adjoint of a block list preserves its exact Toffoli count. -/
theorem exactCount_toffBlocksAdj {N : ℕ} (bs : List (ToffBlock N)) :
    exactCount (toffBlocksAdj bs) = exactCount bs := by
  induction bs with
  | nil => simp [toffBlocksAdj, exactCount]
  | cons b bs ih =>
    have h1 : toffBlocksAdj (b :: bs) = toffBlocksAdj bs ++ [b.adj] := by
      simp [toffBlocksAdj]
    rw [h1, exactCount_append, ih]
    cases b <;> simp [exactCount, ToffBlock.adj]

/-- The recursive block representation of the compressed dirty-prefix ladder. -/
def prefixBlocks {N : ℕ} (c w : ℕ → Fin N) : ℕ → List (ToffBlock N)
  | 0 => []
  | 1 => [.single (w 0) (qubitEulerRotation (-Real.pi/4)),
      .rel (c 0) (c 1) (w 0),
      .single (w 0) ((qubitEulerRotation (-Real.pi/4))ᴴ)]
  | r+2 =>
      [.single (w (r+1)) (qubitEulerRotation (-Real.pi/4)),
        .rel (c (r+2)) (w r) (w (r+1))]
        ++ prefixBlocks c w (r+1)
        ++ [.rel (c (r+2)) (w r) (w (r+1)),
          .single (w (r+1)) ((qubitEulerRotation (-Real.pi/4))ᴴ)]

/-- Expanding `prefixBlocks` gives the compressed prefix gate word. -/
theorem prefixBlocks_gates {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) :
    toffBlocksGates (prefixBlocks c w r) = sourcePrefixCompressed c w r := by
  induction r using Nat.twoStepInduction with
  | zero => rfl
  | one =>
      simp only [prefixBlocks, sourcePrefixCompressed, toffBlocksGates_cons,
        ToffBlock.gates, List.cons_append, List.nil_append]
      rfl
  | more r _ ih =>
      simp only [prefixBlocks, sourcePrefixCompressed, toffBlocksGates_append,
        toffBlocksGates_cons, ToffBlock.gates, List.append_assoc,
        List.cons_append, List.nil_append]
      rw [ih]
      rfl

/-- For `r ≥ 1`, the prefix block list has `2 * r - 1` relative blocks, no exact blocks, and
length `4 * r - 1`. -/
theorem prefixBlocks_census {N : ℕ} (c w : ℕ → Fin N) (r : ℕ) (hr : 1 ≤ r) :
    relCount (prefixBlocks c w r) = 2*r-1 ∧
    exactCount (prefixBlocks c w r) = 0 ∧
    (prefixBlocks c w r).length = 4*r-1 := by
  induction r using Nat.twoStepInduction with
  | zero => omega
  | one => simp [prefixBlocks, relCount, exactCount]
  | more r _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih (by omega)
      simp only [prefixBlocks, relCount_append, exactCount_append,
        List.length_append, relCount, exactCount, List.length_cons, List.length_nil]
      omega

/-- The relative borrowed core as a block list, alternating two relative middle blocks with two
prefix ladders. -/
def relCoreBlocks {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ) :
    List (ToffBlock N) :=
  [.rel (c (r+1)) (w (r-1)) s] ++ prefixBlocks c w r ++
    [.rel (c (r+1)) (w (r-1)) s] ++ prefixBlocks c w r

/-- Expanding the relative core blocks gives `sourceBorrowedRelativeCore`. -/
theorem relCoreBlocks_gates {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ) :
    toffBlocksGates (relCoreBlocks c w s r) = sourceBorrowedRelativeCore c w s r := by
  simp only [relCoreBlocks, sourceBorrowedRelativeCore, toffBlocksGates_append,
    toffBlocksGates_cons, ToffBlock.gates, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [prefixBlocks_gates]

/-- For `r ≥ 1`, the relative core has `4 * r` relative blocks, no exact blocks, and block-list
length `8 * r`. -/
theorem relCoreBlocks_census {N : ℕ} (c w : ℕ → Fin N) (s : Fin N) (r : ℕ) (hr : 1 ≤ r) :
    relCount (relCoreBlocks c w s r) = 4*r ∧
    exactCount (relCoreBlocks c w s r) = 0 ∧
    (relCoreBlocks c w s r).length = 8*r := by
  obtain ⟨h1, h2, h3⟩ := prefixBlocks_census c w r hr
  simp only [relCoreBlocks, relCount_append, exactCount_append,
    List.length_append, relCount, exactCount, List.length_cons, List.length_nil]
  omega

/-- The exact borrowed core as a block list, combining an exact middle block, its adjoint, and
two prefix ladders. -/
def exactCoreBlocks {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    List (ToffBlock N) :=
  [.exact (c (r+1)) (w (r-1)) t] ++ prefixBlocks c w r ++
    [.exactAdj (c (r+1)) (w (r-1)) t] ++ prefixBlocks c w r

/-- Expanding the exact core blocks gives `sourceBorrowedExactCore`. -/
theorem exactCoreBlocks_gates {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ) :
    toffBlocksGates (exactCoreBlocks c w t r) = sourceBorrowedExactCore c w t r := by
  simp only [exactCoreBlocks, sourceBorrowedExactCore, toffBlocksGates_append,
    toffBlocksGates_cons, ToffBlock.gates, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [prefixBlocks_gates]

/-- For `r ≥ 1`, the exact core has `4 * r - 2` relative blocks, two exact blocks, and
block-list length `8 * r`. -/
theorem exactCoreBlocks_census {N : ℕ} (c w : ℕ → Fin N) (t : Fin N) (r : ℕ)
    (hr : 1 ≤ r) :
    relCount (exactCoreBlocks c w t r) = 4*r-2 ∧
    exactCount (exactCoreBlocks c w t r) = 2 ∧
    (exactCoreBlocks c w t r).length = 8*r := by
  obtain ⟨h1, h2, h3⟩ := prefixBlocks_census c w r hr
  simp only [exactCoreBlocks, relCount_append, exactCount_append,
    List.length_append, relCount, exactCount, List.length_cons, List.length_nil]
  omega

/-- The block-list form of the packed commutator with merged single-wire frame gates. -/
def packedBlocks {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (as bs : List (ToffBlock N)) : List (ToffBlock N) :=
  [.single t Hadamard, .single s R] ++ as ++ [.single s (E*Rᴴ)] ++ bs ++
    [.single s (R*Eᴴ)] ++ toffBlocksAdj as ++ [.single s (E*Rᴴ)] ++ toffBlocksAdj bs ++
    [.single s Eᴴ, .single t Hadamard]

/-- Expanding the packed block list gives the packed elementary commutator built from the
expanded input lists. -/
theorem packedBlocks_gates {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (as bs : List (ToffBlock N)) :
    toffBlocksGates (packedBlocks s t R E as bs) =
      sourcePackedCommutator s t R E (toffBlocksGates as) (toffBlocksGates bs) := by
  have hA := toffBlocksGates_adj as
  have hB := toffBlocksGates_adj bs
  simp only [packedBlocks, sourcePackedCommutator, toffBlocksGates_append,
    toffBlocksGates_cons, toffBlocksGates_nil, ToffBlock.gates, List.append_assoc,
    List.cons_append, List.nil_append]
  rw [hA, hB]

/-- The packed commutator doubles the combined relative and exact block counts and has
block-list length `2 * as.length + 2 * bs.length + 7`. -/
theorem packedBlocks_census {N : ℕ} (s t : Fin N) (R E : Matrix Bool Bool ℂ)
    (as bs : List (ToffBlock N)) :
    relCount (packedBlocks s t R E as bs) = 2*(relCount as + relCount bs) ∧
    exactCount (packedBlocks s t R E as bs) = 2*(exactCount as + exactCount bs) ∧
    (packedBlocks s t R E as bs).length = 2*as.length + 2*bs.length + 7 := by
  simp only [packedBlocks, relCount_append, exactCount_append,
    relCount_toffBlocksAdj, exactCount_toffBlocksAdj, toffBlocksAdj_length,
    List.length_append, relCount, exactCount, List.length_cons, List.length_nil]
  constructor <;> omega

/-- The Corollary 7.4 block construction obtained by splitting the controls between a relative
borrowed core and an exact borrowed core. -/
def cor74Blocks {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) :
    List (ToffBlock N) :=
  let a := (m+1)/2
  let b := m/2
  let ra := a-2
  let rb := b-1
  let ca : ℕ → Fin N := c
  let wa : ℕ → Fin N := fun j => c (a+j)
  let cb : ℕ → Fin N := fun i => if i < b then c (a+i) else s
  let wb : ℕ → Fin N := c
  packedBlocks s t (qubitEulerRotation (-Real.pi/4)) tGate
    (relCoreBlocks ca wa s ra) (exactCoreBlocks cb wb t rb)

/-- The elementary gate word obtained by expanding the Corollary 7.4 block construction. -/
def cor74Word {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) :
    List (ReflectionGate N) :=
  toffBlocksGates (cor74Blocks m c s t)

/-- The expanded Corollary 7.4 word equals the packed commutator of the specified relative and
exact borrowed cores. -/
theorem cor74Word_eq {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) :
    cor74Word m c s t =
      sourcePackedCommutator s t (qubitEulerRotation (-Real.pi/4)) tGate
        (sourceBorrowedRelativeCore c (fun j => c ((m+1)/2+j)) s ((m+1)/2-2))
        (sourceBorrowedExactCore (fun i => if i < m/2 then c ((m+1)/2+i) else s) c t (m/2-1)) := by
  simp only [cor74Word, cor74Blocks]
  rw [packedBlocks_gates, relCoreBlocks_gates, exactCoreBlocks_gates]

/-- For `m ≥ 5`, the Corollary 7.4 construction has `8 * m - 28` relative blocks, four exact
blocks, and `8 * m - 24` Toffoli blocks in total [BarencoEtAl1995]. -/
theorem cor74Blocks_census {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    relCount (cor74Blocks m c s t) = 8*m-28 ∧
    exactCount (cor74Blocks m c s t) = 4 ∧
    toffCount (cor74Blocks m c s t) = 8*m-24 := by
  have hra : 1 ≤ (m+1)/2-2 := by omega
  have hrb : 1 ≤ m/2-1 := by omega
  have hsum : ((m+1)/2-2)+(m/2-1) = m-3 := by omega
  have hkey : cor74Blocks m c s t =
      packedBlocks s t (qubitEulerRotation (-Real.pi/4)) tGate
        (relCoreBlocks c (fun j => c ((m+1)/2+j)) s ((m+1)/2-2))
        (exactCoreBlocks (fun i => if i < m/2 then c ((m+1)/2+i) else s) c t (m/2-1)) := by
    simp only [cor74Blocks]
  rw [hkey]
  obtain ⟨ha1, _, _⟩ := relCoreBlocks_census c (fun j => c ((m+1)/2+j)) s ((m+1)/2-2) hra
  obtain ⟨hb1, hb2, _⟩ :=
    exactCoreBlocks_census (fun i => if i < m/2 then c ((m+1)/2+i) else s) c t (m/2-1) hrb
  obtain ⟨hp1, hp2, _⟩ :=
    packedBlocks_census s t (qubitEulerRotation (-Real.pi/4)) tGate
      (relCoreBlocks c (fun j => c ((m+1)/2+j)) s ((m+1)/2-2))
      (exactCoreBlocks (fun i => if i < m/2 then c ((m+1)/2+i) else s) c t (m/2-1))
  simp only [toffCount]
  constructor
  · omega
  · exact ⟨by omega, by omega⟩

/-- For `m ≥ 5`, the expanded Corollary 7.4 word has exactly `48 * m - 109` elementary gates
[BarencoEtAl1995]. -/
theorem cor74Word_length {N : ℕ} (m : ℕ) (c : ℕ → Fin N) (s t : Fin N) (hm : 5 ≤ m) :
    (cor74Word m c s t).length = 48*m-109 := by
  have hra : 1 ≤ (m+1)/2-2 := by omega
  have hrb : 1 ≤ m/2-1 := by omega
  have hAC :=
    (sourceBorrowedCore_lengths c (fun j => c ((m+1)/2+j)) s t ((m+1)/2-2) hra).1
  have hBC :=
    (sourceBorrowedCore_lengths (fun i => if i < m/2 then c ((m+1)/2+i) else s) c s t (m/2-1) hrb).2
  rw [cor74Word_eq, sourcePackedCommutator_length]
  omega

end Qatlib.Concepts.CircuitImpl.MultiControl
