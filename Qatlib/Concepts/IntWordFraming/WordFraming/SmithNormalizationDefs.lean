/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.FourierRecoveryDefs
import Qatlib.Concepts.HspRecovery.JointDlog.JointBezoutDlogDecoder
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Nat.Size

/-!
# Normalized Smith data and counted reduction

This module packages integer presentation reduction as `NormalizedSmithData`, retaining cyclic
coordinates whose moduli differ from one. It defines signed binary inputs, coordinate
conversion, generator words, and compact group presentations in the setting of
[CheungMosca2001].

Counted variants of the reduction record abstract kernel operations and Euclidean
quotient-remainder work. `SmithKernelCounts` and `SmithEuclidWork` keep these two accounting
layers explicit.

## Main statements

* `normalizedSmith`: compute reduction data and retain nontrivial cyclic factors.
* `CompactAbelianPresentation.Valid`: generation and completeness of the given relations.
* `smithRunBinaryEuclid`: reduce binary input while recording both accounting layers.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CfOrder

set_option autoImplicit false
namespace Qatlib.Concepts.IntWordFraming.WordFraming

open Matrix

/-- Presentation reduction data together with a vector of moduli and a list of retained
coordinate indices. -/
structure NormalizedSmithData (m n : ℕ) where
  reduction : PresentationReduction m n
  moduli : Vector ℕ m
  retained : List (Fin m)

/-- The stored modulus of coordinate `r`. -/
def NormalizedSmithData.coeff {m n : ℕ} (p : NormalizedSmithData m n) (r : Fin m) : ℕ :=
  p.moduli[r.val]

/-- Compute a rectangular Smith reduction, take absolute diagonal moduli, and retain exactly the
indices whose moduli differ from one. -/
def normalizedSmith {m n : ℕ} (rows : Vector (Vector ℤ n) m) : NormalizedSmithData m n :=
  let s := rectangularSmith (tableMatrix rows)
  let d := Vector.ofFn (fun r : Fin m => (diagonalCoefficient s.value r).natAbs)
  { reduction := s
    moduli := d
    retained := (List.finRange m).filter (fun r => d[r.val] != 1) }

/-- List the stored moduli at the retained indices. -/
def NormalizedSmithData.factors {m n : ℕ} (p : NormalizedSmithData m n) : List ℕ :=
  p.retained.map p.coeff

/-- List the columns of the inverse left transformation at the retained indices as integer
generator words. -/
def NormalizedSmithData.generatorWords {m n : ℕ} (p : NormalizedSmithData m n) :
    List (Vector ℤ m) :=
  p.retained.map (fun r => Vector.ofFn (fun i => p.reduction.leftInverse i r))

/-- Decide whether every stored modulus is nonzero. -/
def NormalizedSmithData.isFinite {m n : ℕ} (p : NormalizedSmithData m n) : Bool :=
  decide (∀ r : Fin m, p.coeff r ≠ 0)

/-- The family of residue coordinates indexed by positions whose stored modulus differs from
one. -/
abbrev NormalizedCoordinates {m n : ℕ} (p : NormalizedSmithData m n) :=
  ∀ r : {r : Fin m // p.coeff r ≠ 1}, ZMod (p.coeff r)

/-- Extend normalized residue coordinates to all indices by inserting zero at positions of
modulus one. -/
def inflateNormalized {m n : ℕ} (p : NormalizedSmithData m n) (z : NormalizedCoordinates p)
    (r : Fin m) : ZMod (p.coeff r) :=
  if h : p.coeff r ≠ 1 then z ⟨r,h⟩ else 0

/-- Transform an integer word by the stored left matrix and reduce its coordinates at all
positions of modulus different from one. -/
def normalizedEncode {m n : ℕ} (p : NormalizedSmithData m n) (v : Fin m → ℤ) :
    NormalizedCoordinates p :=
  fun r => ((p.reduction.left *ᵥ v) r : ZMod (p.coeff r))

/-- Inflate normalized coordinates, cast them to integers, and apply the stored inverse left
transformation. -/
def normalizedDecode {m n : ℕ} (p : NormalizedSmithData m n) (z : NormalizedCoordinates p) :
    Fin m → ℤ :=
  p.reduction.leftInverse *ᵥ (fun r => (ZMod.cast (inflateNormalized p z r) : ℤ))

/-- Decide whether two words have equal normalized residue coordinates. -/
def normalizedWordEq {m n : ℕ} (p : NormalizedSmithData m n) (u v : Fin m → ℤ) : Bool :=
  decide (∀ r, normalizedEncode p u r = normalizedEncode p v r)

/-- The product of the gcds of `k` with all retained factors. -/
def NormalizedSmithData.torsionProfile {m n : ℕ} (p : NormalizedSmithData m n) (k : ℕ) : ℕ :=
  (p.factors.map (fun d => Nat.gcd d k)).prod

/-- The integer linear map sending a coefficient vector to the corresponding integer combination
of the generators in `g`. -/
def generatorWordMap {C : Type*} [AddCommGroup C] {m : ℕ} (g : Vector C m) :
    (Fin m → ℤ) →ₗ[ℤ] C :=
  ∑ r : Fin m, (LinearMap.proj r).smulRight g[r.val]

/-- A finite integer relation table and a vector of generators in an additive commutative group. -/
structure CompactAbelianPresentation (C : Type*) [AddCommGroup C] (m n : ℕ) where
  relations : Vector (Vector ℤ n) m
  generators : Vector C m

/-- The generators span the group and the kernel of their word map equals the range of the
relation matrix. -/
structure CompactAbelianPresentation.Valid {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) : Prop where
  generates : Function.Surjective (generatorWordMap p.generators)
  relations_complete : LinearMap.ker (generatorWordMap p.generators) =
    LinearMap.range (tableMatrix p.relations).mulVecLin

/-- Compute normalized Smith data from the relation table of a compact presentation. -/
def CompactAbelianPresentation.run {C : Type*} [AddCommGroup C] {m n : ℕ}
    (p : CompactAbelianPresentation C m n) : NormalizedSmithData m n :=
  normalizedSmith p.relations

/-- A signed binary integer representation consisting of a sign bit and a list of magnitude
bits. -/
abbrev SmithIntegerCode := Bool × List Bool

/-- Interpret a Boolean list as a natural number by folding `Nat.bit` from the right. -/
def smithDecodeNat (bits : List Bool) : ℕ := bits.foldr Nat.bit 0

/-- Encode an integer by its negativity bit and the binary digits of its absolute value. -/
def smithEncodeInteger (z : ℤ) : SmithIntegerCode := (decide (z < 0), z.natAbs.bits)

/-- Decode a sign bit and binary magnitude into an integer. -/
def smithDecodeInteger (z : SmithIntegerCode) : ℤ :=
  if z.1 then -(smithDecodeNat z.2 : ℤ) else (smithDecodeNat z.2 : ℤ)

/-- Encode every entry of an integer relation table as a signed binary integer. -/
def smithEncodeRelations {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    Vector (Vector SmithIntegerCode n) m :=
  rows.map (fun row => row.map smithEncodeInteger)

/-- Decode every signed binary entry of a relation table into an integer. -/
def smithDecodeRelations {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    Vector (Vector ℤ n) m := rows.map (fun row => row.map smithDecodeInteger)

/-- Decode a binary relation table and compute its normalized Smith data. -/
def smithRunBinary {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) : NormalizedSmithData m n :=
  normalizedSmith (smithDecodeRelations rows)

/-- Count one sign bit plus the magnitude payload length for every entry of a binary relation
table. -/
def smithRelationBits {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) : ℕ :=
  ∑ i : Fin m, ∑ j : Fin n, (1 + (rows[i.val][j.val]).2.length)

/-- Encode each retained modulus as a list of binary digits. -/
def NormalizedSmithData.binaryFactors {m n : ℕ} (p : NormalizedSmithData m n) : List (List Bool) :=
  p.factors.map Nat.bits

/-- Encode the retained integer generator words entrywise as signed binary integers. -/
def NormalizedSmithData.binaryGeneratorWords {m n : ℕ} (p : NormalizedSmithData m n) :
    List (Vector SmithIntegerCode m) :=
  p.generatorWords.map (fun w => w.map smithEncodeInteger)

/-- Sum the binary factor payload lengths and the signed binary generator-word lengths. -/
def NormalizedSmithData.outputPayloadBits {m n : ℕ} (p : NormalizedSmithData m n) : ℕ :=
  (p.binaryFactors.map List.length).sum +
    (p.binaryGeneratorWords.map (fun w => ∑ i : Fin m, (1 + w[i.val].2.length))).sum

/-- Find the first list element satisfying `p` and record the number of predicate tests
performed. -/
def smithFindCounted {α : Type*} (p : α → Bool) : List α → Option α × ℕ
  | [] => (none,0)
  | a :: as => if p a then (some a,1) else
      let s := smithFindCounted p as
      (s.1,s.2+1)

/-- Decide whether `P` holds at every finite index, recording the number of indices tested
before success or the first failure. -/
def smithCheckAllFin {m : ℕ} (P : Fin m → Prop) [DecidablePred P] : Bool × ℕ :=
  let s := smithFindCounted (fun i => decide (¬ P i)) (List.finRange m)
  (s.1.isNone,s.2)

/-- The operation categories used to account for divisibility tests, matrix reduction steps,
tabulation, and allocated pivot fuel. -/
inductive SmithKernelOp where
  | columnDivTest | rowDivTest | residualDivTest | nonzeroTest
  | pivotRound | columnSweep | rowSweep | clearPivot | exposeRow
  | movePivot | basisCompose | liftResidual | rectangularFrame | tabulateCell | pivotFuelAllocated
  deriving DecidableEq, Repr

/-- A natural-number count for each Smith kernel operation category. -/
abbrev SmithKernelCounts := SmithKernelOp → ℕ

/-- Assign count `n` to operation `op` and zero to every other operation. -/
def smithCharge (op : SmithKernelOp) (n : ℕ) : SmithKernelCounts :=
  fun k => if k = op then n else 0

/-- Run the fuel-bounded pivot isolation procedure while accumulating Smith kernel operation
counts. -/
def countedIsolatePivotLoop {m n : ℕ} : ℕ → Matrix (Fin (m+1)) (Fin (n+1)) ℤ →
    PresentationReduction (m+1) (n+1) × SmithKernelCounts
  | 0, A => (PresentationReduction.identity A,0)
  | fuel+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    let col := smithCheckAllFin (fun r => A 0 0 ∣ A r 0)
    let base := smithCharge .pivotRound 1 + smithCharge .tabulateCell ((m+1)*(n+1)) +
      smithCharge .columnDivTest col.2
    if col.1 then
      let row := smithCheckAllFin (fun c => A 0 0 ∣ A 0 c)
      let base := base + smithCharge .rowDivTest row.2
      if row.1 then
        let s := clearPivot A
        let found := smithFindCounted (fun rc => decide (¬ s.value 0 0 ∣ s.value rc.1 rc.2))
          ((List.finRange (m+1)).product (List.finRange (n+1)))
        let base := base + smithCharge .clearPivot 1 + smithCharge .basisCompose 1 +
          smithCharge .residualDivTest found.2
        match found.1 with
        | none => (s,base)
        | some rc =>
          let e := (exposeRow rc.1 s.value).toReduction
          let t := (rowReduce 0 e.value).toReduction
          let tail := countedIsolatePivotLoop fuel t.value
          (s.then (e.then (t.then tail.1)),
            base + smithCharge .exposeRow 1 + smithCharge .rowSweep 1 +
              smithCharge .basisCompose 3 + tail.2)
      else
        let s := (rowReduce 0 A).toReduction
        let tail := countedIsolatePivotLoop fuel s.value
        (s.then tail.1,base + smithCharge .rowSweep 1 + smithCharge .basisCompose 1 + tail.2)
    else
      let s := (columnReduce 0 A).toReduction
      let tail := countedIsolatePivotLoop fuel s.value
      (s.then tail.1,base + smithCharge .columnSweep 1 + smithCharge .basisCompose 1 + tail.2)

/-- Run counted pivot isolation with absolute-pivot fuel plus one, recording the allocated fuel
as well. -/
def countedIsolatePivot {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    PresentationReduction (m+1) (n+1) × SmithKernelCounts :=
  let fuel := (A 0 0).natAbs+1
  let s := countedIsolatePivotLoop fuel A
  (s.1,s.2 + smithCharge .pivotFuelAllocated fuel)

/-- Recursively reduce a rectangular integer matrix while recording its kernel operation counts. -/
def countedRectangularSmith : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ →
    PresentationReduction m n × SmithKernelCounts
  | 0, _, A => (PresentationReduction.identity A,smithCharge .rectangularFrame 1)
  | _+1, 0, A => (PresentationReduction.identity A,smithCharge .rectangularFrame 1)
  | m+1, n+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    let found := smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
      ((List.finRange (m+1)).product (List.finRange (n+1)))
    let base := smithCharge .rectangularFrame 1 + smithCharge .tabulateCell ((m+1)*(n+1)) +
      smithCharge .nonzeroTest found.2
    match found.1 with
    | none => (PresentationReduction.identity A,base)
    | some rc =>
      let s := movePivot rc A
      let t := countedIsolatePivot s.value
      let u := countedRectangularSmith (t.1.value.submatrix Fin.succ Fin.succ)
      (s.then (t.1.then (u.1.lift (t.1.value 0 0))),
        base + smithCharge .movePivot 1 + smithCharge .basisCompose 3 +
          smithCharge .liftResidual 1 + t.2 + u.2)

/-- The componentwise operation budget assigned to one pivot round on a matrix of the given
dimensions. -/
def smithPivotRoundBudget (rows cols : ℕ) : SmithKernelCounts := fun op =>
  match op with
  | .columnDivTest => rows
  | .rowDivTest => cols
  | .residualDivTest | .tabulateCell => rows*cols
  | .pivotRound | .columnSweep | .rowSweep | .clearPivot | .exposeRow => 1
  | .basisCompose => 4
  | _ => 0

/-- The componentwise rectangular reduction budget determined by row count, column count, and
total pivot fuel. -/
def smithRectangularBudget (rows cols fuel : ℕ) : SmithKernelCounts := fun op =>
  match op with
  | .columnDivTest => rows*fuel
  | .rowDivTest => cols*fuel
  | .residualDivTest => rows*cols*fuel
  | .nonzeroTest => rows*cols*min rows cols
  | .pivotRound | .columnSweep | .rowSweep | .clearPivot | .exposeRow | .pivotFuelAllocated => fuel
  | .movePivot | .liftResidual => min rows cols
  | .basisCompose => 4*fuel + 3*min rows cols
  | .rectangularFrame => min rows cols+1
  | .tabulateCell => rows*cols*(fuel+min rows cols)

/-- Package a computed reduction with its absolute diagonal moduli and the indices of moduli
different from one. -/
def smithNormalizeComputedReduction {m n : ℕ} (s : PresentationReduction m n) :
    NormalizedSmithData m n :=
  let d := Vector.ofFn (fun r : Fin m => (diagonalCoefficient s.value r).natAbs)
  { reduction := s, moduli := d, retained := (List.finRange m).filter (fun r => d[r.val] != 1) }

/-- Compute normalized Smith data from an integer relation table together with kernel operation
counts. -/
def countedNormalizedSmith {m n : ℕ} (rows : Vector (Vector ℤ n) m) :
    NormalizedSmithData m n × SmithKernelCounts :=
  let s := countedRectangularSmith (tableMatrix rows)
  (smithNormalizeComputedReduction s.1,s.2)

/-- Decode a binary relation table and compute normalized Smith data with kernel operation
counts. -/
def countedSmithRunBinary {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    NormalizedSmithData m n × SmithKernelCounts := countedNormalizedSmith (smithDecodeRelations rows)

/-- Compute a Bezout row transformation and its inverse using the counted Euclidean routine,
returning its quotient-remainder count. -/
@[noinline] def smithEuclidPairCounted (a b : ℤ) :
    (Matrix (Fin 2) (Fin 2) ℤ × Matrix (Fin 2) (Fin 2) ℤ) × ℕ :=
  let e := Qatlib.Concepts.HspRecovery.CfOrder.cyclicDlogEuclid a.natAbs 1 0 b.natAbs 0 1
  let d := e.1.1
  let s := if a < 0 then -e.1.2.1 else e.1.2.1
  let t := if b < 0 then -e.1.2.2 else e.1.2.2
  if d = 0 then ((1,1),e.2) else
    let qa := a / (d : ℤ)
    let qb := b / (d : ℤ)
    ((!![s,t;-qb,qa],!![qa,-t;qb,s]),e.2)

/-- Euclidean work statistics: the number of calls, quotient-remainder pairs, and peak
input-pair bit length. -/
structure SmithEuclidWork where
  calls : ℕ
  quotRemPairs : ℕ
  peakPairInputBits : ℕ
  deriving Repr, DecidableEq

/-- Euclidean work statistics with all three fields zero. -/
def SmithEuclidWork.zero : SmithEuclidWork := ⟨0,0,0⟩

/-- Combine work statistics by adding call and quotient-remainder counts and taking the maximum
input bit length. -/
def SmithEuclidWork.append (a b : SmithEuclidWork) : SmithEuclidWork :=
  ⟨a.calls+b.calls,a.quotRemPairs+b.quotRemPairs,max a.peakPairInputBits b.peakPairInputBits⟩

/-- The quotient-remainder count is at most the call count times twice the peak pair input bit
length plus two per call. -/
def SmithEuclidWork.Valid (w : SmithEuclidWork) : Prop :=
  w.quotRemPairs ≤ w.calls*(2*w.peakPairInputBits+2)

/-- Perform one Euclidean row mixing step in column `p`, recording the call count,
quotient-remainder count, and input bit length. -/
def smithColumnStepCounted {m n : ℕ} (p : Fin n) (s : ColumnEliminationState (m+1) n)
    (k : Fin m) : ColumnEliminationState (m+1) n × SmithEuclidWork :=
  let a := s.value 0 p
  let b := s.value k.succ p
  let e := smithEuclidPairCounted a b
  (⟨rowMix 0 k.succ e.1.1 s.value, rowMix 0 k.succ e.1.1 s.left,
      s.inverse * rowMix 0 k.succ e.1.2 1⟩,
    ⟨1,e.2,(max a.natAbs b.natAbs).size⟩)

/-- Fold counted column steps over the given row indices, accumulating Euclidean work in `w`. -/
def smithColumnFoldCounted {m n : ℕ} (p : Fin n)
    (ks : List (Fin m)) (s : ColumnEliminationState (m+1) n) (w : SmithEuclidWork) :
    ColumnEliminationState (m+1) n × SmithEuclidWork :=
  ks.foldl (fun acc k =>
    let step := smithColumnStepCounted p acc.1 k
    (step.1,acc.2.append step.2)) (s,w)

/-- Reduce column `p` with Euclidean row operations while accumulating Euclidean work
statistics. -/
def smithColumnReduceCounted {m n : ℕ} (p : Fin n) (A : Matrix (Fin (m+1)) (Fin n) ℤ) :
    ColumnEliminationState (m+1) n × SmithEuclidWork :=
  smithColumnFoldCounted p (List.finRange m) ⟨A,1,1⟩ SmithEuclidWork.zero

/-- Reduce row `p` through the counted transpose construction, preserving the accumulated
Euclidean work statistics. -/
def smithRowReduceCounted {m n : ℕ} (p : Fin m) (A : Matrix (Fin m) (Fin (n+1)) ℤ) :
    RowEliminationState m (n+1) × SmithEuclidWork :=
  let s := smithColumnReduceCounted p A.transpose
  (⟨s.1.value.transpose,s.1.left.transpose,s.1.inverse.transpose⟩,s.2)

/-- List the integer pairs supplied to consecutive column reduction steps along the specified
row indices. -/
def smithColumnEuclidInputs {m n : ℕ} (p : Fin n) :
    List (Fin m) → ColumnEliminationState (m+1) n → List (ℤ × ℤ)
  | [], _ => []
  | k :: ks, s => (s.value 0 p,s.value k.succ p) :: smithColumnEuclidInputs p ks (columnStep p s k)

/-- The bit length of the larger absolute value in an integer pair. -/
def smithPairInputBits (ab : ℤ × ℤ) : ℕ := (max ab.1.natAbs ab.2.natAbs).size

/-- Presentation reduction data paired with kernel operation counts and Euclidean work
statistics. -/
abbrev SmithEuclidRun (m n : ℕ) :=
  (PresentationReduction m n × SmithKernelCounts) × SmithEuclidWork

/-- Run fuel-bounded pivot isolation while recording both kernel operation counts and Euclidean
work statistics. -/
def smithIsolatePivotEuclidLoop {m n : ℕ} : ℕ → Matrix (Fin (m+1)) (Fin (n+1)) ℤ →
    SmithEuclidRun (m+1) (n+1)
  | 0, A => ((PresentationReduction.identity A,0),SmithEuclidWork.zero)
  | fuel+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    let col := smithCheckAllFin (fun r => A 0 0 ∣ A r 0)
    let base := smithCharge .pivotRound 1 + smithCharge .tabulateCell ((m+1)*(n+1)) +
      smithCharge .columnDivTest col.2
    if col.1 then
      let row := smithCheckAllFin (fun c => A 0 0 ∣ A 0 c)
      let base := base + smithCharge .rowDivTest row.2
      if row.1 then
        let s := clearPivot A
        let found := smithFindCounted (fun rc => decide (¬ s.value 0 0 ∣ s.value rc.1 rc.2))
          ((List.finRange (m+1)).product (List.finRange (n+1)))
        let base := base + smithCharge .clearPivot 1 + smithCharge .basisCompose 1 +
          smithCharge .residualDivTest found.2
        match found.1 with
        | none => ((s,base),SmithEuclidWork.zero)
        | some rc =>
          let e := (exposeRow rc.1 s.value).toReduction
          let t := smithRowReduceCounted 0 e.value
          let tail := smithIsolatePivotEuclidLoop fuel t.1.value
          ((s.then (e.then (t.1.toReduction.then tail.1.1)),
            base + smithCharge .exposeRow 1 + smithCharge .rowSweep 1 +
              smithCharge .basisCompose 3 + tail.1.2),t.2.append tail.2)
      else
        let s := smithRowReduceCounted 0 A
        let tail := smithIsolatePivotEuclidLoop fuel s.1.value
        ((s.1.toReduction.then tail.1.1,
          base + smithCharge .rowSweep 1 + smithCharge .basisCompose 1 + tail.1.2),s.2.append tail.2)
    else
      let s := smithColumnReduceCounted 0 A
      let tail := smithIsolatePivotEuclidLoop fuel s.1.value
      ((s.1.toReduction.then tail.1.1,
        base + smithCharge .columnSweep 1 + smithCharge .basisCompose 1 + tail.1.2),s.2.append tail.2)

/-- Run pivot isolation with absolute-pivot fuel plus one, recording allocated fuel and
Euclidean work. -/
def smithIsolatePivotEuclid {m n : ℕ} (A : Matrix (Fin (m+1)) (Fin (n+1)) ℤ) :
    SmithEuclidRun (m+1) (n+1) :=
  let fuel := (A 0 0).natAbs+1
  let s := smithIsolatePivotEuclidLoop fuel A
  ((s.1.1,s.1.2+smithCharge .pivotFuelAllocated fuel),s.2)

/-- Recursively reduce a rectangular integer matrix while recording kernel operations and
Euclidean work. -/
def smithRectangularEuclid : {m n : ℕ} → Matrix (Fin m) (Fin n) ℤ → SmithEuclidRun m n
  | 0, _, A => ((PresentationReduction.identity A,smithCharge .rectangularFrame 1),SmithEuclidWork.zero)
  | _+1, 0, A => ((PresentationReduction.identity A,smithCharge .rectangularFrame 1),SmithEuclidWork.zero)
  | m+1, n+1, A =>
    let rows := matrixTable A
    let A := tableMatrix rows
    let found := smithFindCounted (fun rc => decide (A rc.1 rc.2 ≠ 0))
      ((List.finRange (m+1)).product (List.finRange (n+1)))
    let base := smithCharge .rectangularFrame 1 + smithCharge .tabulateCell ((m+1)*(n+1)) +
      smithCharge .nonzeroTest found.2
    match found.1 with
    | none => ((PresentationReduction.identity A,base),SmithEuclidWork.zero)
    | some rc =>
      let s := movePivot rc A
      let t := smithIsolatePivotEuclid s.value
      let u := smithRectangularEuclid (t.1.1.value.submatrix Fin.succ Fin.succ)
      ((s.then (t.1.1.then (u.1.1.lift (t.1.1.value 0 0))),
        base + smithCharge .movePivot 1 + smithCharge .basisCompose 3 +
          smithCharge .liftResidual 1 + t.1.2 + u.1.2),t.2.append u.2)

/-- Decode binary relations and return normalized Smith data together with kernel counts and
Euclidean work statistics. -/
def smithRunBinaryEuclid {m n : ℕ} (rows : Vector (Vector SmithIntegerCode n) m) :
    (NormalizedSmithData m n × SmithKernelCounts) × SmithEuclidWork :=
  let s := smithRectangularEuclid (tableMatrix (smithDecodeRelations rows))
  ((smithNormalizeComputedReduction s.1.1,s.1.2),s.2)

end Qatlib.Concepts.IntWordFraming.WordFraming
