/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Finite data loading and access models

This module defines rational complex amplitudes, dense and sparse table loaders, phase
approximations, and preparation matrices. `LoadedInput` records amplitudes and loading counts,
while option slots and `slotEquiv` place the data in a finite qubit register with a
distinguished pivot.

The state and circuit constructions use the finite-dimensional framework of [NielsenChuang2010].
`AccessContract`, `ResourceAccount`, and `AccessCost` specify the preconditions and charges used
to account for table construction, preparation, and subsequent access.

## Main statements

* `denseLoader_reads_card_ge`: universal dense recovery requires reading at least every table
  entry.
* `loadDense` and `loadSparse`: nonzero-mass loaders with explicit read counts.
* `prepareMatrix` and `physPrepare`: preparation in option-slot and register coordinates.
* `AccessContract.totalCharge`: the setup and repeated-access charge.
* `physAccount`: the declared physical preparation resource account.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

namespace Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs

open Matrix
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

/-- Complex coordinates represented by a pair of rational numbers. -/
abbrev RatComplex := ℚ × ℚ

/-- The rational complex number with both coordinates zero. -/
def ratZero : RatComplex := (0, 0)

/-- The complex number whose real and imaginary coordinates are the given rationals. -/
def ratToComplex (z : RatComplex) : ℂ :=
  Complex.ofReal (z.1 : ℝ) + Complex.ofReal (z.2 : ℝ) * Complex.I

/-- The rational squared modulus, equal to the sum of the squared coordinates. -/
def ratSq (z : RatComplex) : ℚ := z.1 ^ 2 + z.2 ^ 2

/-- The rational squared modulus is nonnegative. -/
theorem ratSq_nonneg (z : RatComplex) : 0 ≤ ratSq z := by
  have h1 : 0 ≤ (z.1 : ℚ) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (z.2 : ℚ) ^ 2 := sq_nonneg _
  exact add_nonneg h1 h2

/-- A rational sign equal to `-1` on negative inputs and `1` otherwise. -/
def ratSign (q : ℚ) : ℚ := if q < 0 then -1 else 1

/-- Multiplication of the absolute value by `ratSign` recovers the rational input. -/
theorem ratSign_mul_abs (q : ℚ) : ratSign q * |q| = q := by
  by_cases h : q < 0
  · rw [ratSign, if_pos h, abs_of_neg h]; ring
  · rw [ratSign, if_neg h, abs_of_nonneg (le_of_not_gt h)]; ring

/-- A table of `D` rational complex amplitudes. -/
abbrev DenseTable (D : ℕ) := Fin D → RatComplex

/-- A sparse table entry consisting of a natural-number position and a rational complex value. -/
structure SparseEntry where

  position : ℕ

  value : RatComplex
  deriving DecidableEq, Repr

/-- A dense-table loader specified by the finite set of entries it reads and a decoder acting on
the resulting view. -/
structure DenseLoader (D : ℕ) where

  reads : Finset (Fin D)

  decode : (Fin D → RatComplex) → Fin D → RatComplex

/-- The loader's view of a dense table, retaining read entries and replacing all other entries
by zero. -/
def DenseLoader.view {D : ℕ} (L : DenseLoader D) (xs : DenseTable D) : Fin D → RatComplex :=
  fun i => if i ∈ L.reads then xs i else ratZero

/-- The table produced by applying the loader's decoder to its restricted input view. -/
def DenseLoader.run {D : ℕ} (L : DenseLoader D) (xs : DenseTable D) : Fin D → RatComplex :=
  fun a => L.decode (L.view xs) a

/-- The loader that reads every entry and returns the resulting table unchanged. -/
def fullDenseLoader (D : ℕ) : DenseLoader D where
  reads := Finset.univ
  decode := fun v a => v a

/-- The full dense loader returns the original value at every address. -/
theorem fullDenseLoader_run (D : ℕ) (xs : DenseTable D) (a : Fin D) :
    (fullDenseLoader D).run xs a = xs a := by
  simp [DenseLoader.run, fullDenseLoader, DenseLoader.view]

/-- The full dense loader reads exactly `D` distinct entries. -/
theorem fullDenseLoader_reads (D : ℕ) :
    (fullDenseLoader D).reads.card = D := by
  simp [fullDenseLoader]

/-- A loader that returns every entry correctly on every dense table must read at least `D`
distinct entries. -/
theorem denseLoader_reads_card_ge (D : ℕ) (L : DenseLoader D)
    (h : ∀ (xs : DenseTable D) (a : Fin D), L.run xs a = xs a) :
    D ≤ L.reads.card := by
  have hmem : ∀ a : Fin D, a ∈ L.reads := by
    intro a
    by_contra ha
    have hna : a ∉ L.reads := by simpa using ha
    let xs : DenseTable D := fun _ => ratZero
    let ys : DenseTable D := fun i => if i = a then (1, 0) else ratZero
    have hview : L.view xs = L.view ys := by
      funext i
      by_cases hi : i ∈ L.reads
      · have hia : i ≠ a := by
          intro e
          subst e
          exact hna hi
        simp [DenseLoader.view, hi, hia, xs, ys]
      · simp [DenseLoader.view, hi]
    have hone : L.run xs a = L.run ys a := by
      rw [DenseLoader.run, DenseLoader.run, hview]
    have hxs : L.run xs a = xs a := h xs a
    have hys : L.run ys a = ys a := h ys a
    have hz : xs a = ys a := hxs.symm.trans (hone.trans hys)
    simp [xs, ys, ratZero] at hz
  have hsub : (Finset.univ : Finset (Fin D)) ⊆ L.reads := by
    intro a ha
    exact hmem a
  have hcard := Finset.card_le_card hsub
  simpa using hcard

/-- Loaded rational complex amplitudes together with recorded read and support counts. -/
structure LoadedInput (D : ℕ) where

  amplitude : Fin D → RatComplex

  reads : ℕ

  support : ℕ

/-- The total squared modulus of the loaded amplitudes. -/
def LoadedInput.mass {D : ℕ} (L : LoadedInput D) : ℚ :=
  ∑ i : Fin D, ratSq (L.amplitude i)

/-- The loaded amplitudes extended by zero at the additional `none` slot. -/
def LoadedInput.amp {D : ℕ} (L : LoadedInput D) : Option (Fin D) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some i => L.amplitude i

/-- The squared moduli of the loaded amplitudes, extended by zero at the `none` slot. -/
def LoadedInput.weights {D : ℕ} (L : LoadedInput D) : Option (Fin D) → ℚ :=
  fun a => match a with
    | none => 0
    | some i => ratSq (L.amplitude i)

/-- The total rational weight of a loaded input equals its mass. -/
theorem LoadedInput.mass_eq {D : ℕ} (L : LoadedInput D) :
    rationalWeightMass L.weights = L.mass := by
  unfold rationalWeightMass LoadedInput.weights LoadedInput.mass
  rw [Fintype.sum_option]
  simp

/-- Every loaded input weight is nonnegative. -/
theorem LoadedInput.weights_nonneg {D : ℕ} (L : LoadedInput D) (a : Option (Fin D)) :
    0 ≤ L.weights a := by
  cases a with
  | none => simp [LoadedInput.weights]
  | some i => exact ratSq_nonneg _

/-- Loads a dense table of nonzero mass, recording `D` reads and its nonzero support size;
returns `none` for zero mass. -/
def loadDense (D : ℕ) (xs : DenseTable D) : Option (LoadedInput D) :=
  if (∑ i : Fin D, ratSq (xs i)) = 0 then none
  else some (LoadedInput.mk xs D (Finset.univ.filter (fun i => xs i ≠ ratZero)).card)

/-- Resolves an address by taking its last value in the sparse entry list, or zero if no entry
matches. -/
def sparseResolve {D : ℕ} (es : List SparseEntry) (a : Fin D) : RatComplex :=
  es.foldl (fun acc e => if e.position = a.val then e.value else acc) ratZero

/-- Loads the last-write resolution of a sparse list when all positions are legal and its mass
is nonzero, recording the list length as its read count. -/
def loadSparse (D : ℕ) (es : List SparseEntry) : Option (LoadedInput D) :=
  if ∀ e ∈ es, e.position < D then
    if (∑ i : Fin D, ratSq (sparseResolve es i)) = 0 then none
    else
      some (LoadedInput.mk (fun a => sparseResolve es a) es.length
        (Finset.univ.filter (fun i : Fin D => sparseResolve es i ≠ ratZero)).card)
  else none

/-- A rational approximation to the input's phase at precision `k`, using signed rational payoff
coordinates and assigning phase `(1, 0)` to zero. -/
def phaseApprox (z : RatComplex) (k : ℕ) : RatComplex :=
  if z = ratZero then (1, 0)
  else
    let r2 := ratSq z
    let cs := rationalPayoffCS (z.1 ^ 2 / r2) k
    (ratSign z.1 * cs.2, ratSign z.2 * cs.1)

/-- The input divided by its real modulus, with phase one assigned to zero. -/
noncomputable def exactPhase (z : RatComplex) : ℂ :=
  if z = ratZero then 1
  else
    let r := Real.sqrt (ratSq z : ℝ)
    Complex.ofReal ((z.1 : ℝ) / r) + Complex.ofReal ((z.2 : ℝ) / r) * Complex.I

/-- The diagonal matrix of the exact phases of the supplied amplitudes. -/
noncomputable def exactPhaseDiagonal {D : ℕ} (amp : Option (Fin D) → RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  Matrix.diagonal (fun a => exactPhase (amp a))

/-- The diagonal matrix of rational phase approximations at precision `k`, embedded into `ℂ`. -/
noncomputable def phaseDiagonal {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  Matrix.diagonal (fun a => ratToComplex (phaseApprox (amp a) k))

/-- The diagonal matrix that multiplies label `a` by the complex value of `u` and leaves every
other label unchanged. -/
noncomputable def phaseLabelGate {D : ℕ} (a : Option (Fin D)) (u : RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  fun b c => if b = c then (if c = a then ratToComplex u else 1) else 0

/-- The list containing `none` followed by all `some` labels in increasing finite-index order. -/
def labelList (D : ℕ) : List (Option (Fin D)) :=
  none :: (List.finRange D).map (fun i => some i)

/-- The pointwise product of approximate phase factors associated with a list of labels. -/
def phaseFactors {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    List (Option (Fin D)) → (Option (Fin D) → ℂ)
  | [] => fun _ => 1
  | a :: as => fun b =>
      (if b = a then ratToComplex (phaseApprox (amp a) k) else 1) * phaseFactors k amp as b

/-- The declared phase-label count for a table of size `D`. -/
def phaseLabelCount (D : ℕ) : ℕ := D

/-- The per-label phase comparison charge of `2 * k`. -/
def phaseLabelComparisons (k : ℕ) : ℕ := 2 * k

/-- The phase comparison charge of `2 * D * k` for `D` entries. -/
def phaseComparisons (D k : ℕ) : ℕ := 2 * D * k

/-- The one-gate adjoint word consisting of the approximate phase diagonal. -/
noncomputable def phaseWord {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    List (AdjointStep (Option (Fin D))) :=
  [.gate (phaseDiagonal k amp)]

/-- The adjoint preparation word formed from the phase word and the rational weight preparation
word. -/
noncomputable def prepareWord {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : List (AdjointStep (Option (Fin D))) :=
  phaseWord k amp ++ rationalWeightWord w k

/-- The preparation matrix obtained by multiplying the approximate phase diagonal by the
rational weight preparation matrix. -/
noncomputable def prepareMatrix {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  phaseDiagonal k amp * rationalWeightPrepare w k

/-- The ideal preparation matrix obtained by multiplying the exact phase diagonal by the ideal
weight preparation matrix. -/
noncomputable def exactPrepareMatrix {D : ℕ} (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  exactPhaseDiagonal amp * idealWeightPrepare w

/-- The loaded amplitudes divided by the square root of their mass, with zero amplitude at the
additional `none` slot. -/
noncomputable def loadedTarget {D : ℕ} (L : LoadedInput D) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ratToComplex (L.amplitude i) / Real.sqrt (L.mass : ℝ)

/-- Builds a Boolean table from legal positions using last-write semantics and default false
values; rejects any out-of-range position. -/
def buildBoolTable (D : ℕ) (es : List (ℕ × Bool)) : Option (Fin D → Bool) :=
  if ∀ p ∈ es, p.1 < D then
    some (fun a => es.foldl (fun acc e => if e.1 = a.val then e.2 else acc) false)
  else none

/-- The number of Boolean list entries charged as reads. -/
def buildBoolTableReads (es : List (ℕ × Bool)) : ℕ := es.length

/-- The Boolean table value at the requested finite address. -/
def boolTableRead {D : ℕ} (T : Fin D → Bool) (a : Fin D) : Bool := T a

/-- The address width `Nat.log2 D + 1` assigned to a table of size `D`. -/
def addressBitsFor (D : ℕ) : ℕ := Nat.log2 D + 1

/-- The assigned address width has strictly more than `D` basis states. -/
theorem addressBitsFor_sufficient (D : ℕ) : D < 2 ^ addressBitsFor D := by
  by_cases hD : D = 0
  · subst hD
    simp [addressBitsFor]
  · have hlt : Nat.log2 D < Nat.log2 D + 1 := by omega
    have h := (Nat.log2_lt hD).mp hlt
    simpa [addressBitsFor] using h

/-- Declared access data recording whether a distance is known, a distance bound, and a rational
normalization budget. -/
structure AccessPreconditions where

  distanceKnown : Bool

  distanceBound : ℕ

  normalizationBudget : ℚ
  deriving DecidableEq, Repr

/-- The access precondition record with unknown distance, zero bound, and zero normalization
budget. -/
def freePreconditions : AccessPreconditions :=
  { distanceKnown := false, distanceBound := 0, normalizationBudget := 0 }

/-- The condition that distance knowledge is declared and the normalization budget is positive. -/
def AccessPreconditions.satisfiedBy (p : AccessPreconditions) : Prop :=
  p.distanceKnown = true ∧ 0 < p.normalizationBudget

/-- An equivalence between `2 ^ w` finite indices and option slots, assigning the last index to
`none`. -/
def finSlotEquiv (w : ℕ) : Fin (2 ^ w) ≃ Option (Fin (2 ^ w - 1)) where
  toFun j := if h : j.val < 2 ^ w - 1 then some ⟨j.val, h⟩ else none
  invFun a := match a with
    | none => ⟨2 ^ w - 1, by
        have h2 : (0 : ℕ) < 2 := by norm_num
        have hp : (0 : ℕ) < 2 ^ w := pow_pos h2 w
        omega⟩
    | some j => ⟨j.val, by
        have hj := j.isLt
        have h2 : (0 : ℕ) < 2 := by norm_num
        have hp : (0 : ℕ) < 2 ^ w := pow_pos h2 w
        omega⟩
  left_inv j := by
    by_cases h : j.val < 2 ^ w - 1
    · simp [h]
    · have hj : j.val = 2 ^ w - 1 := by
        have := j.isLt
        omega
      apply Fin.ext
      simp [h, hj]
  right_inv a := by
    cases a with
    | none => simp
    | some j => simp

/-- The equivalence from a `w`-bit register to option slots obtained from its finite-index
representation. -/
def slotEquiv (w : ℕ) : Reg w ≃ Option (Fin (2 ^ w - 1)) :=
  (bitVecEquiv w).trans (finSlotEquiv w)

/-- The register basis label corresponding to the additional `none` slot. -/
def pivotSlot (w : ℕ) : Reg w := (slotEquiv w).symm none

/-- Dense-table amplitudes placed in the available option slots, with zero at `none` and at
indices outside the table. -/
def slotAmpW (D w : ℕ) (xs : DenseTable D) : Option (Fin (2 ^ w - 1)) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some j => if hj : j.val < D then xs ⟨j.val, hj⟩ else ratZero

/-- The squared modulus of each option-slot amplitude. -/
def slotWeight (D w : ℕ) (xs : DenseTable D) : Option (Fin (2 ^ w - 1)) → ℚ :=
  fun a => ratSq (slotAmpW D w xs a)

/-- The dense-table amplitude at an available nonpivot slot, or zero when its index is outside
the table. -/
def physSlotAmp (D w : ℕ) (xs : DenseTable D) : Fin (2 ^ w - 1) → RatComplex :=
  fun j => if hj : j.val < D then xs ⟨j.val, hj⟩ else ratZero

/-- The option-slot amplitudes transported to the physical register. -/
def physAmp (D w : ℕ) (xs : DenseTable D) : Reg w → RatComplex :=
  fun x => slotAmpW D w xs (slotEquiv w x)

/-- The rational squared modulus of each physical-register amplitude. -/
def physWeight (D w : ℕ) (xs : DenseTable D) : Reg w → ℚ :=
  fun x => ratSq (physAmp D w xs x)

/-- The sum of all option-slot weights. -/
def slotMass (D w : ℕ) (xs : DenseTable D) : ℚ :=
  ∑ a : Option (Fin (2 ^ w - 1)), slotWeight D w xs a

/-- The physical-register diagonal of rational phase approximations at precision `k`. -/
noncomputable def physPhaseDiagonal (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal (fun x => ratToComplex (phaseApprox (physAmp D w xs x) k))

/-- The rational weight preparation matrix transported from option slots to the physical
register. -/
noncomputable def physMag (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  relabelGate (slotEquiv w).symm (rationalWeightPrepare (slotWeight D w xs) k)

/-- The physical preparation matrix combining magnitude preparation with the approximate phase
diagonal. -/
noncomputable def physPrepare (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  physPhaseDiagonal D w xs k * physMag D w xs k

/-- The nonpivot physical-slot amplitudes packaged with `D` recorded reads and the original
dense table's nonzero support count. -/
def physLoaded (D w : ℕ) (xs : DenseTable D) : LoadedInput (2 ^ w - 1) where
  amplitude := physSlotAmp D w xs
  reads := D
  support := (Finset.univ.filter (fun i : Fin D => xs i ≠ ratZero)).card

/-- The physical-register amplitudes divided by the square root of the slot mass. -/
noncomputable def physTarget (D w : ℕ) (xs : DenseTable D) : QState (Reg w) :=
  fun x => ratToComplex (physAmp D w xs x) / Real.sqrt (slotMass D w xs : ℝ)

/-- A Boolean-table access contract recording table knowledge, preconditions, paid entries, and
the per-access charge. -/
structure AccessContract (D : ℕ) where

  knownTable : Bool

  preconditions : AccessPreconditions

  table : Fin D → Bool

  paidEntries : ℕ

  perAccess : ℕ
  deriving DecidableEq, Repr

/-- An access contract for a known constructed table, with the supplied paid-entry count and
unit per-access charge. -/
def constructedContract (D : ℕ) (T : Fin D → Bool) (paid : ℕ) : AccessContract D where
  knownTable := true
  preconditions := { distanceKnown := false, distanceBound := 0, normalizationBudget := 0 }
  table := T
  paidEntries := paid
  perAccess := 1

/-- An access contract for a granted table with explicit preconditions, the supplied paid-entry
count, and unit per-access charge. -/
def grantedContract (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions) (paid : ℕ) :
    AccessContract D where
  knownTable := false
  preconditions := p
  table := T
  paidEntries := paid
  perAccess := 1

/-- The requirement that the table is declared known or its access preconditions hold. -/
def AccessContract.preconditionObligation {D : ℕ} (c : AccessContract D) : Prop :=
  c.knownTable = true ∨ c.preconditions.satisfiedBy

/-- The paid-entry charge plus the number of accesses times the address-width and per-access
charges. -/
def AccessContract.totalCharge {D : ℕ} (c : AccessContract D) (accesses : ℕ) : ℕ :=
  c.paidEntries + accesses * (addressBitsFor D + c.perAccess)

/-- The address-width charge plus the contract's per-access charge. -/
def AccessContract.accessCharge {D : ℕ} (c : AccessContract D) : ℕ :=
  addressBitsFor D + c.perAccess

/-- The natural ceiling of `64 * (D + 1) / ε`, used as a preparation precision parameter. -/
def precisionFor (D : ℕ) (ε : ℚ) : ℕ := Nat.ceil (64 * (D + 1) / ε)

/-- Bit-width parameters for amplitudes and addresses. -/
structure InputBits where

  amplitudeBits : ℕ

  addressBits : ℕ
  deriving DecidableEq, Repr

/-- Recorded entry, bit-width, comparison, gate, query, and peak quantum and classical workspace
counts. -/
structure ResourceAccount where

  entries : ℕ

  bits : InputBits

  comparisons : ℕ

  gates : ℕ

  queries : ℕ

  peakQubits : ℕ

  peakCells : ℕ
  deriving DecidableEq, Repr

/-- The comparison charge weighted by amplitude width plus one, together with the query charge
weighted by address width. -/
def ResourceAccount.bitTime (a : ResourceAccount) : ℕ :=
  a.comparisons * (a.bits.amplitudeBits + 1) + a.queries * a.bits.addressBits

/-- The declared resource account for physical preparation, with its comparison and
reflection-gate bounds, zero queries, and specified peak workspace. -/
def physAccount (D w : ℕ) (k b : ℕ) : ResourceAccount where
  entries := D
  bits := { amplitudeBits := b, addressBits := addressBitsFor D }
  comparisons := 2 * (2 ^ w - 1) * k + phaseComparisons D k
  gates := 128 * (w + 1) ^ 2 * 4 ^ w
  queries := 0
  peakQubits := w + (w + 1)
  peakCells := D

/-- A record of loading, preparation, comparison, access, addressing, and peak-space charges. -/
structure AccessCost where

  loadReads : ℕ

  prepareGates : ℕ

  comparisons : ℕ

  accesses : ℕ

  addressBits : ℕ

  perAccessCharge : ℕ

  peakSpace : ℕ

/-- The number of accesses multiplied by the sum of address width and per-access charge. -/
def AccessCost.accessCharge (c : AccessCost) : ℕ :=
  c.accesses * (c.addressBits + c.perAccessCharge)

/-- The sum of loading reads, preparation gates, comparisons, and the access charge. -/
def AccessCost.totalCharge (c : AccessCost) : ℕ :=
  c.loadReads + c.prepareGates + c.comparisons + c.accessCharge

end Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
