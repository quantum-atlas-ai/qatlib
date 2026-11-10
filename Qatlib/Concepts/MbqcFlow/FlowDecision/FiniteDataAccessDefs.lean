/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.AEMeanReadout.LayeredMeanLaw.RationalWeightPreparation
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
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

abbrev RatComplex := ℚ × ℚ

def ratZero : RatComplex := (0, 0)

def ratToComplex (z : RatComplex) : ℂ :=
  Complex.ofReal (z.1 : ℝ) + Complex.ofReal (z.2 : ℝ) * Complex.I

def ratSq (z : RatComplex) : ℚ := z.1 ^ 2 + z.2 ^ 2

theorem ratSq_nonneg (z : RatComplex) : 0 ≤ ratSq z := by
  have h1 : 0 ≤ (z.1 : ℚ) ^ 2 := sq_nonneg _
  have h2 : 0 ≤ (z.2 : ℚ) ^ 2 := sq_nonneg _
  exact add_nonneg h1 h2

def ratSign (q : ℚ) : ℚ := if q < 0 then -1 else 1

theorem ratSign_mul_abs (q : ℚ) : ratSign q * |q| = q := by
  by_cases h : q < 0
  · rw [ratSign, if_pos h, abs_of_neg h]; ring
  · rw [ratSign, if_neg h, abs_of_nonneg (le_of_not_gt h)]; ring

abbrev DenseTable (D : ℕ) := Fin D → RatComplex

structure SparseEntry where

  position : ℕ

  value : RatComplex
  deriving DecidableEq, Repr

structure DenseLoader (D : ℕ) where

  reads : Finset (Fin D)

  decode : (Fin D → RatComplex) → Fin D → RatComplex

def DenseLoader.view {D : ℕ} (L : DenseLoader D) (xs : DenseTable D) : Fin D → RatComplex :=
  fun i => if i ∈ L.reads then xs i else ratZero

def DenseLoader.run {D : ℕ} (L : DenseLoader D) (xs : DenseTable D) : Fin D → RatComplex :=
  fun a => L.decode (L.view xs) a

def fullDenseLoader (D : ℕ) : DenseLoader D where
  reads := Finset.univ
  decode := fun v a => v a

theorem fullDenseLoader_run (D : ℕ) (xs : DenseTable D) (a : Fin D) :
    (fullDenseLoader D).run xs a = xs a := by
  simp [DenseLoader.run, fullDenseLoader, DenseLoader.view]

theorem fullDenseLoader_reads (D : ℕ) :
    (fullDenseLoader D).reads.card = D := by
  simp [fullDenseLoader]

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

structure LoadedInput (D : ℕ) where

  amplitude : Fin D → RatComplex

  reads : ℕ

  support : ℕ

def LoadedInput.mass {D : ℕ} (L : LoadedInput D) : ℚ :=
  ∑ i : Fin D, ratSq (L.amplitude i)

def LoadedInput.amp {D : ℕ} (L : LoadedInput D) : Option (Fin D) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some i => L.amplitude i

def LoadedInput.weights {D : ℕ} (L : LoadedInput D) : Option (Fin D) → ℚ :=
  fun a => match a with
    | none => 0
    | some i => ratSq (L.amplitude i)

theorem LoadedInput.mass_eq {D : ℕ} (L : LoadedInput D) :
    rationalWeightMass L.weights = L.mass := by
  unfold rationalWeightMass LoadedInput.weights LoadedInput.mass
  rw [Fintype.sum_option]
  simp

theorem LoadedInput.weights_nonneg {D : ℕ} (L : LoadedInput D) (a : Option (Fin D)) :
    0 ≤ L.weights a := by
  cases a with
  | none => simp [LoadedInput.weights]
  | some i => exact ratSq_nonneg _

def loadDense (D : ℕ) (xs : DenseTable D) : Option (LoadedInput D) :=
  if (∑ i : Fin D, ratSq (xs i)) = 0 then none
  else some (LoadedInput.mk xs D (Finset.univ.filter (fun i => xs i ≠ ratZero)).card)

def sparseResolve {D : ℕ} (es : List SparseEntry) (a : Fin D) : RatComplex :=
  es.foldl (fun acc e => if e.position = a.val then e.value else acc) ratZero

def loadSparse (D : ℕ) (es : List SparseEntry) : Option (LoadedInput D) :=
  if ∀ e ∈ es, e.position < D then
    if (∑ i : Fin D, ratSq (sparseResolve es i)) = 0 then none
    else
      some (LoadedInput.mk (fun a => sparseResolve es a) es.length
        (Finset.univ.filter (fun i : Fin D => sparseResolve es i ≠ ratZero)).card)
  else none

def phaseApprox (z : RatComplex) (k : ℕ) : RatComplex :=
  if z = ratZero then (1, 0)
  else
    let r2 := ratSq z
    let cs := rationalPayoffCS (z.1 ^ 2 / r2) k
    (ratSign z.1 * cs.2, ratSign z.2 * cs.1)

noncomputable def exactPhase (z : RatComplex) : ℂ :=
  if z = ratZero then 1
  else
    let r := Real.sqrt (ratSq z : ℝ)
    Complex.ofReal ((z.1 : ℝ) / r) + Complex.ofReal ((z.2 : ℝ) / r) * Complex.I

noncomputable def exactPhaseDiagonal {D : ℕ} (amp : Option (Fin D) → RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  Matrix.diagonal (fun a => exactPhase (amp a))

noncomputable def phaseDiagonal {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  Matrix.diagonal (fun a => ratToComplex (phaseApprox (amp a) k))

noncomputable def phaseLabelGate {D : ℕ} (a : Option (Fin D)) (u : RatComplex) :
    Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  fun b c => if b = c then (if c = a then ratToComplex u else 1) else 0

def labelList (D : ℕ) : List (Option (Fin D)) :=
  none :: (List.finRange D).map (fun i => some i)

def phaseFactors {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    List (Option (Fin D)) → (Option (Fin D) → ℂ)
  | [] => fun _ => 1
  | a :: as => fun b =>
      (if b = a then ratToComplex (phaseApprox (amp a) k) else 1) * phaseFactors k amp as b

def phaseLabelCount (D : ℕ) : ℕ := D

def phaseLabelComparisons (k : ℕ) : ℕ := 2 * k

def phaseComparisons (D k : ℕ) : ℕ := 2 * D * k

noncomputable def phaseWord {D : ℕ} (k : ℕ) (amp : Option (Fin D) → RatComplex) :
    List (AdjointStep (Option (Fin D))) :=
  [.gate (phaseDiagonal k amp)]

noncomputable def prepareWord {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : List (AdjointStep (Option (Fin D))) :=
  phaseWord k amp ++ rationalWeightWord w k

noncomputable def prepareMatrix {D : ℕ} (k : ℕ) (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  phaseDiagonal k amp * rationalWeightPrepare w k

noncomputable def exactPrepareMatrix {D : ℕ} (w : Option (Fin D) → ℚ)
    (amp : Option (Fin D) → RatComplex) : Matrix (Option (Fin D)) (Option (Fin D)) ℂ :=
  exactPhaseDiagonal amp * idealWeightPrepare w

noncomputable def loadedTarget {D : ℕ} (L : LoadedInput D) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ratToComplex (L.amplitude i) / Real.sqrt (L.mass : ℝ)

def buildBoolTable (D : ℕ) (es : List (ℕ × Bool)) : Option (Fin D → Bool) :=
  if ∀ p ∈ es, p.1 < D then
    some (fun a => es.foldl (fun acc e => if e.1 = a.val then e.2 else acc) false)
  else none

def buildBoolTableReads (es : List (ℕ × Bool)) : ℕ := es.length

def boolTableRead {D : ℕ} (T : Fin D → Bool) (a : Fin D) : Bool := T a

def addressBitsFor (D : ℕ) : ℕ := Nat.log2 D + 1

theorem addressBitsFor_sufficient (D : ℕ) : D < 2 ^ addressBitsFor D := by
  by_cases hD : D = 0
  · subst hD
    simp [addressBitsFor]
  · have hlt : Nat.log2 D < Nat.log2 D + 1 := by omega
    have h := (Nat.log2_lt hD).mp hlt
    simpa [addressBitsFor] using h

structure AccessPreconditions where

  distanceKnown : Bool

  distanceBound : ℕ

  normalizationBudget : ℚ
  deriving DecidableEq, Repr

def freePreconditions : AccessPreconditions :=
  { distanceKnown := false, distanceBound := 0, normalizationBudget := 0 }

def AccessPreconditions.satisfiedBy (p : AccessPreconditions) : Prop :=
  p.distanceKnown = true ∧ 0 < p.normalizationBudget

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

def slotEquiv (w : ℕ) : Reg w ≃ Option (Fin (2 ^ w - 1)) :=
  (bitVecEquiv w).trans (finSlotEquiv w)

def pivotSlot (w : ℕ) : Reg w := (slotEquiv w).symm none

def slotAmpW (D w : ℕ) (xs : DenseTable D) : Option (Fin (2 ^ w - 1)) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some j => if hj : j.val < D then xs ⟨j.val, hj⟩ else ratZero

def slotWeight (D w : ℕ) (xs : DenseTable D) : Option (Fin (2 ^ w - 1)) → ℚ :=
  fun a => ratSq (slotAmpW D w xs a)

def physSlotAmp (D w : ℕ) (xs : DenseTable D) : Fin (2 ^ w - 1) → RatComplex :=
  fun j => if hj : j.val < D then xs ⟨j.val, hj⟩ else ratZero

def physAmp (D w : ℕ) (xs : DenseTable D) : Reg w → RatComplex :=
  fun x => slotAmpW D w xs (slotEquiv w x)

def physWeight (D w : ℕ) (xs : DenseTable D) : Reg w → ℚ :=
  fun x => ratSq (physAmp D w xs x)

def slotMass (D w : ℕ) (xs : DenseTable D) : ℚ :=
  ∑ a : Option (Fin (2 ^ w - 1)), slotWeight D w xs a

noncomputable def physPhaseDiagonal (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal (fun x => ratToComplex (phaseApprox (physAmp D w xs x) k))

noncomputable def physMag (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  relabelGate (slotEquiv w).symm (rationalWeightPrepare (slotWeight D w xs) k)

noncomputable def physPrepare (D w : ℕ) (xs : DenseTable D) (k : ℕ) :
    Matrix (Reg w) (Reg w) ℂ :=
  physPhaseDiagonal D w xs k * physMag D w xs k

def physLoaded (D w : ℕ) (xs : DenseTable D) : LoadedInput (2 ^ w - 1) where
  amplitude := physSlotAmp D w xs
  reads := D
  support := (Finset.univ.filter (fun i : Fin D => xs i ≠ ratZero)).card

noncomputable def physTarget (D w : ℕ) (xs : DenseTable D) : QState (Reg w) :=
  fun x => ratToComplex (physAmp D w xs x) / Real.sqrt (slotMass D w xs : ℝ)

structure AccessContract (D : ℕ) where

  knownTable : Bool

  preconditions : AccessPreconditions

  table : Fin D → Bool

  paidEntries : ℕ

  perAccess : ℕ
  deriving DecidableEq, Repr

def constructedContract (D : ℕ) (T : Fin D → Bool) (paid : ℕ) : AccessContract D where
  knownTable := true
  preconditions := { distanceKnown := false, distanceBound := 0, normalizationBudget := 0 }
  table := T
  paidEntries := paid
  perAccess := 1

def grantedContract (D : ℕ) (T : Fin D → Bool) (p : AccessPreconditions) (paid : ℕ) :
    AccessContract D where
  knownTable := false
  preconditions := p
  table := T
  paidEntries := paid
  perAccess := 1

def AccessContract.preconditionObligation {D : ℕ} (c : AccessContract D) : Prop :=
  c.knownTable = true ∨ c.preconditions.satisfiedBy

def AccessContract.totalCharge {D : ℕ} (c : AccessContract D) (accesses : ℕ) : ℕ :=
  c.paidEntries + accesses * (addressBitsFor D + c.perAccess)

def AccessContract.accessCharge {D : ℕ} (c : AccessContract D) : ℕ :=
  addressBitsFor D + c.perAccess

def precisionFor (D : ℕ) (ε : ℚ) : ℕ := Nat.ceil (64 * (D + 1) / ε)

structure InputBits where

  amplitudeBits : ℕ

  addressBits : ℕ
  deriving DecidableEq, Repr

structure ResourceAccount where

  entries : ℕ

  bits : InputBits

  comparisons : ℕ

  gates : ℕ

  queries : ℕ

  peakQubits : ℕ

  peakCells : ℕ
  deriving DecidableEq, Repr

def ResourceAccount.bitTime (a : ResourceAccount) : ℕ :=
  a.comparisons * (a.bits.amplitudeBits + 1) + a.queries * a.bits.addressBits

def physAccount (D w : ℕ) (k b : ℕ) : ResourceAccount where
  entries := D
  bits := { amplitudeBits := b, addressBits := addressBitsFor D }
  comparisons := 2 * (2 ^ w - 1) * k + phaseComparisons D k
  gates := 128 * (w + 1) ^ 2 * 4 ^ w
  queries := 0
  peakQubits := w + (w + 1)
  peakCells := D

structure AccessCost where

  loadReads : ℕ

  prepareGates : ℕ

  comparisons : ℕ

  accesses : ℕ

  addressBits : ℕ

  perAccessCharge : ℕ

  peakSpace : ℕ

def AccessCost.accessCharge (c : AccessCost) : ℕ :=
  c.accesses * (c.addressBits + c.perAccessCharge)

def AccessCost.totalCharge (c : AccessCost) : ℕ :=
  c.loadReads + c.prepareGates + c.comparisons + c.accessCharge

end Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
