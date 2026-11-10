/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.Instrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription

namespace Qatlib.Concepts.ClusterPatterns.CnotPatterns

open Complex
open scoped Classical BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable def mpSVector (α : ℝ) (o : Bool) : Bool → ℂ :=
  fun b =>
    (if b then if o then -Complex.exp (Complex.ofReal α) else Complex.exp (Complex.ofReal α)
      else 1) / Real.sqrt 2

noncomputable def mpSBasisProjector (α : ℝ) (o : Bool) : Operator 2 :=
  Matrix.of fun i j =>
    mpSVector α o ((i : ℕ) = 1) * star (mpSVector α o ((j : ℕ) = 1))

def mpParity {k : ℕ} (S : Finset (Fin k)) (s : Fin k → Bool) : Bool :=
  decide ((∑ i ∈ S, if s i then 1 else 0 : ℕ) % 2 = 1)

@[simp] theorem mpParity_empty {k : ℕ} (s : Fin k → Bool) : mpParity ∅ s = false := by
  simp [mpParity]

structure MpPattern (n w m : ℕ) where

  entangler : Matrix (Reg (w + m)) (Reg (w + m)) ℂ

  baseAngle : Fin w → ℝ

  angleSign : Fin w → Finset (Fin w)

  angleShift : Fin w → Finset (Fin w)

  xCorr : Fin m → (Fin w → Bool) → Bool

  zCorr : Fin m → (Fin w → Bool) → Bool

  nin : n ≤ w

noncomputable def mpAdaptiveAngle {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool)
    (j : Fin w) : ℝ :=
  (if mpParity (P.angleSign j) s then -P.baseAngle j else P.baseAngle j)
    + Real.pi * (if mpParity (P.angleShift j) s then (1 : ℝ) else 0)

noncomputable def mpLoadMatrix {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) : Matrix (Reg (w + m)) (Reg n) ℂ :=
  Matrix.of fun u y =>
    if ∀ i : Fin n, u (Fin.castLE (by have := P.nin; omega : n ≤ w + m) i) = y i then
      resource (fun k => u (Fin.cast (by have := P.nin; omega) (Fin.natAdd n k)))
    else 0

noncomputable def mpProjector {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) :
    Matrix (Reg (w + m)) (Reg (w + m)) ℂ :=
  Matrix.of fun u u' =>
    (∏ j : Fin w,
        mpSVector (mpAdaptiveAngle P s j) (s j) (u (Fin.castLE (by omega : w ≤ w + m) j))
          * star (mpSVector (mpAdaptiveAngle P s j) (s j)
              (u' (Fin.castLE (by omega) j))))
      * (if ∀ k : Fin m, u (Fin.natAdd w k) = u' (Fin.natAdd w k) then (1 : ℂ) else 0)

def mpCorrection {n w m : ℕ} (P : MpPattern n w m) (s : Fin w → Bool) :
    Matrix (Reg (w + m)) (Reg (w + m)) ℂ :=
  Matrix.of fun u u' =>
    if ∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j)
        = u' (Fin.castLE (by omega) j) then
      if ∀ k : Fin m, u (Fin.natAdd w k) = (xor (P.xCorr k s) (u' (Fin.natAdd w k))) then
        ∏ k : Fin m, if P.zCorr k s && u' (Fin.natAdd w k) then (-1 : ℂ) else 1
      else 0
    else 0

def mpReadout (w m : ℕ) (z : Fin w → Bool) : Matrix (Fin (2 ^ m)) (Reg (w + m)) ℂ :=
  Matrix.of fun xp u =>
    if (∀ j : Fin w, u (Fin.castLE (by omega : w ≤ w + m) j) = z j)
        ∧ bitVecEquiv m (fun k => u (Fin.natAdd w k)) = xp then (1 : ℂ) else 0

noncomputable def mpPatternKraus {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s z : Fin w → Bool) :
    Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) ℂ :=
  Matrix.reindex (Equiv.refl _) (bitVecEquiv n)
    (mpReadout w m z * mpCorrection P s * mpProjector P s * P.entangler * mpLoadMatrix P resource)

noncomputable def mpPatternBranch {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) (s : Fin w → Bool) :
    Operator (2 ^ n) →ₗ[ℂ] Operator (2 ^ m) :=
  ∑ z : Fin w → Bool, conjBranch (mpPatternKraus P resource s z)

noncomputable def mpPatternInstrument {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n)))
    (htotal : ∀ A : Operator (2 ^ n),
      Matrix.trace (∑ s : Fin w → Bool, mpPatternBranch P resource s A) = Matrix.trace A) :
    Instrument (Fin w → Bool) (2 ^ n) (2 ^ m) :=
  Instrument.ofBranches (mpPatternBranch P resource)
    (fun s => CompletelyPositive.sum (s := Finset.univ)
      fun z _ => completelyPositive_conjBranch (mpPatternKraus P resource s z))
    htotal

noncomputable def mpWirePattern : MpPattern 1 2 1 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩)} :
      Finset (Fin 3 × Fin 3))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun _ s => !s 1
  zCorr := fun _ s => !s 0
  nin := by omega

noncomputable def mpCnotPattern : MpPattern 2 4 2 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨2, by omega⟩), (⟨0, by omega⟩, ⟨3, by omega⟩),
      (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨2, by omega⟩, ⟨5, by omega⟩),
      (⟨3, by omega⟩, ⟨4, by omega⟩)} : Finset (Fin 6 × Fin 6))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun k s => if (k : ℕ) = 0 then !s 3 else s 2
  zCorr := fun k s => if (k : ℕ) = 0 then !(xor (s 0) (s 1)) else !s 1
  nin := by omega

def mpEulerSignSet (j : Fin 5) : Finset (Fin 5) :=
  Finset.univ.filter fun i => (i : ℕ) < (j : ℕ) ∧ ((j : ℕ) - (i : ℕ)) % 2 = 1

noncomputable def mpEulerPattern (θ : Fin 5 → ℝ) : MpPattern 1 5 1 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    (Finset.univ.filter fun p : Fin 6 × Fin 6 =>
      ∃ k : ℕ, k + 1 < 6 ∧ (p.1 : ℕ) = k ∧ (p.2 : ℕ) = k + 1)
  baseAngle := fun j => -θ j
  angleSign := fun j => mpEulerSignSet j
  angleShift := fun _ => ∅
  xCorr := fun _ s => xor (xor (s 0) (s 2)) (s 4)
  zCorr := fun _ s => xor (s 1) (s 3)
  nin := by omega

noncomputable def mpTwoOutputPattern : MpPattern 1 2 2 where
  entangler := Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse
    ({(⟨0, by omega⟩, ⟨1, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩),
      (⟨2, by omega⟩, ⟨3, by omega⟩)} : Finset (Fin 4 × Fin 4))
  baseAngle := fun _ => 0
  angleSign := fun _ => ∅
  angleShift := fun _ => ∅
  xCorr := fun k s => if (k : ℕ) = 0 then s 1 else false
  zCorr := fun k s => if (k : ℕ) = 0 then s 0 else s 1
  nin := by omega

noncomputable def mpFinGate (g : FiniteGateCode) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (bitVecEquiv 2) (bitVecEquiv 2) (finiteCodeMatrix 2 g)

noncomputable def mpFin1Gate (g : FiniteGateCode) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.reindex (bitVecEquiv 1) (bitVecEquiv 1) (finiteCodeMatrix 1 g)

noncomputable def mpFinCnot (c t : Fin 2) : Matrix (Fin 4) (Fin 4) ℂ :=
  mpFinGate (FiniteGateCode.cx (c : ℕ) (t : ℕ))

def mpWireSwapMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.reindex (bitVecEquiv 2) (bitVecEquiv 2)
    (permMatrix fun x : Reg 2 => fun i => if (i : ℕ) = 0 then x 1 else x 0)

noncomputable def mpLatticeEdges (a b : ℕ) : Finset (Fin (a * b) × Fin (a * b)) :=
  Finset.univ.filter fun p =>
    ∃ i j : ℕ, i < a ∧ j < b ∧ (p.1 : ℕ) = i * b + j ∧
      (((p.2 : ℕ) = i * b + j + 1 ∧ j + 1 < b) ∨ ((p.2 : ℕ) = (i + 1) * b + j ∧ i + 1 < a))

noncomputable def mpLatticeEntangler (a b : ℕ) : Matrix (Reg (a * b)) (Reg (a * b)) ℂ :=
  Qatlib.Concepts.MbqcFlow.FlowDecision.sourcePulse (mpLatticeEdges a b)

def mpVertexProjector (n : ℕ) (v : Fin n) (b : Bool) : Matrix (Reg n) (Reg n) ℂ :=
  Matrix.diagonal fun x => if x v = b then (1 : ℂ) else 0

def mpEdge01 : Finset (Fin 2 × Fin 2) := {(⟨0, by omega⟩, ⟨1, by omega⟩)}

noncomputable def mpDeletionState (b : Bool) : QState (Reg 2) :=
  fun x => if x 0 = b then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (!b && x 1) / 2 else 0

noncomputable def mpBellVector (f1 f2 : Bool) : QState (Reg 2) :=
  fun x =>
    if x 0 = false then
      (if x 1 = f1 then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (f2 && f1) / Real.sqrt 2 else 0)
    else
      (if x 1 = !f1 then Qatlib.Concepts.MbqcFlow.FlowDecision.bitPhase (f2 && !f1) / Real.sqrt 2 else 0)

def mpLoadPauli (f1 f2 : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    (if f2 then (if i ≠ j then (1 : ℂ) else 0) else (if i = j then (1 : ℂ) else 0))
      * (if (j : ℕ) = 1 ∧ f1 then (-1 : ℂ) else 1)

noncomputable def mpLoadKraus (f1 f2 : Bool) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2) • mpLoadPauli f1 f2

noncomputable def mpSupportSet {w : ℕ} (f : (Fin w → Bool) → Bool) : Finset (Fin w) :=
  Finset.univ.filter fun i =>
    decide (∃ s : Fin w → Bool, f (Function.update s i (!(s i))) ≠ f s)

noncomputable def MpDependency {n w m : ℕ} (P : MpPattern n w m) :
    Finset (Fin (w + m) × Fin (w + m)) :=
  (Finset.univ : Finset (Fin w)).biUnion fun j =>
      ((P.angleSign j ∪ P.angleShift j).image fun i : Fin w =>
        (Fin.castLE (by omega : w ≤ w + m) i, Fin.castLE (by omega) j))
    ∪ (Finset.univ : Finset (Fin m)).biUnion fun k =>
      ((mpSupportSet (P.xCorr k) ∪ mpSupportSet (P.zCorr k)).image fun i : Fin w =>
        (Fin.castLE (by omega) i, Fin.natAdd w k))

def MpFlowCondition {n w m : ℕ} (P : MpPattern n w m) : Prop :=
  ∀ p ∈ MpDependency P, (p.1 : ℕ) < (p.2 : ℕ)

noncomputable def mpBitTime {n w m : ℕ} (P : MpPattern n w m) : ℕ :=
    2 * w + m + (MpDependency P).card

def mpPeakSpace {n w m : ℕ} (P : MpPattern n w m) : ℕ := w + m

noncomputable def mpCommBits {n w m : ℕ} (P : MpPattern n w m) : ℕ := (MpDependency P).card

def MpDeterministic {n w m : ℕ} (P : MpPattern n w m)
    (resource : QState (Reg (w + m - n))) : Prop :=
  (∃ V : Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) ℂ,
      V.conjTranspose * V = 1 ∧
      ∀ (s : Fin w → Bool) (ρ : Operator (2 ^ n)),
        ∑ z : Fin w → Bool,
            (mpPatternKraus P resource s z) * ρ
              * (mpPatternKraus P resource s z).conjTranspose
          = (1 / (2 : ℂ) ^ w) • (V * ρ * V.conjTranspose))
    ∧ ∀ j : Fin w, ∃ p, p ∈ MpDependency P ∧
      (p.1 = Fin.castLE (by omega : w ≤ w + m) j ∨ p.2 = Fin.castLE (by omega) j)

@[simp] theorem mpPeakSpace_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpPeakSpace P = w + m := rfl

@[simp] theorem mpCommBits_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpCommBits P = (MpDependency P).card := rfl

@[simp] theorem mpBitTime_eq {n w m : ℕ} (P : MpPattern n w m) :
    mpBitTime P = 2 * w + m + (MpDependency P).card := rfl

noncomputable def mpRoundedAngle (b : ℕ) (θ : ℝ) : ℝ :=
  2 * Real.pi * ((Int.floor (θ * (2 ^ b) / (2 * Real.pi) + 1 / 2) : ℤ) : ℝ) / (2 ^ b)

end Qatlib.Concepts.ClusterPatterns.CnotPatterns
