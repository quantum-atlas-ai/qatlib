/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
import Qatlib.Concepts.TableAccess.LookupCompile.FiniteTableAccess
import Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.TableAccess.LookupCompile
open Qatlib
open scoped Classical BigOperators Matrix.Norms.L2Operator

set_option autoImplicit false

structure ComputableComplex where

  approx : ℕ → RatComplex

  value : ℂ

  err : ℕ → ℚ

  err_nonneg : ∀ k, 0 ≤ err k

  certified : ∀ k, ‖ratToComplex (approx k) - value‖ ≤ (err k : ℝ)

  halving : ∀ k, (err (k + 1) : ℝ) ≤ (err k : ℝ) / 2

  width : ℕ

  bounded : ∀ k,
    (approx k).1.num.natAbs < 2 ^ width ∧ (approx k).2.den < 2 ^ width

structure CertifiedTable (D : ℕ) where

  entry : Fin D → ComputableComplex

  err : ℕ → ℚ

  err_nonneg : ∀ k, 0 ≤ err k

  certified : ∀ k i, ‖ratToComplex ((entry i).approx k) - (entry i).value‖ ≤ (err k : ℝ)

  halving : ∀ k, (err (k + 1) : ℝ) ≤ (err k : ℝ) / 2

  width : ℕ

  bounded : ∀ k i,
    ((entry i).approx k).1.num.natAbs < 2 ^ width ∧
      ((entry i).approx k).2.den < 2 ^ width

def certMass {D : ℕ} (T : CertifiedTable D) : ℝ :=
  ∑ i : Fin D, (((T.entry i).value.re) ^ 2 + ((T.entry i).value.im) ^ 2)

theorem ratSq_real (z : RatComplex) : ((ratSq z : ℚ) : ℝ) = ‖ratToComplex z‖ ^ 2 := by
  have hre : (ratToComplex z).re = (z.1 : ℝ) := by simp [ratToComplex]
  have him : (ratToComplex z).im = (z.2 : ℝ) := by simp [ratToComplex]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  simp only [ratSq]
  push_cast
  ring

theorem ratToComplex_re (z : RatComplex) : (ratToComplex z).re = (z.1 : ℝ) := by
  simp [ratToComplex]

theorem ratToComplex_im (z : RatComplex) : (ratToComplex z).im = (z.2 : ℝ) := by
  simp [ratToComplex]

noncomputable def certTarget {D : ℕ} (T : CertifiedTable D) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => (T.entry i).value / Real.sqrt (certMass T)

def certSnapshotAmp {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Fin D → RatComplex :=
  fun i => (T.entry i).approx k

def certSnapshotWeights {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Option (Fin D) → ℚ :=
  fun a => match a with
    | none => 0
    | some i => ratSq (certSnapshotAmp T k i)

def certSnapshotAmpOpt {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Option (Fin D) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some i => (T.entry i).approx k

def certSnapshotMass {D : ℕ} (T : CertifiedTable D) (k : ℕ) : ℚ :=
  ∑ i : Fin D, ratSq (certSnapshotAmp T k i)

def certSnapshotLoaded {D : ℕ} (T : CertifiedTable D) (k : ℕ) : LoadedInput D where
  amplitude := certSnapshotAmp T k
  reads := D
  support := D

noncomputable def certSnapshotState {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ratToComplex (certSnapshotAmp T k i) / Real.sqrt (certSnapshotMass T k : ℝ)

def checkedLookupExpr (a b D : ℕ) (hD : D ≤ 2 ^ a) (j : Fin b) : Expr (inputs a b) :=
  ((List.finRange D).map (Fin.castLE hD)).foldr (fun r z =>
    .xor (.conj (.var (enableWire a b))
      (.conj (matchExpr a b r) (.var (tableWire a b r j)))) z)
    (.constant false)

def loadedIndexBits {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b)) : Prop :=
  ∀ j : Fin a, x (addressWire a b j) = i.val.testBit j.val

def loadIndex {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b)) : Reg (inputs a b) :=
  fun w => if w.val < a then i.val.testBit w.val else x w

structure QramContract (D : ℕ) where

  rows : ℕ

  addressWidth : ℕ

  rows_le : rows ≤ 2 ^ addressWidth

  preconditions : AccessPreconditions

  paidEntries : ℕ

  perAccess : ℕ

  paid_reads_rows : paidEntries = rows

def QramContract.totalCharge {D : ℕ} (c : QramContract D) (n : ℕ) : ℕ :=
  c.paidEntries + n * c.perAccess

def remSeq : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => a
  | 1, a, b => b
  | n + 2, a, b => if remSeq (n + 1) a b = 0 then 0
    else remSeq n a b % remSeq (n + 1) a b

def gcdStepBound (a : ℕ) : ℕ := 2 * (Nat.log2 a + 2)

def gcdRun : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b => (a, b)
  | fuel + 1, a, b => if b = 0 then (a, 0) else gcdRun fuel b (a % b)

structure EffectiveAccessConventions where

  amplitudeBits : ℕ

  phaseComparisons : ℕ

  comparisonBits : ℕ

  gcdSteps : ℕ

  nativeOracleCalls : ℕ := 0

end Qatlib.Concepts.MbqcFlow.FlowDecision
