/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
import Qatlib.Concepts.TableAccess.LookupCompile.FiniteTableAccess
import Qatlib.Concepts.BlockEncoding.Postselection

/-!
# Certified amplitude tables and access accounting

`ComputableComplex` and `CertifiedTable` record rational complex approximations with certified
errors that halve at each refinement step. This module defines their masses, rescaled target
vectors, and finite rational snapshots for use in state-loading constructions. State preparation
and finite quantum registers provide the background in [NielsenChuang2010].

The module also defines bounded-row lookup expressions, address loading, and `QramContract` for
initial and per-access charges. `remSeq`, `gcdRun`, and `EffectiveAccessConventions` supply
arithmetic and resource-accounting data used by effective-access constructions.

## Main definitions

* `ComputableComplex` and `CertifiedTable`: certified rational approximations of complex
  amplitudes.
* `certTarget` and `certSnapshotState`: target and snapshot vectors rescaled by the square root
  of their mass.
* `checkedLookupExpr`: an enabled lookup expression using the specified number of rows.
* `QramContract.totalCharge`: the initial charge plus the charge for a given number of accesses.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

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

/-- A complex value equipped with rational complex approximations, certified nonnegative error
bounds halving at each step, and fixed bounds on the real numerator and imaginary
denominator. -/
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

/-- A finite table of certified complex values with a shared halving error bound and shared
bounds on the real numerators and imaginary denominators of all approximations. -/
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

/-- The total squared magnitude of the exact complex entries of a certified table. -/
def certMass {D : ℕ} (T : CertifiedTable D) : ℝ :=
  ∑ i : Fin D, (((T.entry i).value.re) ^ 2 + ((T.entry i).value.im) ^ 2)

/-- The real cast of the rational squared magnitude equals the squared norm of the corresponding
complex number. -/
theorem ratSq_real (z : RatComplex) : ((ratSq z : ℚ) : ℝ) = ‖ratToComplex z‖ ^ 2 := by
  have hre : (ratToComplex z).re = (z.1 : ℝ) := by simp [ratToComplex]
  have him : (ratToComplex z).im = (z.2 : ℝ) := by simp [ratToComplex]
  rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
  simp only [ratSq]
  push_cast
  ring

/-- The real part of a rational complex pair is the real cast of its first component. -/
theorem ratToComplex_re (z : RatComplex) : (ratToComplex z).re = (z.1 : ℝ) := by
  simp [ratToComplex]

/-- The imaginary part of a rational complex pair is the real cast of its second component. -/
theorem ratToComplex_im (z : RatComplex) : (ratToComplex z).im = (z.2 : ℝ) := by
  simp [ratToComplex]

/-- The vector of exact table entries divided by the square root of `certMass`, extended by zero
at the extra `none` index. -/
noncomputable def certTarget {D : ℕ} (T : CertifiedTable D) : QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => (T.entry i).value / Real.sqrt (certMass T)

/-- The rational amplitude table obtained at approximation level `k`. -/
def certSnapshotAmp {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Fin D → RatComplex :=
  fun i => (T.entry i).approx k

/-- The rational squared magnitudes of the level-`k` snapshot amplitudes, extended by zero at
`none`. -/
def certSnapshotWeights {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Option (Fin D) → ℚ :=
  fun a => match a with
    | none => 0
    | some i => ratSq (certSnapshotAmp T k i)

/-- The level-`k` rational amplitude snapshot extended to an optional index by assigning the
zero amplitude to `none`. -/
def certSnapshotAmpOpt {D : ℕ} (T : CertifiedTable D) (k : ℕ) : Option (Fin D) → RatComplex :=
  fun a => match a with
    | none => ratZero
    | some i => (T.entry i).approx k

/-- The sum of the rational squared magnitudes of all level-`k` snapshot amplitudes. -/
def certSnapshotMass {D : ℕ} (T : CertifiedTable D) (k : ℕ) : ℚ :=
  ∑ i : Fin D, ratSq (certSnapshotAmp T k i)

/-- The level-`k` amplitude snapshot packaged as a loaded input with both read and support
counts set to the table size. -/
def certSnapshotLoaded {D : ℕ} (T : CertifiedTable D) (k : ℕ) : LoadedInput D where
  amplitude := certSnapshotAmp T k
  reads := D
  support := D

/-- The complex snapshot amplitudes divided by the square root of their total rational mass,
with zero amplitude at `none`. -/
noncomputable def certSnapshotState {D : ℕ} (T : CertifiedTable D) (k : ℕ) :
    QState (Option (Fin D)) :=
  fun a => match a with
    | none => 0
    | some i => ratToComplex (certSnapshotAmp T k i) / Real.sqrt (certSnapshotMass T k : ℝ)

/-- The Boolean expression that XORs the enabled address-matching table bits for output bit `j`
over the first `D` rows. -/
def checkedLookupExpr (a b D : ℕ) (hD : D ≤ 2 ^ a) (j : Fin b) : Expr (inputs a b) :=
  ((List.finRange D).map (Fin.castLE hD)).foldr (fun r z =>
    .xor (.conj (.var (enableWire a b))
      (.conj (matchExpr a b r) (.var (tableWire a b r j)))) z)
    (.constant false)

/-- The condition that every address wire contains the corresponding binary digit of index `i`. -/
def loadedIndexBits {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b)) : Prop :=
  ∀ j : Fin a, x (addressWire a b j) = i.val.testBit j.val

/-- The register obtained by writing the binary digits of index `i` into the first `a` wires and
preserving all remaining wires. -/
def loadIndex {D : ℕ} (a b : ℕ) (i : Fin D) (x : Reg (inputs a b)) : Reg (inputs a b) :=
  fun w => if w.val < a then i.val.testBit w.val else x w

/-- A finite access contract recording row capacity, address width, access preconditions, and
initial and per-access charges, with the initial paid-entry count equal to the row count. -/
structure QramContract (D : ℕ) where

  rows : ℕ

  addressWidth : ℕ

  rows_le : rows ≤ 2 ^ addressWidth

  preconditions : AccessPreconditions

  paidEntries : ℕ

  perAccess : ℕ

  paid_reads_rows : paidEntries = rows

/-- The initial paid-entry charge plus `n` times the per-access charge. -/
def QramContract.totalCharge {D : ℕ} (c : QramContract D) (n : ℕ) : ℕ :=
  c.paidEntries + n * c.perAccess

/-- The Euclidean remainder sequence starting at `a` and `b`, remaining zero after a zero
remainder is reached. -/
def remSeq : ℕ → ℕ → ℕ → ℕ
  | 0, a, b => a
  | 1, a, b => b
  | n + 2, a, b => if remSeq (n + 1) a b = 0 then 0
    else remSeq n a b % remSeq (n + 1) a b

/-- The arithmetic step budget `2 * (Nat.log2 a + 2)` for input `a`. -/
def gcdStepBound (a : ℕ) : ℕ := 2 * (Nat.log2 a + 2)

/-- The Euclidean algorithm run for at most the given fuel, returning the final pair and
stopping early when the second component is zero. -/
def gcdRun : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, a, b => (a, b)
  | fuel + 1, a, b => if b = 0 then (a, 0) else gcdRun fuel b (a % b)

/-- Resource-accounting parameters for amplitude precision, phase comparisons, comparison
precision, Euclidean steps, and native oracle calls, with the last count defaulting to zero. -/
structure EffectiveAccessConventions where

  amplitudeBits : ℕ

  phaseComparisons : ℕ

  comparisonBits : ℕ

  gcdSteps : ℕ

  nativeOracleCalls : ℕ := 0

end Qatlib.Concepts.MbqcFlow.FlowDecision
