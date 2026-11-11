/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Rational
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! A fully rational traced dyadic-phase initializer.
Machin series, explicit rational powers, Cayley initialization, and every
Gaussian square produce their operand trace together with the returned value.
The interpretation proofs identify these data with the exact pinned backend;
no exact-complex primitive or free numerical phase is substituted.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LocalMachine.LocalTransport

/-- Construction for nat Add in the backend model. -/
def natAdd (a b : ℕ) : Run ℕ := emit (.natural .add a b) (a+b)
/-- Construction for nat Mul in the backend model. -/
def natMul (a b : ℕ) : Run ℕ := emit (.natural .mul a b) (a*b)

/-- A traced natural addition returns its actual result. -/
@[simp] theorem natAdd_value (a b : ℕ) : (natAdd a b).value = a+b := by
  simp [natAdd]
/-- A traced natural multiplication returns its actual result. -/
@[simp] theorem natMul_value (a b : ℕ) : (natMul a b).value = a*b := by
  simp [natMul]

/-- Construction for nat Power in the backend model. -/
def natPower (a : ℕ) : ℕ → Run ℕ
  | 0 => pure 1
  | n+1 => do
    let p ← natPower a n
    natMul p a

/-- Traced natural power performs its complete multiplication recurrence. -/
@[simp] theorem natPower_value (a n : ℕ) : (natPower a n).value = a^n := by
  induction n with
  | zero => simp [natPower]
  | succ n ih => simp [natPower, ih, pow_succ]

/-- Construction for atan Series in the backend model. -/
def atanSeries (x : ℚ) : ℕ → Run ℚ
  | 0 => pure 0
  | n+1 => do
    let previous ← atanSeries x n
    let sign ← power (-1) n
    let twice ← natMul 2 n
    let degree ← natAdd twice 1
    let numerator ← power x degree
    let signed ← mul sign numerator
    let denominator ← cast degree
    let term ← div signed denominator
    add previous term

/-- The traced finite alternating series preserves the actual rational backend. -/
@[simp] theorem atanSeries_value (x : ℚ) (n : ℕ) :
    (atanSeries x n).value = atanRatSeries x n := by
  induction n with
  | zero => simp [atanSeries, atanRatSeries]
  | succ n ih => simp [atanSeries, atanRatSeries, ih]

/-- Construction for machin Preparation in the backend model. -/
def machinPreparation (k : ℕ) : Run (ℚ × ℚ × ℕ) := do
  let n ← natAdd k 3
  let x ← div 1 5
  let y ← div 1 239
  pure (x,y,n)

/-- The traced preparation keeps both exact rational constants and the series length. -/
@[simp] theorem machinPreparation_value (k : ℕ) :
    (machinPreparation k).value = ((1/5 : ℚ),(1/239 : ℚ),k+3) := by
  simp [machinPreparation]

/-- Construction for machin Combination in the backend model. -/
def machinCombination (a b : ℚ) : Run ℚ := do
  let a' ← mul 16 a
  let b' ← mul 4 b
  sub a' b'

/-- The traced Machin combination preserves its exact rational arithmetic. -/
@[simp] theorem machinCombination_value (a b : ℚ) :
    (machinCombination a b).value = 16*a-4*b := by
  simp [machinCombination]

/-- Construction for machin Series in the backend model. -/
def machinSeries (x y : ℚ) (n : ℕ) : Run ℚ :=
  let a := atanSeries x n
  let b := atanSeries y n
  let combined := machinCombination a.value b.value
  ⟨combined.value,a.events ++ b.events ++ combined.events⟩

/-- The two traced series have the exact original Machin combination for arbitrary inputs. -/
@[simp] theorem machinSeries_value (x y : ℚ) (n : ℕ) :
    (machinSeries x y n).value = 16*atanRatSeries x n-4*atanRatSeries y n := by
  simp only [machinSeries, value_mk, atanSeries_value, machinCombination_value]

attribute [irreducible] atanSeries machinSeries

/-- Construction for machin Pi in the backend model. -/
def machinPi (k : ℕ) : Run ℚ :=
  let input := machinPreparation k
  let result := machinSeries input.value.1 input.value.2.1 input.value.2.2
  ⟨result.value,input.events ++ result.events⟩

/-- The traced initializer computes the original Machin rational approximation. -/
@[simp] theorem machinPi_value (k : ℕ) : (machinPi k).value = piRatApprox k := by
  simp only [machinPi, value_mk, machinPreparation_value, machinSeries_value, piRatApprox]

/-- Construction for phase Angle in the backend model. -/
def phaseAngle (j : ℕ) (negative : Bool) (k : ℕ) : Run ℚ :=
  let precision := natAdd k 4
  let pi := machinPi precision.value
  let twice := mul 2 pi.value
  let signed := mul (if negative then -1 else 1) twice.value
  let power := natPower 2 j
  let denominator := cast power.value
  let result := div signed.value denominator.value
  ⟨result.value,precision.events ++ pi.events ++ twice.events ++ signed.events ++
    power.events ++ denominator.events ++ result.events⟩

/-- The traced phase angle retains the original sign, precision and denominator. -/
@[simp] theorem phaseAngle_value (j : ℕ) (negative : Bool) (k : ℕ) :
    (phaseAngle j negative k).value = numericalPhaseRat j negative k := by
  simp [phaseAngle, numericalPhaseRat]

/-- Construction for cayley Init in the backend model. -/
def cayleyInit (x : ℚ) (k : ℕ) : Run GaussianRat := do
  let power ← natPower 2 k
  let rationalPower ← cast power
  let twicePower ← mul 2 rationalPower
  let t ← div x twicePower
  let square ← mul t t
  let denominator ← add 1 square
  let numerator ← sub 1 square
  let realPart ← div numerator denominator
  let twiceT ← mul 2 t
  let imagPart ← div twiceT denominator
  pure (realPart,imagPart)

/-- The traced Cayley initialization includes the original finite-power computation. -/
@[simp] theorem cayleyInit_value (x : ℚ) (k : ℕ) :
    (cayleyInit x k).value = (countedCayleyInit x k).1 := by
  simp [cayleyInit, countedCayleyInit, countedCayleyPowerTwo_value_and_cost]

/-- Construction for gaussian Square in the backend model. -/
def gaussianSquare (z : GaussianRat) : Run GaussianRat := do
  let aa ← mul z.1 z.1
  let bb ← mul z.2 z.2
  let ab ← mul z.1 z.2
  let ab' ← mul z.1 z.2
  let realPart ← sub aa bb
  let imagPart ← add ab ab'
  pure (realPart,imagPart)

/-- A traced Gaussian square retains all four actual rational multiplications. -/
@[simp] theorem gaussianSquare_value (z : GaussianRat) :
    (gaussianSquare z).value = squareGaussianRat z := by
  simp [gaussianSquare, squareGaussianRat]

/-- Construction for squares in the backend model. -/
def squares (z : GaussianRat) : ℕ → Run GaussianRat
  | 0 => pure z
  | n+1 => do
    let previous ← squares z n
    gaussianSquare previous

/-- Traced repeated squaring gives the original finite-loop value. -/
@[simp] theorem squares_value (z : GaussianRat) (n : ℕ) :
    (squares z n).value = (squareLoop z n).1 := by
  induction n with
  | zero => simp [squares, squareLoop]
  | succ n ih => simp [squares, squareLoop, ih]

/-- Construction for dyadic Phase in the backend model. -/
def dyadicPhase (j : ℕ) (negative : Bool) (k : ℕ) : Run GaussianRat :=
  let angle := phaseAngle j negative k
  let reduced := div angle.value 8
  let precision := natAdd k 4
  let initial := cayleyInit reduced.value precision.value
  let first := squares initial.value precision.value
  let result := squares first.value 3
  ⟨result.value,angle.events ++ reduced.events ++ precision.events ++ initial.events ++
    first.events ++ result.events⟩

/-- The complete traced rational backend returns the exact pinned dyadic phase. -/
@[simp] theorem dyadicPhase_value (j : ℕ) (negative : Bool) (k : ℕ) :
    (dyadicPhase j negative k).value = numericalDyadicPhase j negative k := by
  simp [dyadicPhase, numericalDyadicPhase, countedCayleyPhase]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
