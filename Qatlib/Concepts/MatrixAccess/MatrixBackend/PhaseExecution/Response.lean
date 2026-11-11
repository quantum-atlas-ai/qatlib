/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution.Rational

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

/-! A single traced response and coefficient-score interpreter.
All Gaussian arithmetic, zero-extension, finite coefficient visits and newly
constructed list cells are recorded. The returned legacy counters refer to
this same response/score run; they are not independently supplied promises.
Primitive prices remain an explicit arithmetic/access model, not host bit time.
-/
set_option autoImplicit false

namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis

/-- Construction for response in the response model. -/
def response (base : GaussianRat) : List GaussianRat →
    Run ((List GaussianRat × List GaussianRat) × ℕ)
  | [] => do
    let p ← allocate base []
    pure ((p,[]),0)
  | z::tail => do
    let previous ← response base tail
    let pShift ← shiftArray previous.1.1
    let qShift ← shiftArray previous.1.2
    let qShiftTwice ← shiftArray qShift
    let difference ← subArrays previous.1.2 qShiftTwice
    let sum ← addArrays pShift difference
    let p ← scaleArray z sum
    let qDifference ← subArrays previous.1.1 qShift
    let conjugate ← gaussianConj z
    let q ← scaleArray conjugate qDifference
    pure ((p,q),previous.2+1)

/-- The complete traced response returns both original coefficient arrays and rounds. -/
@[simp] theorem response_value (base : GaussianRat) (phases : List GaussianRat) :
    (response base phases).value = responseData base phases := by
  induction phases with
  | nil => simp [response, responseData]
  | cons z phases ih => simp [response, responseData, ih]

/-- Construction for score Coefficients in the response model. -/
def scoreCoefficients (p : List ℚ) (coefficients : List GaussianRat) :
    ℕ → Run (ℚ × ℕ)
  | 0 => pure (0,0)
  | n+1 => do
    let previous ← scoreCoefficients p coefficients n
    let actual ← visit coefficients n gzero
    let target ← visit p n 0
    let difference ← sub actual.1 target
    let error ← abs difference
    let total ← add previous.1 error
    pure (total,previous.2+1)

/-- Traced coefficient scoring keeps the original sum and every coefficient visit. -/
@[simp] theorem scoreCoefficients_value (p : List ℚ) (coefficients : List GaussianRat)
    (n : ℕ) : (scoreCoefficients p coefficients n).value = scoreLoop p coefficients n := by
  induction n with
  | zero => simp [scoreCoefficients, scoreLoop]
  | succ n ih => simp [scoreCoefficients, scoreLoop, ih]

/-- Construction for score in the response model. -/
def score (p : List ℚ) (degree : ℕ) (data : PhaseData) : Run ((ℚ × ℕ) × ℕ) := do
  let actual ← response data.base data.phases
  let value ← scoreCoefficients p actual.1.1 (degree+1)
  pure ((value.1,actual.2),value.2)

/-- The traced score and both counters equal the original exact finite computation. -/
@[simp] theorem score_value (p : List ℚ) (degree : ℕ) (data : PhaseData) :
    (score p degree data).value = scoreData p degree data := by
  simp [score, scoreData]

end Qatlib.Concepts.MatrixAccess.MatrixBackend.PhaseExecution
