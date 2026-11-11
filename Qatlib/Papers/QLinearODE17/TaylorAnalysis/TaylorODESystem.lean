/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge

/-!
# Taylor linear systems for differential equations

This module defines the Taylor history matrices `taylorStepMatrix` and `taylorStepMatrixV2`,
together with the initial and forcing data `taylorRHS`. Time and terminal labels identify the
blocks used to compare a linear-system solution with `taylorODESolution`.

The terminal success set, coherent extraction, and measured density provide distinct ways to
recover the final state from the history register. See [BerryEtAl2017ODE] for the paper's
setting.

## Main statements

* `taylorStepMatrix`: The Taylor history matrix with step, block-sum, and terminal-copy
  contributions in its defining conditional expression.
* `taylorMeasuredDensityV2`: The sum of the outer products of the terminal blocks of `φ`,
  representing the unnormalized density after selecting those labels and discarding the label
  register.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.LchsSimulation.TimeOrdered

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QLinearODE17.TaylorAnalysis

open Matrix

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The Taylor history matrix with step, block-sum, and terminal-copy contributions in its
defining conditional expression. -/
def taylorStepMatrix (m k p : ℕ) (M : Matrix N N ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1) × N) (Fin (m * (k + 1) + p + 1) × N) ℂ :=
  fun r c =>
    (if r = c then (1 : ℂ) else 0)
      - if (r.1 : ℕ) < m * (k + 1) ∧ 1 ≤ (r.1 : ℕ) % (k + 1) ∧ c.1.val + 1 = r.1.val then
          M r.2 c.2 / ((r.1 : ℕ) % (k + 1) : ℕ) else 0
      - if (r.1 : ℕ) ≤ m * (k + 1) ∧ 0 < (r.1 : ℕ) ∧ (k + 1 : ℕ) ∣ (r.1 : ℕ) ∧
          r.1.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.1.val then
          (if r.2 = c.2 then (1 : ℂ) else 0) else 0
      - if m * (k + 1) < (r.1 : ℕ) ∧ c.1.val + 1 = r.1.val then
          (if r.2 = c.2 then (1 : ℂ) else 0) else 0

/-- The Taylor history matrix obtained by subtracting the step, block-sum, and terminal-copy
contributions separately from the identity. -/
def taylorStepMatrixV2 (m k p : ℕ) (M : Matrix N N ℂ) :
    Matrix (Fin (m * (k + 1) + p + 1) × N) (Fin (m * (k + 1) + p + 1) × N) ℂ :=
  fun r c =>
    (if r = c then (1 : ℂ) else 0)
      - (if (r.1 : ℕ) < m * (k + 1) ∧ 1 ≤ (r.1 : ℕ) % (k + 1) ∧ c.1.val + 1 = r.1.val then
          M r.2 c.2 / ((r.1 : ℕ) % (k + 1) : ℕ) else 0)
      - (if (r.1 : ℕ) ≤ m * (k + 1) ∧ 0 < (r.1 : ℕ) ∧ (k + 1 : ℕ) ∣ (r.1 : ℕ) ∧
          r.1.val - (k + 1) ≤ c.1.val ∧ c.1.val < r.1.val then
          (if r.2 = c.2 then (1 : ℂ) else 0) else 0)
      - (if m * (k + 1) < (r.1 : ℕ) ∧ c.1.val + 1 = r.1.val then
          (if r.2 = c.2 then (1 : ℂ) else 0) else 0)

/-- The Taylor-system right-hand side, with `x_in` at label zero and `h • b` at the designated
first-order labels. -/
def taylorRHS (m k p : ℕ) (h : ℝ) (x_in b : QState N) :
    QState (Fin (m * (k + 1) + p + 1) × N) :=
  fun r =>
    if (r.1 : ℕ) = 0 then x_in r.2
    else if (r.1 : ℕ) ≤ m * (k + 1) ∧ (r.1 : ℕ) % (k + 1) = 1 then h * b r.2 else 0

/-- The state obtained by fixing the label register of `x` to `l`. -/
def taylorBlock {d : ℕ} (x : QState (Fin d × N)) (l : Fin d) : QState N :=
  fun n => x (l, n)

/-- The label `j * (k + 1)` of the time block with index `j ≤ m`. -/
def taylorTimeLabel (m k p j : ℕ) (hj : j ≤ m) : Fin (m * (k + 1) + p + 1) :=
  ⟨j * (k + 1), by
    have h1 : j * (k + 1) ≤ m * (k + 1) := Nat.mul_le_mul_right _ hj
    omega⟩

/-- The terminal label `m * (k + 1) + j` for `j ≤ p`. -/
def taylorFinalLabel (m k p j : ℕ) (hj : j ≤ p) : Fin (m * (k + 1) + p + 1) :=
  ⟨m * (k + 1) + j, by
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le hj) _⟩

/-- The constant-coefficient forced evolution used as the reference solution for the Taylor
system, with initial state `x_in` at time zero. -/
def taylorODESolution (A : Matrix N N ℂ) (b x_in : QState N) (t : ℝ) : QState N :=
  orderedForcedSolution (fun _ => -A) (fun _ => b) 0 x_in t

/-- The basis indices whose label lies in the terminal region starting at `m * (k + 1)`. -/
def taylorSuccessSet (m k p : ℕ) : Finset (Fin (m * (k + 1) + p + 1) × N) :=
  Finset.univ.filter fun r => m * (k + 1) ≤ (r.1 : ℕ)

/-- The coherent sum of the terminal blocks of `φ`. -/
def taylorExtract (m k p : ℕ) (φ : QState (Fin (m * (k + 1) + p + 1) × N)) : QState N :=
  fun n => ∑ l : Fin (m * (k + 1) + p + 1),
    if m * (k + 1) ≤ (l : ℕ) then φ (l, n) else 0

/-- The sum of the outer products of the terminal blocks of `φ`, representing the unnormalized
density after selecting those labels and discarding the label register. -/
def taylorMeasuredDensityV2 (m k p : ℕ)
    (φ : QState (Fin (m * (k + 1) + p + 1) × N)) : Matrix N N ℂ :=
  ∑ l : Fin (m * (k + 1) + p + 1),
    if m * (k + 1) ≤ (l : ℕ) then outerProduct (taylorBlock φ l) else 0

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
