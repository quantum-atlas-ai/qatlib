/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.TimeOrdered.TimeOrderedConsumers
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Foundations.InstrumentCore.Measurement.Basic
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
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

def taylorRHS (m k p : ℕ) (h : ℝ) (x_in b : QState N) :
    QState (Fin (m * (k + 1) + p + 1) × N) :=
  fun r =>
    if (r.1 : ℕ) = 0 then x_in r.2
    else if (r.1 : ℕ) ≤ m * (k + 1) ∧ (r.1 : ℕ) % (k + 1) = 1 then h * b r.2 else 0

def taylorBlock {d : ℕ} (x : QState (Fin d × N)) (l : Fin d) : QState N :=
  fun n => x (l, n)

def taylorTimeLabel (m k p j : ℕ) (hj : j ≤ m) : Fin (m * (k + 1) + p + 1) :=
  ⟨j * (k + 1), by
    have h1 : j * (k + 1) ≤ m * (k + 1) := Nat.mul_le_mul_right _ hj
    omega⟩

def taylorFinalLabel (m k p j : ℕ) (hj : j ≤ p) : Fin (m * (k + 1) + p + 1) :=
  ⟨m * (k + 1) + j, by
    exact Nat.add_lt_add_left (Nat.lt_succ_of_le hj) _⟩

def taylorODESolution (A : Matrix N N ℂ) (b x_in : QState N) (t : ℝ) : QState N :=
  orderedForcedSolution (fun _ => -A) (fun _ => b) 0 x_in t

def taylorSuccessSet (m k p : ℕ) : Finset (Fin (m * (k + 1) + p + 1) × N) :=
  Finset.univ.filter fun r => m * (k + 1) ≤ (r.1 : ℕ)

def taylorExtract (m k p : ℕ) (φ : QState (Fin (m * (k + 1) + p + 1) × N)) : QState N :=
  fun n => ∑ l : Fin (m * (k + 1) + p + 1),
    if m * (k + 1) ≤ (l : ℕ) then φ (l, n) else 0

def taylorMeasuredDensityV2 (m k p : ℕ)
    (φ : QState (Fin (m * (k + 1) + p + 1) × N)) : Matrix N N ℂ :=
  ∑ l : Fin (m * (k + 1) + p + 1),
    if m * (k + 1) ≤ (l : ℕ) then outerProduct (taylorBlock φ l) else 0

end Qatlib.Papers.QLinearODE17.TaylorAnalysis
