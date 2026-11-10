/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCounts
import Qatlib.Concepts.UniformBqp.Phi3Compile.MachineSource
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

structure RatAngle where

  num : ℕ

  den : ℕ

  den_pos : 0 < den

def RatAngle.value (a : RatAngle) : ℝ := (a.num : ℝ) / a.den

def dyadicApprox (a : RatAngle) (d : ℕ) : ℕ := (a.num * 2 ^ d) / a.den

def dyadicRemainder (a : RatAngle) (d : ℕ) : ℕ := (a.num * 2 ^ d) % a.den

def dyadicValue (a : RatAngle) (d : ℕ) : ℝ := (dyadicApprox a d : ℝ) / (2 ^ d : ℝ)

def phaseOf (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

def vonNeumannOut : List Bool → Option Bool
  | [b0, b1] => if b0 == b1 then some b0 else none
  | _ => none

def copyProgram (inW work : ℕ) : List DynOp :=
  [.alloc work, .fixedGate (.cx inW work), .fixedGate (.cx inW work), .releaseClean work]

def cleanBase {N : ℕ} (base : ℕ) (hbase : base ≤ N) (x : Reg N) : Prop :=
  ∀ w : ℕ, (hw : w < base) → x ⟨w, Nat.lt_of_lt_of_le hw hbase⟩ = false

def qtmTransition {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (m : LocalQTM Q A) : Matrix (Q × A) (Q × A) ℂ :=
  fun i j => m.step i.1 i.2 QtmMove.stay j.1 j.2

def qtmReverseTransition {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) : Matrix (Q × A) (Q × A) ℂ :=
  fun i j => star (m.step j.1 j.2 QtmMove.stay i.1 i.2)

def windowAcceptance {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) : ℂ :=
  ((qtmTransition m) ^ k) (m.start, m.blank) (qf, a)

def windowReverseAcceptance {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) : ℂ :=
  ((qtmReverseTransition m) ^ k) (m.start, m.blank) (qf, a)

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
