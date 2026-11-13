/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.GateSynthesis.GateCounts
import Qatlib.Concepts.UniformBqp.Phi3Compile.MachineSource
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Rational phases and finite execution data

This module defines nonnegative rational angles, their dyadic quotient and remainder, and the
complex phase function `phaseOf`. It also supplies a short allocation-and-uncomputation program
and the stay-move transition matrices used for finite local quantum-machine calculations, within
the amplitude formalism of [NielsenChuang2010].

The function `vonNeumannOut` selects the common bit of an equal two-bit input. The window
quantities select entries of powers of the forward and conjugate-transposed transition matrices.

## Main definitions

* `RatAngle` and `dyadicValue`: rational angle data and its dyadic truncation.
* `copyProgram`: an allocation, two identical CNOT gates, and a clean release.
* `qtmTransition` and `qtmReverseTransition`: forward and reverse stay-move matrices.
* `windowAcceptance` and `windowReverseAcceptance`: selected finite-power matrix entries.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.ResourceBounds.AsymBounds
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
noncomputable section

namespace Qatlib.Concepts.CircuitImpl.GateSynthesis

open Matrix
open Qatlib
open scoped Classical BigOperators ENNReal

/-- A nonnegative rational angle represented by a natural numerator and a positive natural
denominator. -/
structure RatAngle where

  num : ℕ

  den : ℕ

  den_pos : 0 < den

/-- The real value of a rational angle, obtained by dividing its numerator by its denominator. -/
def RatAngle.value (a : RatAngle) : ℝ := (a.num : ℝ) / a.den

/-- The natural quotient of `a.num * 2 ^ d` by `a.den`, giving the numerator of the dyadic
approximation. -/
def dyadicApprox (a : RatAngle) (d : ℕ) : ℕ := (a.num * 2 ^ d) / a.den

/-- The natural remainder of `a.num * 2 ^ d` upon division by `a.den`. -/
def dyadicRemainder (a : RatAngle) (d : ℕ) : ℕ := (a.num * 2 ^ d) % a.den

/-- The real dyadic approximation obtained by dividing `dyadicApprox a d` by `2 ^ d`. -/
def dyadicValue (a : RatAngle) (d : ℕ) : ℝ := (dyadicApprox a d : ℝ) / (2 ^ d : ℝ)

/-- The complex phase `exp (Complex.I * θ)` associated with the real angle `θ`. -/
def phaseOf (θ : ℝ) : ℂ := Complex.exp (Complex.I * (θ : ℂ))

/-- The common bit of an equal two-bit list, returning `none` for unequal pairs or any other
list length. -/
def vonNeumannOut : List Bool → Option Bool
  | [b0, b1] => if b0 == b1 then some b0 else none
  | _ => none

/-- The dynamic program that allocates `work`, applies the same CNOT from `inW` to `work` twice,
and requests a clean release of `work`. -/
def copyProgram (inW work : ℕ) : List DynOp :=
  [.alloc work, .fixedGate (.cx inW work), .fixedGate (.cx inW work), .releaseClean work]

/-- The predicate that every register wire with index strictly below `base` contains `false`. -/
def cleanBase {N : ℕ} (base : ℕ) (hbase : base ≤ N) (x : Reg N) : Prop :=
  ∀ w : ℕ, (hw : w < base) → x ⟨w, Nat.lt_of_lt_of_le hw hbase⟩ = false

/-- The local transition matrix whose entries are the machine's stay-move amplitudes between
state-symbol pairs. -/
def qtmTransition {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (m : LocalQTM Q A) : Matrix (Q × A) (Q × A) ℂ :=
  fun i j => m.step i.1 i.2 QtmMove.stay j.1 j.2

/-- The matrix formed by swapping the state-symbol indices of the stay-move amplitudes and
taking their complex conjugates. -/
def qtmReverseTransition {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) : Matrix (Q × A) (Q × A) ℂ :=
  fun i j => star (m.step j.1 j.2 QtmMove.stay i.1 i.2)

/-- The entry of `(qtmTransition m) ^ k` with row `(m.start, m.blank)` and column `(qf, a)`. -/
def windowAcceptance {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A] [DecidableEq A]
    (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) : ℂ :=
  ((qtmTransition m) ^ k) (m.start, m.blank) (qf, a)

/-- The entry of `(qtmReverseTransition m) ^ k` with row `(m.start, m.blank)` and column `(qf,
a)`. -/
def windowReverseAcceptance {Q A : Type} [Fintype Q] [DecidableEq Q] [Fintype A]
    [DecidableEq A] (m : LocalQTM Q A) (k : ℕ) (qf : Q) (a : A) : ℂ :=
  ((qtmReverseTransition m) ^ k) (m.start, m.blank) (qf, a)

end Qatlib.Concepts.CircuitImpl.GateSynthesis

end
