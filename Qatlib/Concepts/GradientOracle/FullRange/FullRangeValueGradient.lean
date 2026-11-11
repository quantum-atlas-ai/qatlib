/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Full-range dyadic value encoding

This module defines the guarded range width, floor-based value labels, character state, and
full-range gradient program. The separation between range bits and fractional bits implements
the value-oracle precision setup associated with [Jordan2005Gradient].

## Main definitions

* `fullRangeValueTable`: scaled values reduced modulo `2^(K+k)`.
* `fullRangeKickState`: the Fourier character indexed by `2^K`.
* `fullRangeGradientOutput`: execution of the value-oracle program from basis-state inputs.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange

/-- The ceiling binary logarithm of `max 2 (Nat.ceil A + 1)`, used as the range-bit width for
the scaled value range. -/
def fullRangeClassicalBits (A : ℚ) : ℕ := Nat.clog 2 (max 2 (Nat.ceil A+1))

noncomputable section
open Matrix
open scoped Classical BigOperators

/-- The integer floor of `2^k * s * (f x-lo)`, encoding the scaled value with `k` fractional
bits. -/
def fullRangeInteger {X : Type} (k : ℕ) (f : X → ℝ) (lo s : ℝ) (x : X) : ℤ :=
  ⌊(2 : ℝ)^k*s*(f x-lo)⌋

/-- The modular value table obtained by reducing `fullRangeInteger` modulo `2^(K+k)`. -/
def fullRangeValueTable {X : Type} (K k : ℕ) (f : X → ℝ) (lo s : ℝ) :
    X → ZMod (2^(K+k)) := fun x => (fullRangeInteger k f lo s x : ZMod (2^(K+k)))

/-- The character index `2^K` in the target register modulo `2^(K+k)`. -/
def fullRangeCharacterIndex (K k : ℕ) : ZMod (2^(K+k)) := (2^K : ℕ)

/-- The inverse-square-root-scaled conjugate additive character with index
`fullRangeCharacterIndex`, used for full-range phase kickback. -/
def fullRangeKickState (K k : ℕ) : QState (ZMod (2^(K+k))) :=
  fun y => (Real.sqrt (2^(K+k) : ℕ) : ℂ)⁻¹ *
    star (ZMod.stdAddChar (fullRangeCharacterIndex K k*y))

/-- The real phase table obtained by dividing each canonical modular value label by `2^k`. -/
def fullRangePhase {X : Type} (K k : ℕ) (v : X → ZMod (2^(K+k))) : X → ℝ :=
  fun x => ((v x).val : ℝ)/(2 : ℝ)^k

/-- The value-oracle gradient program with target register of size `2^(K+k)`, including
character-state preparation. -/
def fullRangeGradientProgram (d M K k : ℕ) : Circuit (GradientGrid d M × ZMod (2^(K+k))) :=
  gradientValueProgram d M (2^(K+k))

/-- The state produced by the full-range value-oracle gradient program from zero data and the
basis state indexed by `fullRangeCharacterIndex`. -/
def fullRangeGradientOutput (d M : ℕ) (hM : 0 < M) (K k : ℕ)
    (f : GradientGrid d M → ℝ) (lo s : ℝ) : QState (GradientGrid d M × ZMod (2^(K+k))) :=
  Run (gradientValueOracle (2^(K+k)) (fullRangeValueTable K k f lo s))
    (fullRangeGradientProgram d M K k)
    (TensorState (Ket (gradientZero d M hM)) (Ket (fullRangeCharacterIndex K k)))

end
end Qatlib.Concepts.GradientOracle.FullRange
