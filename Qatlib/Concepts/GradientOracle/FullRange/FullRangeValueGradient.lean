/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision
import Mathlib.Analysis.SpecialFunctions.Log.Base
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.GradientOracle.ReadoutWindow
open Qatlib.Concepts.GradientOracle.ValueKickback

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.FullRange

def fullRangeClassicalBits (A : ℚ) : ℕ := Nat.clog 2 (max 2 (Nat.ceil A+1))

noncomputable section
open Matrix
open scoped Classical BigOperators

def fullRangeInteger {X : Type} (k : ℕ) (f : X → ℝ) (lo s : ℝ) (x : X) : ℤ :=
  ⌊(2 : ℝ)^k*s*(f x-lo)⌋

def fullRangeValueTable {X : Type} (K k : ℕ) (f : X → ℝ) (lo s : ℝ) :
    X → ZMod (2^(K+k)) := fun x => (fullRangeInteger k f lo s x : ZMod (2^(K+k)))

def fullRangeCharacterIndex (K k : ℕ) : ZMod (2^(K+k)) := (2^K : ℕ)

def fullRangeKickState (K k : ℕ) : QState (ZMod (2^(K+k))) :=
  fun y => (Real.sqrt (2^(K+k) : ℕ) : ℂ)⁻¹ *
    star (ZMod.stdAddChar (fullRangeCharacterIndex K k*y))

def fullRangePhase {X : Type} (K k : ℕ) (v : X → ZMod (2^(K+k))) : X → ℝ :=
  fun x => ((v x).val : ℝ)/(2 : ℝ)^k

def fullRangeGradientProgram (d M K k : ℕ) : Circuit (GradientGrid d M × ZMod (2^(K+k))) :=
  gradientValueProgram d M (2^(K+k))

def fullRangeGradientOutput (d M : ℕ) (hM : 0 < M) (K k : ℕ)
    (f : GradientGrid d M → ℝ) (lo s : ℝ) : QState (GradientGrid d M × ZMod (2^(K+k))) :=
  Run (gradientValueOracle (2^(K+k)) (fullRangeValueTable K k f lo s))
    (fullRangeGradientProgram d M K k)
    (TensorState (Ket (gradientZero d M hM)) (Ket (fullRangeCharacterIndex K k)))

end
end Qatlib.Concepts.GradientOracle.FullRange
