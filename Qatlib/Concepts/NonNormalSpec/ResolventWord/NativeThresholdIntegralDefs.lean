/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralDefs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Nat.Log
set_option warningAsError false

set_option autoImplicit false

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord

def rationalPolynomialCompose : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => ratAddList [x] (ratMulList (rationalPolynomialCompose xs ys) ys)

def rationalThresholdCoefficients (τ : ℚ) (k : ℕ) : List ℚ :=
  (ratAddList [1]
    (rationalPolynomialCompose (rationalSignCoefficients k) [-(τ ^ 2), 0, 1])).map
      (fun x => x / 2)

def rationalIntegralCoefficients (γ : ℚ) (xs : List ℚ) : List ℚ :=
  0 :: xs.zipIdx.map (fun ai => γ * ai.1 / (ai.2 + 1 : ℚ))

def rationalIntegratedThresholdCoefficients (γ δ : ℚ) (k : ℕ) : List ℚ :=
  rationalIntegralCoefficients γ
    (ratSubList [1] (rationalThresholdCoefficients ((1 - δ / 2) / γ) k))

def nativeAmplifierGap (γ δ : ℚ) : ℚ := δ / (4 * γ ^ 2)
def nativeAmplifierTolerance (γ δ ε : ℚ) : ℚ := min ε (δ / (4 * γ))
def nativeAmplifierLogBudget (γ δ ε : ℚ) : ℕ :=
  Nat.clog 2 (Nat.ceil (1 / nativeAmplifierTolerance γ δ ε))
def nativeAmplifierExponentBudget (γ δ ε : ℚ) : ℕ :=
  Nat.ceil ((nativeAmplifierGap γ δ)⁻¹ ^ 2 * nativeAmplifierLogBudget γ δ ε)
def nativeAmplifierCutoff (γ δ ε : ℚ) : ℕ :=
  Nat.clog 2 (nativeAmplifierExponentBudget γ δ ε)
def nativeAmplifierDegree (γ δ ε : ℚ) : ℕ := 2 * 3 ^ nativeAmplifierCutoff γ δ ε + 1

def nativeAmplifierPhaseResult (γ δ ε : ℚ) : SynthesisResult :=
  finitePhaseSynthesis
    (rationalIntegratedThresholdCoefficients γ δ (nativeAmplifierCutoff γ δ ε))
    (nativeAmplifierDegree γ δ ε) (ε / 2)

end Qatlib.Concepts.NonNormalSpec.ResolventWord
