/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionEffective
import Qatlib.Concepts.ConversionCore.WitnessCompile.StateConversionDefs
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesis
import Qatlib.Concepts.NumericalWord.MixedWordError.FixedGateSynthesisDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.BitWordCompiler.WordComposition
open Qatlib.Concepts.NumericalWord.MixedWordError
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.ConversionCore.WitnessCompile
open Qatlib.Concepts.ConversionCore.WitnessCompile.RationalRectFactorization

set_option autoImplicit false

namespace Qatlib.Papers.StateConvLee10.EffectiveCert

open Qatlib
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

def maxAbsRat {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) : ℚ :=
  Finset.fold max 0 (fun r => |a r|) (Finset.univ : Finset X)

def newtonScale (M : ℚ) : ℕ → ℚ
  | 0 => M + 1
  | n + 1 => (newtonScale M n + M / newtonScale M n) / 2

def scaleSearch (M δ : ℚ) : ℕ → Option ℚ
  | 0 => none
  | n + 1 => if newtonScale M n ^ 2 - M ≤ δ then some (newtonScale M n) else scaleSearch M δ n

structure DiagonalScaleCertificate {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) where

  scale : ℚ

  witness : RationalRectFactorization 1 1 (diagonalRectInstance a).A (diagonalRectInstance a).Z

  scale_pos : 0 < scale

  witness_valid : RationalRectFactorization.rationalCertValid witness

def diagonalScaleCertificate {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) (t : ℚ)
    (ht : 0 < t)
    (hv : RationalRectFactorization.rationalCertValid (diagonalRectFactorization a t)) :
    DiagonalScaleCertificate a where
  scale := t
  witness := diagonalRectFactorization a t
  scale_pos := ht
  witness_valid := hv

def sourceAccessWires (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d + sourceValueBits d ≤ w) : List (Fin w) :=
  (List.finRange (sourceAddressBits d + sourceValueBits d)).map
    (fun i => ⟨i.val, by omega⟩)

def emittedWord (w : ℕ) (g : LocalQFTGate w) (_k : ℕ) : List (LocalQFTGate w) :=
  match g with
  | .h a => [.h a]
  | .swap a c => [.swap a c]
  | .cp a c e neg => if e ≤ 3 then [.cp a c e neg] else []

def sourceFrameSynthesisProgram (d : SourceRationalProblem) (w : ℕ) (g : LocalQFTGate w) (k : ℕ)
    (hw : w ≤ nativeFrameWidth d + k) : SourceNativeProgram where
  width := nativeFrameWidth d + k
  steps := SourceNativeStep.query
      (sourceAccessWires d (nativeFrameWidth d + k) (by unfold nativeFrameWidth; omega)) false ::
    (liftWordTo hw (emittedWord w g k)).map (fun h => SourceNativeStep.local h)

def ratCoordComplex (p : ℚ × ℚ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

noncomputable def selectedComplexGram (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    Matrix (Fin d.count) (Fin d.count) ℂ :=
  fun x y => ∑ h : Fin d.dimension,
    star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
      (ratCoordComplex ((rationalizeReal d hacc R).start y h))

noncomputable def trueComplexGram (d : SourceRealProblem) : Matrix (Fin d.count) (Fin d.count) ℂ :=
  fun x y => ∑ h : Fin d.dimension, star (d.start x h) * (d.start y h)

end Qatlib.Papers.StateConvLee10.EffectiveCert
