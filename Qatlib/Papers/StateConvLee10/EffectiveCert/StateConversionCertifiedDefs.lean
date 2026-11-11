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

/-!
# Data for effective state-conversion certificates

This module defines rational Newton scales, a finite scale search, and a certificate carrying a
positive scale with a valid rational diagonal factorization. It also defines source-access
wires, an emitted primitive word, its native frame program, and exact and rationalized Gram
matrices for effective constructions associated with [LeeEtAl2011].

## Main statements

* `DiagonalScaleCertificate`: a positive rational scale together with a valid factorization
  witness.
* `scaleSearch`: a finite search for a Newton scale meeting a squared-error tolerance.
* `sourceFrameSynthesisProgram`: a source query followed by the lifted emitted local gates.
* `selectedComplexGram`: the Gram matrix of rationalized start coordinates.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

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

/-- The finite maximum of the absolute rational coordinates, with default value zero for an
empty index type. -/
def maxAbsRat {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) : ℚ :=
  Finset.fold max 0 (fun r => |a r|) (Finset.univ : Finset X)

/-- The rational Newton iteration starting at `M + 1` and replacing a scale `t` by `(t + M / t)
/ 2`. -/
def newtonScale (M : ℚ) : ℕ → ℚ
  | 0 => M + 1
  | n + 1 => (newtonScale M n + M / newtonScale M n) / 2

/-- The finite search that checks Newton iterates for squared error at most `δ`, returning no
value when the fuel is zero. -/
def scaleSearch (M δ : ℚ) : ℕ → Option ℚ
  | 0 => none
  | n + 1 => if newtonScale M n ^ 2 - M ≤ δ then some (newtonScale M n) else scaleSearch M δ n

/-- A positive rational scale together with a rational factorization witness for the diagonal
instance and a proof of its validity. -/
structure DiagonalScaleCertificate {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) where

  scale : ℚ

  witness : RationalRectFactorization 1 1 (diagonalRectInstance a).A (diagonalRectInstance a).Z

  scale_pos : 0 < scale

  witness_valid : RationalRectFactorization.rationalCertValid witness

/-- The diagonal scale certificate formed from a positive scale and validity of its
corresponding diagonal factorization. -/
def diagonalScaleCertificate {X : Type} [Fintype X] [DecidableEq X] (a : X → ℚ) (t : ℚ)
    (ht : 0 < t)
    (hv : RationalRectFactorization.rationalCertValid (diagonalRectFactorization a t)) :
    DiagonalScaleCertificate a where
  scale := t
  witness := diagonalRectFactorization a t
  scale_pos := ht
  witness_valid := hv

/-- The consecutive wire indices reserved for the source address and value registers. -/
def sourceAccessWires (d : SourceRationalProblem) (w : ℕ)
    (hw : sourceAddressBits d + sourceValueBits d ≤ w) : List (Fin w) :=
  (List.finRange (sourceAddressBits d + sourceValueBits d)).map
    (fun i => ⟨i.val, by omega⟩)

/-- The singleton word for a Hadamard, swap, or controlled-phase gate with exponent at most
three; controlled phases with larger exponent produce the empty word. -/
def emittedWord (w : ℕ) (g : LocalQFTGate w) (_k : ℕ) : List (LocalQFTGate w) :=
  match g with
  | .h a => [.h a]
  | .swap a c => [.swap a c]
  | .cp a c e neg => if e ≤ 3 then [.cp a c e neg] else []

/-- The native program consisting of a forward source-access query followed by the emitted local
word lifted to width `nativeFrameWidth d + k`. -/
def sourceFrameSynthesisProgram (d : SourceRationalProblem) (w : ℕ) (g : LocalQFTGate w) (k : ℕ)
    (hw : w ≤ nativeFrameWidth d + k) : SourceNativeProgram where
  width := nativeFrameWidth d + k
  steps := SourceNativeStep.query
      (sourceAccessWires d (nativeFrameWidth d + k) (by unfold nativeFrameWidth; omega)) false ::
    (liftWordTo hw (emittedWord w g k)).map (fun h => SourceNativeStep.local h)

/-- The complex number whose real and imaginary parts are the two rational coordinates. -/
def ratCoordComplex (p : ℚ × ℚ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

/-- The Gram matrix of the rationalized start states at precision `R`. -/
noncomputable def selectedComplexGram (d : SourceRealProblem) (hacc : sourceRealAccess d) (R : ℕ) :
    Matrix (Fin d.count) (Fin d.count) ℂ :=
  fun x y => ∑ h : Fin d.dimension,
    star (ratCoordComplex ((rationalizeReal d hacc R).start x h)) *
      (ratCoordComplex ((rationalizeReal d hacc R).start y h))

/-- The Gram matrix of the original complex start states. -/
noncomputable def trueComplexGram (d : SourceRealProblem) : Matrix (Fin d.count) (Fin d.count) ℂ :=
  fun x y => ∑ h : Fin d.dimension, star (d.start x h) * (d.start y h)

end Qatlib.Papers.StateConvLee10.EffectiveCert
