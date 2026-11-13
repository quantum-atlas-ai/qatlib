/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.HermitianFunctionStability
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
import Qatlib.Concepts.QsvtCore.QsVtMain.LengthQSVT

/-!
# Source QSVT response conditions and costs

This module defines response conditions and resource records for the QSVT statements associated
with [GilyenSuLowWiebe2019]. `Cor8Admissible` packages parity and norm constraints on the real
and imaginary axes, while `ModulusOfContinuity` specifies a monotone difference bound on the
unit interval.

The definitions also provide polynomial responses, angle tables, explicit robustness
expressions, and the records `QsvtCostLedger` and `QsvtProgram` used to state resource bounds.

## Main statements

* `Cor8Admissible`: reflection-response conditions.
* `ModulusOfContinuity`: a difference bound on `[-1, 1]`.
* `QsvtCostLedger` and `QsvtProgram`: resource counts and angle data.
* `truncationErrorWithin` and `angleTableWithin`: response and angle error predicates.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.TrotterFormula.SuzukiFourth

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.PhaseExistence

open Polynomial
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open scoped Classical BigOperators

/-- States that the complex-valued response is even. -/
def IsEvenFunction (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, f (-x) = f x

/-- States that the complex-valued response is odd. -/
def IsOddFunction (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, f (-x) = -f x

/-- A monotone function vanishing at zero that bounds response differences on `[-1, 1]`. -/
structure ModulusOfContinuity (f : ℝ → ℂ) (ω : ℝ → ℝ) : Prop where

  mono : Monotone ω

  at_zero : ω 0 = 0

  dominates :
    ∀ x y : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 →
      ‖f x - f y‖ ≤ ω |x - y|

/-- The logarithmic robustness factor `4 * (log (2 / δ + 1) + 1)^2`. -/
noncomputable def modulusRobustnessFactor (δ : ℝ) : ℝ :=
  4 * (Real.log (2 / δ + 1) + 1) ^ 2

/-- The polynomial robustness bound `4 * n * sqrt δ`. -/
noncomputable def polynomialRobustnessBound (n : ℕ) (δ : ℝ) : ℝ :=
  4 * n * Real.sqrt δ

/-- The interior robustness expression `n * sqrt (2 / (1 - m^2)) * δ`. -/
noncomputable def interiorRobustnessRate (n : ℕ) (m δ : ℝ) : ℝ :=
  n * Real.sqrt (2 / (1 - m ^ 2)) * δ

/-- The complex polynomial evaluated on real inputs. -/
noncomputable def polynomialResponse (P : Polynomial ℂ) : ℝ → ℂ :=
  fun x => P.eval (x : ℂ)

/-- The response parity, real-interval and exterior norm conditions, and even-order
imaginary-axis condition used for reflection-based phase synthesis in
[GilyenSuLowWiebe2019]. -/
structure Cor8Admissible (P : Polynomial ℂ) (n : ℕ) : Prop where

  parity : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity n P

  interval : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
    Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1

  exterior : ∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
    1 ≤ Complex.normSq (P.eval (Complex.ofReal x))

  imaginaryAxis : n % 2 = 0 → ∀ y : ℝ,
    1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))

/-- States that a polynomial is constant with a complex value of squared norm one. -/
def IsUnitConstantPolynomial (P : Polynomial ℂ) : Prop :=
  ∃ c : ℂ, P = C c ∧ Complex.normSq c = 1

/-- States that every entry of a complex phase list is a unit phase. -/
def IsPhaseTable (zs : List ℂ) : Prop :=
  ∀ z ∈ zs, IsPhase z

/-- Maps a real angle list to its corresponding list of complex phases. -/
noncomputable def anglePhaseTable (Φ : List ℝ) : List ℂ :=
  Φ.map anglePhase

/-- The source resource tuple `(d, 2 * (d / 2), 2 * ((d + 1) / 2), d)`. -/
def sourceCppQuadruple (d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (d, 2 * (d / 2), 2 * ((d + 1) / 2), d)

/-- A record of data and adjoint queries, projector-controlled NOTs, phase and elementary gates,
integer bit time, and peak workspace. -/
structure QsvtCostLedger where

  dataQueries : ℕ

  adjointQueries : ℕ

  projectorNots : ℕ

  phaseGates : ℕ

  elementaryGates : ℕ

  integerBitTime : ℕ

  peakWorkspace : ℕ

/-- A real angle list paired with a QSVT cost ledger. -/
structure QsvtProgram where

  angles : List ℝ

  ledger : QsvtCostLedger

/-- States that two responses differ in norm by at most `ε` throughout `[-1, 1]`. -/
def truncationErrorWithin (ε : ℝ) (f g : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f x - g x‖ ≤ ε

/-- Relates two angle lists pointwise by absolute error at most `ε`. -/
def angleTableWithin (ε : ℝ) : List ℝ → List ℝ → Prop :=
  List.Forall₂ (fun a b => |a - b| ≤ ε)

/-- The binary precision count `ceil (log (1 / ε) / log 2) + 1`. -/
noncomputable def binaryPrecisionBits (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1

end Qatlib.Concepts.QsvtCore.PhaseExistence
