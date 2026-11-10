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
set_option warningAsError false

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

def IsEvenFunction (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, f (-x) = f x

def IsOddFunction (f : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, f (-x) = -f x

structure ModulusOfContinuity (f : ℝ → ℂ) (ω : ℝ → ℝ) : Prop where

  mono : Monotone ω

  at_zero : ω 0 = 0

  dominates :
    ∀ x y : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → y ∈ Set.Icc (-1 : ℝ) 1 →
      ‖f x - f y‖ ≤ ω |x - y|

noncomputable def modulusRobustnessFactor (δ : ℝ) : ℝ :=
  4 * (Real.log (2 / δ + 1) + 1) ^ 2

noncomputable def polynomialRobustnessBound (n : ℕ) (δ : ℝ) : ℝ :=
  4 * n * Real.sqrt δ

noncomputable def interiorRobustnessRate (n : ℕ) (m δ : ℝ) : ℝ :=
  n * Real.sqrt (2 / (1 - m ^ 2)) * δ

noncomputable def polynomialResponse (P : Polynomial ℂ) : ℝ → ℂ :=
  fun x => P.eval (x : ℂ)

structure Cor8Admissible (P : Polynomial ℂ) (n : ℕ) : Prop where

  parity : Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.HasResponseParity n P

  interval : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 →
    Complex.normSq (P.eval (Complex.ofReal x)) ≤ 1

  exterior : ∀ x : ℝ, x ∉ Set.Ioo (-1 : ℝ) 1 →
    1 ≤ Complex.normSq (P.eval (Complex.ofReal x))

  imaginaryAxis : n % 2 = 0 → ∀ y : ℝ,
    1 ≤ Complex.normSq (P.eval (Complex.ofReal y * Complex.I))

def IsUnitConstantPolynomial (P : Polynomial ℂ) : Prop :=
  ∃ c : ℂ, P = C c ∧ Complex.normSq c = 1

def IsPhaseTable (zs : List ℂ) : Prop :=
  ∀ z ∈ zs, IsPhase z

noncomputable def anglePhaseTable (Φ : List ℝ) : List ℂ :=
  Φ.map anglePhase

def sourceCppQuadruple (d : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (d, 2 * (d / 2), 2 * ((d + 1) / 2), d)

structure QsvtCostLedger where

  dataQueries : ℕ

  adjointQueries : ℕ

  projectorNots : ℕ

  phaseGates : ℕ

  elementaryGates : ℕ

  integerBitTime : ℕ

  peakWorkspace : ℕ

structure QsvtProgram where

  angles : List ℝ

  ledger : QsvtCostLedger

def truncationErrorWithin (ε : ℝ) (f g : ℝ → ℂ) : Prop :=
  ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → ‖f x - g x‖ ≤ ε

def angleTableWithin (ε : ℝ) : List ℝ → List ℝ → Prop :=
  List.Forall₂ (fun a b => |a - b| ≤ ε)

noncomputable def binaryPrecisionBits (ε : ℝ) : ℕ :=
  Nat.ceil (Real.log (1 / ε) / Real.log 2) + 1

end Qatlib.Concepts.QsvtCore.PhaseExistence
