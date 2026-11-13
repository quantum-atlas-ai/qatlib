/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientOracle

/-!
# Probability oracles and realized phase definitions

This module defines `ProbabilityOracle` as a grid function with values in `[0, 1]`, its accuracy
predicate, and its associated phase rotation. `composedGoodWindow` and the refined specification
connect these interfaces to Fourier gradient estimation [Jordan2005Gradient].

The remaining definitions compress an operator to `probabilityProgramFrame`, extract its
diagonal phase coefficients, measure their deviations and moduli, and form both raw and
normalized diagonal operators. Their approximation and unitarity properties are proved in the
companion module.

## Main statements

* `ProbabilityReadAccurate`: uniform error against a specified real function.
* `probabilityProgramFrameOperator`: compression to the input frame.
* `probabilityNormalizedRealizedPhaseOperator`: the diagonal operator formed by modulus
  normalization.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

/-- A probability function on the gradient grid with a pointwise proof that its values lie in
`[0, 1]`. -/
structure ProbabilityOracle (d M : ℕ) where

  prob : GradientGrid d M → ℝ

  prob_valid : ∀ x, 0 ≤ prob x ∧ prob x ≤ 1

/-- States that a probability oracle approximates the supplied real function uniformly within
`ε`. -/
def ProbabilityReadAccurate {d M : ℕ} (o : ProbabilityOracle d M)
    (truth : GradientGrid d M → ℝ) (ε : ℝ) : Prop :=
  ∀ x, |o.prob x - truth x| ≤ ε

/-- The diagonal probability phase rotation associated with a probability oracle. -/
noncomputable def probabilityOracleRotation {d M : ℕ} (o : ProbabilityOracle d M) :
    Matrix (GradientGrid d M) (GradientGrid d M) ℂ :=
  Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityPhaseOperator o.prob

/-- The probability oracle's phase function in the gradient readout convention. -/
noncomputable def probabilityOraclePhase {d M : ℕ} (o : ProbabilityOracle d M) :
    GradientGrid d M → ℝ :=
  Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase o.prob

/-- The finite set of readout labels within modular distance `w` of every target gradient
coordinate. -/
noncomputable def composedGoodWindow (d M : ℕ) (g : Fin d → ℝ) (w : ℝ) :
    Finset (GradientGrid d M) :=
  Finset.univ.filter (fun z => ∀ j : Fin d,
    phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)

/-- The refined specification for probability phase errors, readout transport, composed success
probability, and explicit query and gate counts. -/
def stageB_gradient_oracle_clause2_next_spec : Prop :=
  (∀ {X : Type} [Fintype X] [DecidableEq X] (p q : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε),
      ‖Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityPhaseOperator p
          - Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityPhaseOperator q‖
        ≤ ε) ∧
  (∀ {X : Type} [Fintype X] [DecidableEq X] (p q : X → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε) (x : X),
      |Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase p x
          - Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase q x|
        ≤ ε / (2 * Real.pi)) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (herror : ∀ x, |p x - q x| ≤ ε) (S : Finset (GradientGrid d M)),
      |MeasureProb (gradientReadout d M hM
            (Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase p)) S
          - MeasureProb (gradientReadout d M hM
            (Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase q)) S|
        ≤ 2 * ε) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) (g : Fin d → ℝ) (c w B : ℝ) (hw : 0 < w)
      (hB : 0 ≤ B) (p q : GradientGrid d M → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
      (hlin : ∀ x, |Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase p x
          - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B)
      (herror : ∀ x, |p x - q x| ≤ ε),
      MeasureProb (gradientReadout d M hM
            (Qatlib.Concepts.FourierRecovery.ModularFourier.probabilityReadoutPhase q))
          (composedGoodWindow d M g w)
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B - 2 * ε) ∧
  (∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ) (d M : ℕ)
      (hM : 0 < M),
      adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k) = 6912 * k + 110646 ∧
        adjointGateCount (probabilityPhaseWord (X := X) a₀ good k) = 6912 * k + 110861 ∧
        QueryCount (gradientWord d M) = 1 ∧
        GateCount (gradientWord d M) = 2 * d)

/-- The frame embedding formed by the clean input frame, Hamiltonian frame, and three auxiliary
Boolean registers. -/
noncomputable def probabilityProgramFrame {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A) :
    Matrix (Bool × (Bool × (Bool × (X × A)))) X ℂ :=
  scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀))

/-- Compresses an operator to the probability program frame as `Fᴴ * Aop * F`. -/
noncomputable def probabilityProgramFrameOperator {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ) :
    Matrix X X ℂ :=
  (probabilityProgramFrame (X := X) a₀)ᴴ * Aop * probabilityProgramFrame (X := X) a₀

/-- The diagonal coefficient at `x` of the operator compressed to the probability program frame. -/
noncomputable def probabilityRealizedPhase {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ)
    (x : X) : ℂ :=
  (probabilityProgramFrameOperator (X := X) a₀ Aop) x x

/-- The norm of the difference between a realized phase coefficient and `exp (i * p x)`. -/
noncomputable def probabilityPhaseDeviation {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ)
    (p : X → ℝ) (x : X) : ℝ :=
  ‖probabilityRealizedPhase (X := X) a₀ Aop x - Complex.exp (Complex.I * (p x : ℂ))‖

/-- The diagonal matrix formed from the realized phase coefficients. -/
noncomputable def probabilityRealizedPhaseOperator {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ) :
    Matrix X X ℂ :=
  Matrix.diagonal (fun x => probabilityRealizedPhase (X := X) a₀ Aop x)

/-- The norm of a realized phase coefficient. -/
noncomputable def probabilityRealizedPhaseModulus {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ)
    (x : X) : ℝ :=
  ‖probabilityRealizedPhase (X := X) a₀ Aop x‖

/-- The realized phase coefficient divided by its modulus. -/
noncomputable def probabilityNormalizedRealizedPhase {X A : Type} [Fintype X] [Fintype A]
    [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ)
    (x : X) : ℂ :=
  probabilityRealizedPhase (X := X) a₀ Aop x
    / (probabilityRealizedPhaseModulus (X := X) a₀ Aop x : ℂ)

/-- The diagonal matrix formed from the normalized realized phase coefficients. -/
noncomputable def probabilityNormalizedRealizedPhaseOperator {X A : Type} [Fintype X]
    [Fintype A] [DecidableEq X] [DecidableEq A] (a₀ : A)
    (Aop : Matrix (Bool × (Bool × (Bool × (X × A)))) (Bool × (Bool × (Bool × (X × A)))) ℂ) :
    Matrix X X ℂ :=
  Matrix.diagonal (fun x => probabilityNormalizedRealizedPhase (X := X) a₀ Aop x)

end Qatlib.Concepts.FourierRecovery.ModularFourier
