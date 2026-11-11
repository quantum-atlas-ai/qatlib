/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Qatlib.Concepts.GradientOracle.ReadoutWindow.ValueOracleGradientPrecision
import Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeValueGradient
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

/-!
# Value Oracle Gradient Specifications

`valuePhaseGate` and `valueComputeKickbackUncomputeWord` define a value-register phase
construction for the finite-grid gradient setting of [Jordan2005Gradient]. The word contains two
value-oracle uses and one phase gate; `stationaryPhaseResidual` and `gradientEstimate` describe
the affine residual and centered output coordinates.

The three `stageB_fourier_gradient_gext1_spec`, `stageB_fourier_gradient_gext2_spec`, and
`stageB_fourier_gradient_gext3_spec` propositions collect desired kickback, phase stability,
readout, dyadic representation, and resource identities. This module defines those
specifications; their definitions alone do not establish the collected properties.

## Main statements

- `valueComputeKickbackUncomputeWord` defines the value-register circuit word.
- `stageB_fourier_gradient_gext1_spec` collects phase construction and readout properties.
- `stageB_fourier_gradient_gext2_spec` collects decoding and representation properties.
- `stageB_fourier_gradient_gext3_spec` collects circuit and register resource properties.

## References

* [Jordan, 2005][Jordan2005Gradient], *Fast Quantum Algorithm for Numerical Gradient
  Estimation*.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The complex unit phase associated with the residue `y`, namely `exp (2*pi*I*y.val/Q)`. -/
noncomputable def valuePhaseCoeff (Q : ℕ) [NeZero Q] (y : ZMod Q) : ℂ :=
  Complex.exp (((2 * Real.pi * ((y.val : ℝ) / (Q : ℝ)) : ℝ) : ℂ) * Complex.I)

/-- The diagonal value-register gate with entries `valuePhaseCoeff Q y`. -/
noncomputable def valuePhaseGate (Q : ℕ) [NeZero Q] : Matrix (ZMod Q) (ZMod Q) ℂ :=
  Matrix.diagonal (fun y => valuePhaseCoeff Q y)

/-- The adjoint-query word with a backward query, a value-register phase gate, and a forward
query. -/
noncomputable def valueComputeKickbackUncomputeWord (d M Q : ℕ) [NeZero Q] :
    List (AdjointStep (GradientGrid d M × ZMod Q)) :=
  [.backward,
   .gate (TensorGate (1 : Matrix (GradientGrid d M) (GradientGrid d M) ℂ) (valuePhaseGate Q)),
   .forward]

/-- The value-register bit budget `Nat.clog 2 (max 2 Q)`. -/
def valueRegisterBits (Q : ℕ) : ℕ := Nat.clog 2 (max 2 Q)

/-- The phase remaining after subtracting the linear grid phase with slopes `g`. -/
noncomputable def stationaryPhaseResidual (d M : ℕ) (φ : GradientGrid d M → ℝ)
    (g : Fin d → ℝ) : GradientGrid d M → ℝ :=
  fun x => φ x - ∑ j : Fin d, g j * (x j).val

/-- The centered real grid output, defined by `signedGridValue M z`. -/
noncomputable def centeredGridOutput (M : ℕ) (z : Fin M) : ℝ :=
  signedGridValue M z

/-- The coordinatewise centered decoding of a grid measurement label. -/
noncomputable def gradientEstimate (d M : ℕ) (z : GradientGrid d M) : Fin d → ℝ :=
  fun j => centeredGridOutput M (z j)

/-- The proposition that the normalized grid label has an integer numerator over the dyadic
denominator `2^m`. -/
def DyadicGridLabel (m : ℕ) (z : Fin (2 ^ m)) : Prop :=
  ∃ n : ℤ, (z.val : ℝ) / (2 : ℝ) ^ m = (n : ℝ) / (2 : ℝ) ^ m

/-- The finite real-record predicate `HasDyadicRecord k θ` used for comparison with dyadic grid
outputs. -/
def GeneralRealRecord (k : ℕ) (θ : ℝ) : Prop :=
  HasDyadicRecord k θ

/-- The conjunction specifying value-oracle phase kickback and counts, integer-shift invariance,
modular phase stability, residual-based readout probability, and exact affine readout. -/
def stageB_fourier_gradient_gext1_spec : Prop :=
  (∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q) (x : GradientGrid d M),
      (evaluate (gradientValueOracle Q v) (valueComputeKickbackUncomputeWord d M Q)) *ᵥ
          (Ket (x, (0 : ZMod Q))) =
        valuePhaseCoeff Q (v x) • Ket (x, (0 : ZMod Q))) ∧
  (∀ (d M Q : ℕ) [NeZero Q],
      WellFormedAdjointCircuit (valueComputeKickbackUncomputeWord d M Q) ∧
      adjointQueryCount (valueComputeKickbackUncomputeWord d M Q) = 2 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q) = 1) ∧
  (∀ (d M : ℕ) (φ : GradientGrid d M → ℝ) (k : GradientGrid d M → ℤ),
      gradientPhase d M (fun x => φ x + (k x : ℝ)) = gradientPhase d M φ) ∧
  (∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q)
      (φ : GradientGrid d M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ),
      ‖gradientPhase d M (gradientValuePhase Q v) - gradientPhase d M φ‖ ≤ 2 * Real.pi * δ) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM φ)
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (q : GradientGrid d M) (c : ℝ),
      gradientReadout d M hM (fun x => c + ∑ j : Fin d, (q j).val * (x j).val / (M : ℝ))
        = Complex.exp (2 * Real.pi * Complex.I * (c : ℂ)) • Ket q)

/-- The conjunction specifying centered gradient decoding, residual-based readout probability,
dyadic output representations, and limits of the general real-record predicate. -/
def stageB_fourier_gradient_gext2_spec : Prop :=
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d, |gradientEstimate d M z j - g j| ≤ w) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |stationaryPhaseResidual d M φ g x - (c : ℝ)| ≤ B),
      MeasureProb (gradientReadout d M hM φ)
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)), DyadicGridLabel m z) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)),
      ∃ n : ℤ, centeredGridOutput (2 ^ m) z = (n : ℝ) / (2 : ℝ) ^ m) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)), GeneralRealRecord m ((z.val : ℝ) / (2 : ℝ) ^ m)) ∧
  (¬ GeneralRealRecord 0 (1 / 3)) ∧
  (¬ GeneralRealRecord 1 (1 / 3)) ∧
  (∀ (Q : ℕ) (hQ : 1 < Q), ¬ GeneralRealRecord 0 ((1 : ℝ) / Q))

/-- The conjunction specifying gradient circuit counts, readout and value-register bit budgets,
one-coordinate dyadic output, and a magnitude bound for accurate estimates. -/
def stageB_fourier_gradient_gext3_spec : Prop :=
  (∀ (d M : ℕ) (hM : 0 < M),
      IsUnitaryCircuit (gradientWord d M) ∧
      QueryCount (gradientWord d M) = 1 ∧
      GateCount (gradientWord d M) = 2 * d) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ),
      readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k) ∧
  (∀ (d M Q : ℕ) [NeZero Q], valueRegisterBits Q = Nat.clog 2 (max 2 Q)) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)),
      ∃ n : ℤ, gradientEstimate 1 (2 ^ m) (fun _ => z) 0 = (n : ℝ) / (2 : ℝ) ^ m) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (ê : Fin d → ℝ) (herror : ∀ j : Fin d, |ê j - g j| ≤ w),
      ∀ j : Fin d, |ê j| ≤ |g j| + w)

end Qatlib.Concepts.SignalPrimitive.GridGradient
