/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Complex.Norm
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.ClassicalTape.TapeCompilation.BitMachineTime
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
import Qatlib.Concepts.NativeNumerics.PhaseSynthesis.FinitePhaseSynthesis
set_option warningAsError false


open Qatlib.Concepts.ClassicalTape.TapeCompilation
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Matrix
open scoped Classical BigOperators

noncomputable def encodedPhaseWord (w : ℕ) (θ : Reg w → ℝ) : Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal fun x => Complex.exp (2 * Real.pi * Complex.I * θ x)

noncomputable def encodedSignClassifier (w : ℕ) (label : Reg w → Bool) :
    Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal fun x => if label x then (1 : ℂ) else -1

noncomputable def localProgramError {w : ℕ} (gs : List (LocalQFTGate w))
    (V : Matrix (Reg w) (Reg w) ℂ) (r : Reg w) : ℝ :=
  ∑ i, ‖(localProgramMatrix gs *ᵥ Ket r) i - (V *ᵥ Ket r) i‖ ^ 2

noncomputable def localProgramWithin {w : ℕ} (gs : List (LocalQFTGate w))
    (V : Matrix (Reg w) (Reg w) ℂ) (eps : ℝ) : Prop :=
  ∀ r : Reg w, localProgramError gs V r ≤ eps ^ 2

def HasLocalPhaseWordClassifierSynthesis : Prop :=
  ∃ C : ℕ → ℕ,
    (∀ (w : ℕ) (θ : Reg w → ℝ) (eps : ℝ), 0 < eps →
      ∃ gs : List (LocalQFTGate w),
        localProgramWithin gs (encodedPhaseWord w θ) eps ∧
          gs.length ≤ C w * (Nat.ceil ((1 / eps) ^ 2) + 1)) ∧
      (∀ (w : ℕ) (label : Reg w → Bool) (eps : ℝ), 0 < eps →
        ∃ gs : List (LocalQFTGate w),
          localProgramWithin gs (encodedSignClassifier w label) eps ∧
            gs.length ≤ C w * (Nat.ceil ((1 / eps) ^ 2) + 1))

def natTapeBits (n : ℕ) : List (Option Bool) :=
  (List.range (Nat.log2 n + 1)).reverse.map fun i => some (n.testBit i)

def ratTapeRecord (q : ℚ) : List (Option Bool) :=
  some (decide (q.num < 0)) :: natTapeBits q.num.natAbs ++ none :: natTapeBits q.den

def phaseTargetTape (p : List ℚ) (d : ℕ) (eps : ℚ) : List (Option Bool) :=
  (p.map ratTapeRecord).flatten ++ [none] ++ ratTapeRecord (d : ℚ) ++ [none] ++
    ratTapeRecord eps

def HasEfficientPhaseInversion : Prop :=
  ∃ (machine : Turing.TM0.Machine (Option Bool) (Fin 2))
      (out : Turing.TM0.Cfg (Option Bool) (Fin 2) → PhaseData),
    BitMachinePolynomialTime machine ∧
      ∀ (p : List ℚ) (d : ℕ) (eps : ℚ),
        0 < eps → (realTarget p).degree ≤ (d : WithBot ℕ) →
          Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d (realTarget p) →
          (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget p).eval x| ≤ 1) →
          ∃ (t : ℕ) (cfg : Turing.TM0.Cfg (Option Bool) (Fin 2)),
            BitMachineAfter machine (phaseTargetTape p d eps) t = some cfg ∧
              Turing.TM0.step machine cfg = none ∧
              let data := out cfg
              data.phases.length = d ∧
                ‖gaussianRatComplex data.base‖ = 1 ∧
                (∀ z ∈ data.phases, ‖gaussianRatComplex z‖ = 1) ∧
                (scoreData p d data).1.1 ≤ (1 / 2 : ℚ) ^ phaseToleranceBits eps ∧
                (∀ x ∈ Set.Icc (-1 : ℝ) 1,
                  |((responseP (gaussianRatComplex data.base)
                      (data.phases.map gaussianRatComplex)).eval (x : ℂ)).re -
                    (realTarget p).eval x| ≤ (eps : ℝ))

def phaseScoreStability : Prop :=
  ∀ (p q : List ℚ) (d : ℕ) (data : PhaseData) (δ : ℚ),
    0 ≤ δ → (∀ i : ℕ, |p.getD i 0 - q.getD i 0| ≤ δ) →
      |(scoreData p d data).1.1 - (scoreData q d data).1.1| ≤ ((d + 1 : ℕ) : ℚ) * δ

noncomputable def dyadicCode (x : ℝ) (r : ℕ) : ℤ := Int.floor (x * (2 ^ r : ℝ))

noncomputable def dyadicDecode (c : ℤ) (r : ℕ) : ℝ := (c : ℝ) / (2 ^ r : ℝ)

def dyadicBitWidth (c : ℤ) (r : ℕ) : ℕ := c.natAbs.size + r + 2

def HasGeneralRealQuantization : Prop :=
  ∀ (x : ℝ) (eps : ℝ), 0 < eps →
    ∃ (r : ℕ) (c : ℤ),
      |x - dyadicDecode c r| ≤ eps ∧
        ((2 ^ r : ℝ) ≥ 1 / eps) ∧
        c = dyadicCode x r ∧
        ((c.natAbs : ℝ) ≤ (|x| + 1) * (2 ^ r : ℝ))

def localProgramBitCost (w r : ℕ) (gs : List (LocalQFTGate w)) : ℕ :=
  gs.length * (w + 1) * (r + 2)

def localProgramSpaceBits (w r : ℕ) : ℕ := w + r

def HasIntegerBitBackend : Prop :=
  ∃ T : ℕ → ℕ → ℕ → ℕ,
    ∀ (w : ℕ) (θ : Reg w → ℝ) (eps : ℝ), 0 < eps →
      ∃ (r : ℕ) (k : Reg w → ℤ) (gs : List (LocalQFTGate w)),
        ((2 ^ r : ℝ) ≥ 2 / eps) ∧
          (∀ x : Reg w, |θ x - dyadicDecode (k x) r| ≤ eps / 2) ∧
          localProgramWithin gs
            (encodedPhaseWord w fun x => dyadicDecode (k x) r) (eps / 2) ∧
          localProgramBitCost w r gs ≤ T w r (Nat.ceil ((1 / eps) ^ 2) + 1) ∧
          localProgramSpaceBits w r = w + r

def powerTwoOracleWord {H : Type} (j : ℕ) : List (AdjointStep H) :=
  List.replicate (2 ^ j) AdjointStep.forward

noncomputable def oraclePowerIterate {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) : ℕ → Matrix H H ℂ
  | 0 => 1
  | n + 1 => oraclePowerIterate U n * U

def zeroQueryWordOracleIndependent : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (word : List (AdjointStep H))
      (U V : Matrix H H ℂ),
    adjointQueryCount word = 0 → evaluate U word = evaluate V word

def zeroQueryAdjointImpossible : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] [Nonempty H],
    ¬ ∃ word : List (AdjointStep H),
      adjointQueryCount word = 0 ∧
        ∀ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ → evaluate U word = Uᴴ

def zeroQueryControlledImpossible : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] [Nonempty H],
    ¬ ∃ W : Matrix (Bool × H) (Bool × H) ℂ,
      ∀ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ → W = controlOracle U

def noCountableRealCoverage : Prop :=
  ¬ ∃ e : ℕ → ℝ, Function.Surjective e

def rationalBackendMissesRealPhase : Prop :=
  ¬ ∀ φ : ℝ, ∃ z : GaussianRat,
    gaussianRatComplex z = Complex.exp (2 * Real.pi * Complex.I * φ)

def noFixedFiniteGatePhaseSynthesis : Prop :=
  ∀ (w : ℕ) (gs : List (LocalQFTGate w)) (_h : 0 < w),
    ∃ θ : Reg w → ℝ, localProgramMatrix gs ≠ encodedPhaseWord w θ

end Qatlib.Concepts.HspRecovery.ReductionCore
