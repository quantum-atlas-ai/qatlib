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

/-!
# Phase synthesis and oracle access specifications

This module defines diagonal phase targets, Boolean sign targets, and basis-state approximation
errors for local gate programs. It formulates synthesis, rational phase inversion, dyadic
quantization, and bit-resource contracts in the circuit and signal-processing settings of
[NielsenChuang2010] and [LowChuang2017].

It also states oracle-independence and exact-representation obstructions as propositions,
distinguishing finite program descriptions from arbitrary real phase data.

## Main definitions

* `HasLocalPhaseWordClassifierSynthesis`: local approximation and program-length requirements.
* `HasEfficientPhaseInversion`: polynomial-time phase data production for rational polynomial
  targets.
* `HasIntegerBitBackend`: dyadic phase approximation with bit-cost accounting.
* `zeroQueryAdjointImpossible`: the proposed impossibility of universal adjoint evaluation
  without queries.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
* [Low and Chuang, 2017][LowChuang2017]
-/

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

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Matrix
open scoped Classical BigOperators

/-- The diagonal matrix whose entry at register `x` is the phase `exp (2πi θ(x))`. -/
noncomputable def encodedPhaseWord (w : ℕ) (θ : Reg w → ℝ) : Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal fun x => Complex.exp (2 * Real.pi * Complex.I * θ x)

/-- The diagonal sign matrix with entry 1 at registers labeled true and entry -1 at registers
labeled false. -/
noncomputable def encodedSignClassifier (w : ℕ) (label : Reg w → Bool) :
    Matrix (Reg w) (Reg w) ℂ :=
  Matrix.diagonal fun x => if label x then (1 : ℂ) else -1

/-- The squared Euclidean error between the local program and target matrix applied to the basis
ket at `r`. -/
noncomputable def localProgramError {w : ℕ} (gs : List (LocalQFTGate w))
    (V : Matrix (Reg w) (Reg w) ℂ) (r : Reg w) : ℝ :=
  ∑ i, ‖(localProgramMatrix gs *ᵥ Ket r) i - (V *ᵥ Ket r) i‖ ^ 2

/-- The condition that every basis ket has squared approximation error at most `eps ^ 2` under
the local program. -/
noncomputable def localProgramWithin {w : ℕ} (gs : List (LocalQFTGate w))
    (V : Matrix (Reg w) (Reg w) ℂ) (eps : ℝ) : Prop :=
  ∀ r : Reg w, localProgramError gs V r ≤ eps ^ 2

/-- The existence of local approximations to all diagonal phase and Boolean sign targets, with
basis-state error at most `eps` and length bounded by `C w * (Nat.ceil ((1 / eps) ^ 2) + 1)`
for a common width-dependent function `C`. -/
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

/-- The binary digits of a natural number, most significant first, encoded by nonblank tape
symbols and using at least one digit. -/
def natTapeBits (n : ℕ) : List (Option Bool) :=
  (List.range (Nat.log2 n + 1)).reverse.map fun i => some (n.testBit i)

/-- A rational tape encoding consisting of a numerator sign bit, the absolute numerator bits, a
blank separator, and denominator bits. -/
def ratTapeRecord (q : ℚ) : List (Option Bool) :=
  some (decide (q.num < 0)) :: natTapeBits q.num.natAbs ++ none :: natTapeBits q.den

/-- The tape encoding of rational polynomial coefficients, a degree parameter, and a rational
tolerance, with blank separators between the components. -/
def phaseTargetTape (p : List ℚ) (d : ℕ) (eps : ℚ) : List (Option Bool) :=
  (p.map ratTapeRecord).flatten ++ [none] ++ ratTapeRecord (d : ℚ) ++ [none] ++
    ratTapeRecord eps

/-- The existence of a polynomial-time bit machine producing unit-modulus rational phase data
for each bounded rational polynomial with the prescribed degree and parity. The data must
satisfy both the rational score threshold and the uniform real-response error bound on `[-1,
1]`. -/
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

/-- The condition that coefficient perturbations bounded by a nonnegative rational `δ` change
the phase score by at most `(d + 1) * δ`. -/
def phaseScoreStability : Prop :=
  ∀ (p q : List ℚ) (d : ℕ) (data : PhaseData) (δ : ℚ),
    0 ≤ δ → (∀ i : ℕ, |p.getD i 0 - q.getD i 0| ≤ δ) →
      |(scoreData p d data).1.1 - (scoreData q d data).1.1| ≤ ((d + 1 : ℕ) : ℚ) * δ

/-- The integer obtained by rounding `x * 2 ^ r` downward. -/
noncomputable def dyadicCode (x : ℝ) (r : ℕ) : ℤ := Int.floor (x * (2 ^ r : ℝ))

/-- The real value represented by the dyadic code `c` at precision `r`, namely `c / 2 ^ r`. -/
noncomputable def dyadicDecode (c : ℤ) (r : ℕ) : ℝ := (c : ℝ) / (2 ^ r : ℝ)

/-- The bit-width expression `c.natAbs.size + r + 2` for a signed dyadic code and its precision. -/
def dyadicBitWidth (c : ℤ) (r : ℕ) : ℕ := c.natAbs.size + r + 2

/-- The condition that every real number has arbitrarily accurate floor-based dyadic
approximations with the stated precision and code-magnitude bounds. -/
def HasGeneralRealQuantization : Prop :=
  ∀ (x : ℝ) (eps : ℝ), 0 < eps →
    ∃ (r : ℕ) (c : ℤ),
      |x - dyadicDecode c r| ≤ eps ∧
        ((2 ^ r : ℝ) ≥ 1 / eps) ∧
        c = dyadicCode x r ∧
        ((c.natAbs : ℝ) ≤ (|x| + 1) * (2 ^ r : ℝ))

/-- The bit-cost expression `gs.length * (w + 1) * (r + 2)` for a local program of width `w` and
precision `r`. -/
def localProgramBitCost (w r : ℕ) (gs : List (LocalQFTGate w)) : ℕ :=
  gs.length * (w + 1) * (r + 2)

/-- The space expression `w + r` for register width `w` and precision `r`. -/
def localProgramSpaceBits (w r : ℕ) : ℕ := w + r

/-- The existence of dyadic approximations to every phase table and local programs approximating
the resulting diagonal matrices, each using half the error allowance. The contract also
requires the stated precision, bit-cost bound through a function `T`, and space expression. -/
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

/-- The oracle word consisting of `2 ^ j` forward-query steps. -/
def powerTwoOracleWord {H : Type} (j : ℕ) : List (AdjointStep H) :=
  List.replicate (2 ^ j) AdjointStep.forward

/-- The recursively defined matrix iterate starting at the identity and multiplying on the right
by `U` at each successor. -/
noncomputable def oraclePowerIterate {H : Type} [Fintype H] [DecidableEq H]
    (U : Matrix H H ℂ) : ℕ → Matrix H H ℂ
  | 0 => 1
  | n + 1 => oraclePowerIterate U n * U

/-- The proposition that every zero-query adjoint word evaluates identically for any two oracle
matrices. -/
def zeroQueryWordOracleIndependent : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] (word : List (AdjointStep H))
      (U V : Matrix H H ℂ),
    adjointQueryCount word = 0 → evaluate U word = evaluate V word

/-- The proposition that no zero-query word computes the conjugate transpose of every unitary
oracle on a nonempty finite register. -/
def zeroQueryAdjointImpossible : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] [Nonempty H],
    ¬ ∃ word : List (AdjointStep H),
      adjointQueryCount word = 0 ∧
        ∀ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ → evaluate U word = Uᴴ

/-- The proposition that no single fixed matrix equals the controlled version of every unitary
oracle on a nonempty finite register. -/
def zeroQueryControlledImpossible : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H] [Nonempty H],
    ¬ ∃ W : Matrix (Bool × H) (Bool × H) ℂ,
      ∀ U : Matrix H H ℂ, U ∈ Matrix.unitaryGroup H ℂ → W = controlOracle U

/-- The proposition that no sequence indexed by the natural numbers is surjective onto the real
numbers. -/
def noCountableRealCoverage : Prop :=
  ¬ ∃ e : ℕ → ℝ, Function.Surjective e

/-- The proposition that some real phase exponential is not represented by any Gaussian
rational. -/
def rationalBackendMissesRealPhase : Prop :=
  ¬ ∀ φ : ℝ, ∃ z : GaussianRat,
    gaussianRatComplex z = Complex.exp (2 * Real.pi * Complex.I * φ)

/-- The proposition that, at positive register width, every fixed local gate program differs
from some diagonal phase target. -/
def noFixedFiniteGatePhaseSynthesis : Prop :=
  ∀ (w : ℕ) (gs : List (LocalQFTGate w)) (_h : 0 < w),
    ∃ θ : Reg w → ℝ, localProgramMatrix gs ≠ encodedPhaseWord w θ

end Qatlib.Concepts.HspRecovery.ReductionCore
