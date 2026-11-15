/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.CompressedQuery.CompressOracle.CompressedOracle
public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

@[expose] public section
open Qatlib.Concepts.CompressedQuery.CompressOracle Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.CompressedQuery.CompressOracle

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation
open Qatlib.Concepts.QmaCompleteness.HistoryHam
open Qatlib
open Qatlib.Concepts.QmaCompleteness.WitnessSampler

def DatabaseRecordsCollision {I : Type} [Fintype I] (d : I → Bool) : Prop :=
  ∃ x y : I, x ≠ y ∧ (d x = true) ∧ (d y = true)

def DatabaseNewElement {I : Type} [Fintype I] (d : I → Bool) (x : I) : Prop :=
  d x = true

def CompressedXOREquivalence : Prop :=
  ∀ (I W : Type) [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W] (p : ℝ),
    0 ≤ p → p ≤ 1 →
    (∀ (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)),
        IsUnitaryCircuit C → Normalized ψ → Normalized (compressedRunState p C ψ)) ∧
    (∀ (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W)) (t : ℕ),
        QueryCount C ≤ t → ∀ (q : (I × Bool) × W) (d : I → Bool),
          t < databaseCard d → compressedRunState p C ψ (q, d) = 0) ∧
    (∀ (C : Circuit ((I × Bool) × W)), IsUnitaryCircuit C →
      ∀ (ψ : QState ((I × Bool) × W)), Normalized ψ → ∀ (i t : ℕ), QueryCount C ≤ t →
        (∑ q : (I × Bool) × W, ∑ d : I → Bool,
            (Nat.choose (databaseCard d) i : ℝ) * ‖compressedRunState p C ψ (q, d)‖ ^ 2)
          ≤ (Nat.choose t i : ℝ) * (2 * Real.sqrt (p * (1 - p))) ^ i) ∧
    (∀ (C : Circuit ((I × Bool) × W)) (ψ : QState ((I × Bool) × W))
        (q q' : (I × Bool) × W),
        (∑ d : I → Bool,
            compressedRunState p C ψ (q, d) * star (compressedRunState p C ψ (q', d)))
          = ∑ x : I → Bool, bernoulliPmf p x *
              Run (workspacePhaseOracle (I := I) (W := W) x) C ψ q *
              star (Run (workspacePhaseOracle (I := I) (W := W) x) C ψ q'))

def FockBasis (N t : ℕ) : Type := { v : Fin N → Fin (t + 1) // ∑ i, (v i : ℕ) = t }

noncomputable def bosonicCreation (N t : ℕ) (x : Fin N) :
    Matrix (FockBasis N (t + 1)) (FockBasis N t) ℂ :=
  Matrix.of fun w v =>
    if (∀ i : Fin N, (i : ℕ) ≠ (x : ℕ) → (w.1 i : ℕ) = (v.1 i : ℕ))
        ∧ ((w.1 x : ℕ) = (v.1 x : ℕ) + 1) then
      Complex.ofReal (Real.sqrt ((v.1 x : ℕ) + 1)) else 0

open Classical in

noncomputable def bosonicPhaseOracleBlock (N t : ℕ) (θ : ℝ) (x : Fin N) :
    Matrix (FockBasis N t) (FockBasis N t) ℂ :=
  Matrix.diagonal fun v : FockBasis N t =>
    Complex.exp (Complex.I * θ * (((v.1 x : ℕ) : ℂ)))

noncomputable def bosonicPhaseDeviation (θ : ℝ) (n : ℕ) : ℝ := 2 * |Real.sin (θ * n / 2)|

noncomputable def bosonicPerQueryNorm (θ : ℝ) : ℝ := 2 * |Real.sin θ|

noncomputable def bosonicMultiQueryBound (θ : ℝ) (t : ℕ) : ℝ := bosonicPerQueryNorm θ ^ t

def bosonicMultiQueryRecurrence (θ : ℝ) : Prop :=
  bosonicMultiQueryBound θ 0 = 1 ∧
    ∀ t : ℕ, bosonicMultiQueryBound θ (t + 1) =
      bosonicPerQueryNorm θ * bosonicMultiQueryBound θ t

def BosonicActionNormBound (N t : ℕ) (θ : ℝ) : Prop :=
  ∀ (x : Fin N) (v : FockBasis N t),
    ‖Complex.exp (Complex.I * θ * (((v.1 x : ℕ) : ℂ))) - 1‖
      = bosonicPhaseDeviation θ (v.1 x : ℕ)

def BosonicSamplingSuccessBound : Prop :=
  ∀ (I W : Type) [Fintype I] [Fintype W] [DecidableEq I] [DecidableEq W] (p : ℝ),
    0 ≤ p → p ≤ 1 →
    ∀ (t : ℕ) (C : Circuit ((I × Bool) × W)), QueryCount C ≤ t →
      IsUnitaryCircuit C →
        ∀ ψ : QState ((I × Bool) × W), Normalized ψ →
          (∑ q : (I × Bool) × W, ∑ d : I → Bool,
              if 2 ≤ databaseCard d then ‖compressedRunState p C ψ (q, d)‖ ^ 2 else 0)
            ≤ (Nat.choose t 2 : ℝ) * (2 * Real.sqrt (p * (1 - p))) ^ 2

noncomputable def qmaqcmaBaselineConstant : ℝ := 99 / 100

noncomputable def qmaqcmaNoThreshold : ℝ := 1 / 100

def MixedOutputQueryLowerBound : Prop :=
  ∀ (n W : ℕ) (S U : Reg n → Bool) (T : ℕ),
    spectralForrelation n S U ≤ qmaqcmaNoThreshold →
      ∀ C : TOCircuit (ForrSpace n (Fin W)),
        IsUnitaryTOCircuit C →
          TOQueryCountS C + TOQueryCountU C ≤ T →
            ∀ ψ : QState (ForrSpace n (Fin W)), Normalized ψ →
              ∀ acc : ForrSpace n (Fin W) → Bool,
                MeasureProb
                  (TORun (forrPhaseOracleS n S (Fin W)) (forrPhaseOracleU n U (Fin W)) C ψ)
                  (Finset.univ.filter (fun r => acc r)) ≤ qmaqcmaBaselineConstant

end Qatlib.Papers.QMAvsQCMA25.Forrelation
