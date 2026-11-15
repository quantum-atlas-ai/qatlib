/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.Theorem62CumulativeSamplerStat

@[expose] public section
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.OracleSeparator

open Qatlib

noncomputable def classicalWitnessEmbed (n q : ℕ) (w : Fin q → Bool) :
    QState (ForrSpace n (Fin q → Bool)) :=
  Ket ((ZeroStr n, false), ((ZeroStr n, false), w))

def CumulativeSamplerProgram : Prop :=
  ∀ (n q t v : ℕ) (S U : Reg n → Bool)
    (C : TOCircuit (ForrSpace n (Fin q → Bool)))
    (E : Finset (ForrSpace n (Fin q → Bool))),
    IsUnitaryTOCircuit C →
    TOQueryCountS C ≤ t →
    TOQueryCountU C ≤ t →
    (∀ w : Fin q → Bool, Normalized (classicalWitnessEmbed n q w)) ∧
    ((∀ hist : List (Reg n), hist.Nodup → (∀ x ∈ hist, S x) → hist.length ≤ v →
        ∀ w' : Fin q → Bool,
          MeasureProb
            (TORun (forrPhaseOracleS n (regOfList n hist) (Fin q → Bool))
              (forrPhaseOracleU n U (Fin q → Bool)) C
              (classicalWitnessEmbed n q w')) E ≤
            1 / 3) →
      (∃ w₀ : Fin q → Bool,
        2 / 3 ≤ MeasureProb
          (TORun (forrPhaseOracleS n S (Fin q → Bool))
            (forrPhaseOracleU n U (Fin q → Bool)) C
            (classicalWitnessEmbed n q w₀)) E) →
      cumulativeSamplerSuccess n q (Fin q → Bool) S U C
          (fun w => classicalWitnessEmbed n q w) v ≥
        1 / (2 ^ q : ℝ) * (1 / (36 * (t : ℝ) ^ 2)) ^ v ∧
      ∀ hist : List (Reg n),
        TOQueryCountS
            (hardcodeS (forrPhaseOracleS n (regOfList n hist) (Fin q → Bool)) C) = 0 ∧
          TOQueryCountU
              (hardcodeS (forrPhaseOracleS n (regOfList n hist) (Fin q → Bool)) C) =
            TOQueryCountU C ∧
          TOQueryCountU
              (hardcodeS (forrPhaseOracleS n (regOfList n hist) (Fin q → Bool)) C) ≤ t)

end Qatlib.Papers.QMAvsQCMA25.OracleSeparator
