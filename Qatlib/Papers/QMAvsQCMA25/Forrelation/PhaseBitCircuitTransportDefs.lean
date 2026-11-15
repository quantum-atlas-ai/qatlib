/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QmaCompleteness.WitnessSampler.TwoOracleDefs

@[expose] public section
open Qatlib.Concepts.QmaCompleteness.WitnessSampler Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025 Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.QueryWordCore.QueryMachinery

open Qatlib

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.QmaCompleteness.WitnessSampler

namespace Qatlib.Papers.QMAvsQCMA25.Forrelation

noncomputable def hadamardSControl (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate (TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) Hadamard) 1

noncomputable def hadamardUControl (n : ℕ) (W : Type) [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate 1 (TensorGate (TensorGate (1 : Matrix (Reg n) (Reg n) ℂ) Hadamard) 1)

def transportPhaseToBit {I : Type} (hS hU : Matrix I I ℂ) : TOCircuit I → TOCircuit I
  | [] => []
  | TOStep.gate G :: C => TOStep.gate G :: transportPhaseToBit hS hU C
  | TOStep.queryS :: C =>
      TOStep.gate hS :: TOStep.queryS :: TOStep.gate hS :: transportPhaseToBit hS hU C
  | TOStep.queryU :: C =>
      TOStep.gate hU :: TOStep.queryU :: TOStep.gate hU :: transportPhaseToBit hS hU C
end Qatlib.Papers.QMAvsQCMA25.Forrelation
