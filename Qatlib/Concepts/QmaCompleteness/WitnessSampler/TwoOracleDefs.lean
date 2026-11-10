/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

inductive TOStep (I : Type) where
  | gate : Matrix I I ℂ → TOStep I
  | queryS : TOStep I
  | queryU : TOStep I

abbrev TOCircuit (I : Type) := List (TOStep I)

def IsUnitaryTOCircuit {I : Type} [Fintype I] [DecidableEq I] (C : TOCircuit I) : Prop :=
  ∀ U : Matrix I I ℂ, TOStep.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ

noncomputable def TORun {I : Type} [Fintype I] [DecidableEq I] (oS oU : Matrix I I ℂ) :
    TOCircuit I → QState I → QState I
  | [], ψ => ψ
  | TOStep.gate U :: C, ψ => TORun oS oU C (ApplyGate U ψ)
  | TOStep.queryS :: C, ψ => TORun oS oU C (ApplyGate oS ψ)
  | TOStep.queryU :: C, ψ => TORun oS oU C (ApplyGate oU ψ)

def TOQueryCountS {I : Type} : TOCircuit I → ℕ
  | [] => 0
  | TOStep.gate _ :: C => TOQueryCountS C
  | TOStep.queryS :: C => TOQueryCountS C + 1
  | TOStep.queryU :: C => TOQueryCountS C

def TOQueryCountU {I : Type} : TOCircuit I → ℕ
  | [] => 0
  | TOStep.gate _ :: C => TOQueryCountU C
  | TOStep.queryS :: C => TOQueryCountU C
  | TOStep.queryU :: C => TOQueryCountU C + 1

abbrev ForrSpace (n : ℕ) (W : Type) : Type := (Reg n × Bool) × ((Reg n × Bool) × W)

noncomputable def forrPhaseOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate (PhaseOracle fun p : Reg n × Bool => p.2 && S p.1) 1

noncomputable def forrPhaseOracleU (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate 1 (TensorGate (PhaseOracle fun p : Reg n × Bool => p.2 && U p.1) 1)

noncomputable def forrBitOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate (BitOracleOn S) 1

noncomputable def forrBitOracleU (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate 1 (TensorGate (BitOracleOn U) 1)

noncomputable def controlFiberMass (n : ℕ) (S Δ : Reg n → Bool) (W : Type) [Fintype W]
    (φ : QState (ForrSpace n W)) : ℝ :=
  MeasureProb φ
    (Finset.univ.filter fun p : ForrSpace n W => p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1)

noncomputable def sQueryBornMass (n : ℕ) (W : Type) [Fintype W] (φ : QState (ForrSpace n W))
    (x : Reg n) : ℝ :=
  MeasureProb φ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 = x)

def regOfList (n : ℕ) (hist : List (Reg n)) : Reg n → Bool := fun x => decide (x ∈ hist)

noncomputable def sQueryStates {I : Type} [Fintype I] [DecidableEq I] (oS oU : Matrix I I ℂ) :
    TOCircuit I → QState I → List (QState I)
  | [], ψ => []
  | TOStep.gate U :: C, ψ => sQueryStates oS oU C (ApplyGate U ψ)
  | TOStep.queryS :: C, ψ => ψ :: sQueryStates oS oU C (ApplyGate oS ψ)
  | TOStep.queryU :: C, ψ => sQueryStates oS oU C (ApplyGate oU ψ)

def hardcodeS {I : Type} (oΔ : Matrix I I ℂ) : TOCircuit I → TOCircuit I
  | [] => []
  | TOStep.gate U :: C => TOStep.gate U :: hardcodeS oΔ C
  | TOStep.queryS :: C => TOStep.gate oΔ :: hardcodeS oΔ C
  | TOStep.queryU :: C => TOStep.queryU :: hardcodeS oΔ C

end Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib
namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

noncomputable def witnessEmbed (n : ℕ) (ψ : QState (Reg n)) :
    QState (ForrSpace n (Reg n × Bool)) :=
  fun p =>
    if p.1 = (ZeroStr n, false) ∧ p.2.1 = (ZeroStr n, false) ∧ p.2.2.2 = false then
      ψ p.2.2.1
    else
      0
end Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Matrix
namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

theorem sQueryStates_length {I : Type} [Fintype I] [DecidableEq I]
    (oS oU : Matrix I I ℂ) (C : TOCircuit I) (ψ : QState I) :
    (sQueryStates oS oU C ψ).length = TOQueryCountS C := by
  induction C generalizing ψ with
  | nil => rfl
  | cons s C ih =>
    cases s with
    | gate U' =>
      show (sQueryStates oS oU C (ApplyGate U' ψ)).length = TOQueryCountS C
      rw [ih (ApplyGate U' ψ)]
    | queryS =>
      show (ψ :: sQueryStates oS oU C (ApplyGate oS ψ)).length = TOQueryCountS C + 1
      rw [List.length_cons, ih (ApplyGate oS ψ)]
    | queryU =>
      show (sQueryStates oS oU C (ApplyGate oU ψ)).length = TOQueryCountS C
      rw [ih (ApplyGate oU ψ)]
end Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025
