/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QmaCompleteness.HistoryHam.SpectralForrelation
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle

/-!
# Two-oracle circuits for witness sampling

This module defines the circuit syntax `TOStep` and `TOCircuit`, its execution `TORun`, and
separate query counts for two oracles. The forrelation register space `ForrSpace` supports
controlled phase and bit oracles, query-state masses, and the list of states preceding
first-oracle calls.

The transformation `hardcodeS` replaces first-oracle calls by fixed matrices, while
`witnessEmbed` initializes the remaining registers around a witness. These constructions use the
standard oracle-circuit framework of [NielsenChuang2010].

## Main statements

* `TORun`: execution with supplied first and second oracle matrices.
* `sQueryStates_length`: the number of recorded states equals the first-oracle query count.
* `hardcodeS`: replacement of first-oracle calls by fixed gates.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib

/-- A step of a two oracle circuit on basis type `I`, consisting of a fixed complex matrix gate,
a query to the first oracle, or a query to the second oracle. -/
inductive TOStep (I : Type) where
  | gate : Matrix I I ℂ → TOStep I
  | queryS : TOStep I
  | queryU : TOStep I

/-- A two oracle circuit on basis type `I`, represented as a list of `TOStep I` instructions. -/
abbrev TOCircuit (I : Type) := List (TOStep I)

/-- The condition that every fixed matrix gate appearing in `C` belongs to `Matrix.unitaryGroup
I ℂ`, imposing no condition on the separately supplied oracle matrices. -/
def IsUnitaryTOCircuit {I : Type} [Fintype I] [DecidableEq I] (C : TOCircuit I) : Prop :=
  ∀ U : Matrix I I ℂ, TOStep.gate U ∈ C → U ∈ Matrix.unitaryGroup I ℂ

/-- Executes a `TOCircuit` in list order on a state vector, applying each fixed gate and
substituting `oS` and `oU` for first and second oracle queries respectively. -/
noncomputable def TORun {I : Type} [Fintype I] [DecidableEq I] (oS oU : Matrix I I ℂ) :
    TOCircuit I → QState I → QState I
  | [], ψ => ψ
  | TOStep.gate U :: C, ψ => TORun oS oU C (ApplyGate U ψ)
  | TOStep.queryS :: C, ψ => TORun oS oU C (ApplyGate oS ψ)
  | TOStep.queryU :: C, ψ => TORun oS oU C (ApplyGate oU ψ)

/-- Counts occurrences of `TOStep.queryS` in a two oracle circuit, ignoring fixed gates and
second oracle queries. -/
def TOQueryCountS {I : Type} : TOCircuit I → ℕ
  | [] => 0
  | TOStep.gate _ :: C => TOQueryCountS C
  | TOStep.queryS :: C => TOQueryCountS C + 1
  | TOStep.queryU :: C => TOQueryCountS C

/-- Counts occurrences of `TOStep.queryU` in a two oracle circuit, ignoring fixed gates and
first oracle queries. -/
def TOQueryCountU {I : Type} : TOCircuit I → ℕ
  | [] => 0
  | TOStep.gate _ :: C => TOQueryCountU C
  | TOStep.queryS :: C => TOQueryCountU C
  | TOStep.queryU :: C => TOQueryCountU C + 1

/-- The basis type `(Reg n × Bool) × ((Reg n × Bool) × W)` comprising two address and control
pairs and a workspace basis `W`. -/
abbrev ForrSpace (n : ℕ) (W : Type) : Type := (Reg n × Bool) × ((Reg n × Bool) × W)

/-- The phase oracle on the first address and control pair, multiplying by negative one exactly
when its control and `S` at its address are true, tensored with the identity on the
remaining registers. -/
noncomputable def forrPhaseOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate (PhaseOracle fun p : Reg n × Bool => p.2 && S p.1) 1

/-- The phase oracle on the second address and control pair, multiplying by negative one exactly
when its control and `U` at its address are true, tensored with identities on the first pair
and workspace. -/
noncomputable def forrPhaseOracleU (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate 1 (TensorGate (PhaseOracle fun p : Reg n × Bool => p.2 && U p.1) 1)

/-- The bit oracle `BitOracleOn S` acting on the first address and control pair, tensored with
the identity on the second pair and workspace. -/
noncomputable def forrBitOracleS (n : ℕ) (S : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate (BitOracleOn S) 1

/-- The bit oracle `BitOracleOn U` acting on the second address and control pair, tensored with
identities on the first pair and workspace. -/
noncomputable def forrBitOracleU (n : ℕ) (U : Reg n → Bool) (W : Type)
    [Fintype W] [DecidableEq W] :
    Matrix (ForrSpace n W) (ForrSpace n W) ℂ :=
  TensorGate 1 (TensorGate (BitOracleOn U) 1)

/-- The measurement mass of basis states whose first control bit is true and whose first address
belongs to `S` but not to `Δ`. -/
noncomputable def controlFiberMass (n : ℕ) (S Δ : Reg n → Bool) (W : Type) [Fintype W]
    (φ : QState (ForrSpace n W)) : ℝ :=
  MeasureProb φ
    (Finset.univ.filter fun p : ForrSpace n W => p.1.2 = true ∧ S p.1.1 ∧ ¬Δ p.1.1)

/-- The measurement mass of all basis states whose first oracle address equals `x`, summing over
both control values and all remaining registers. -/
noncomputable def sQueryBornMass (n : ℕ) (W : Type) [Fintype W] (φ : QState (ForrSpace n W))
    (x : Reg n) : ℝ :=
  MeasureProb φ (Finset.univ.filter fun p : ForrSpace n W => p.1.1 = x)

/-- The Boolean membership predicate of the list `hist` of `n` bit strings, defined by `decide
(x ∈ hist)`. -/
def regOfList (n : ℕ) (hist : List (Reg n)) : Reg n → Bool := fun x => decide (x ∈ hist)

/-- The list, in execution order, of state vectors immediately before each `TOStep.queryS`
instruction, obtained by executing fixed gates and the supplied oracle matrices. -/
noncomputable def sQueryStates {I : Type} [Fintype I] [DecidableEq I] (oS oU : Matrix I I ℂ) :
    TOCircuit I → QState I → List (QState I)
  | [], _ψ => []
  | TOStep.gate U :: C, ψ => sQueryStates oS oU C (ApplyGate U ψ)
  | TOStep.queryS :: C, ψ => ψ :: sQueryStates oS oU C (ApplyGate oS ψ)
  | TOStep.queryU :: C, ψ => sQueryStates oS oU C (ApplyGate oU ψ)

/-- Replaces every `TOStep.queryS` in a circuit by the fixed matrix gate `oΔ`, retaining all
original fixed gates and second oracle queries in order. -/
def hardcodeS {I : Type} (oΔ : Matrix I I ℂ) : TOCircuit I → TOCircuit I
  | [] => []
  | TOStep.gate U :: C => TOStep.gate U :: hardcodeS oΔ C
  | TOStep.queryS :: C => TOStep.gate oΔ :: hardcodeS oΔ C
  | TOStep.queryU :: C => TOStep.queryU :: hardcodeS oΔ C

end Qatlib.Concepts.QmaCompleteness.WitnessSampler

open Qatlib
namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

/-- Embeds `ψ` into workspace `Reg n × Bool` of `ForrSpace` with both oracle address and control
pairs fixed to `(ZeroStr n, false)` and the workspace Boolean fixed to false. -/
noncomputable def witnessEmbed (n : ℕ) (ψ : QState (Reg n)) :
    QState (ForrSpace n (Reg n × Bool)) :=
  fun p =>
    if p.1 = (ZeroStr n, false) ∧ p.2.1 = (ZeroStr n, false) ∧ p.2.2.2 = false then
      ψ p.2.2.1
    else
      0
end Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

set_option autoImplicit false

open Matrix
namespace Qatlib.Concepts.QmaCompleteness.WitnessSampler.SeparatingQMAFromQCMAWithAClassicalOracle2025

/-- The number of states collected by `sQueryStates oS oU C ψ` equals the first oracle query
count `TOQueryCountS C`, independently of the matrices and initial vector. -/
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
