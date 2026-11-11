/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.StopModel.StructuralProgram

/-!
# Variable-time algorithm specification

`VariableTimeAlgorithm` specifies a finite distribution of legal structural programs for a
supported growing variable-time computation. It requires a uniform weighted-time bound and a set
of records of mass at least nine tenths on which success is at least two fifths and the good
component preserves the original direction.

The variable-time amplification setting is described in [Ambainis2012].

## Main statements

* `VariableTimeAlgorithm`: probabilistic structural amplification with time and output
  guarantees.

## References

* [Ambainis, 2012][Ambainis2012]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Papers.VarTimeAmpAmp10.StopModel

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
set_option autoImplicit false
namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm

/-- The specification of legal structural amplification programs for supported growing
computations with no final running mass and the stated success floor. It requires the
displayed time bound and, with probability at least nine tenths, success at least two fifths
with preservation of the good component's direction. -/
def VariableTimeAlgorithm : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C]
    (stages : List (Matrix (VtSpace C) (VtSpace C) ℂ)) (history : ℕ → Finset C),
    GrowingVtLegal stages history → 1 ≤ stages.length →
    ∀ j₀ : VtSpace C,j₀.1=vtRunningFlag → GrowingVtSupported stages history j₀ →
    let Ψ:=vtState stages stages.length (Ket j₀)
    MeasureProb Ψ (runningSet C)=0 →
    1/(10^12*(stages.length : ℝ)^3) ≤ MeasureProb Ψ (goodSet C) →
    ∃ (Ω : Type) (_ : Fintype Ω) (law : Ω → ℝ) (good : Finset Ω)
      (W : Type) (_ : Fintype W) (_ : DecidableEq W) (w₀ : W)
      (prog : Ω → List (StructuralVtStep W C)),
      (∑ ω,law ω=1) ∧ (∀ ω,0 ≤ law ω) ∧
      (∀ ω,StructuralWordLegal stages (prog ω)) ∧
      (∀ ω,(structuralWordTime (prog ω) : ℝ) ≤
        4000000*(stages.length : ℝ)*Real.sqrt (stages.length : ℝ)*
          (vtTmax stages+reachedTav stages history j₀/Real.sqrt (MeasureProb Ψ (goodSet C)))) ∧
      (1-1/10 ≤ ∑ ω∈good,law ω) ∧
      (∀ ω∈good,
        let out:=Run 1 (compileStructuralWord stages history j₀ (prog ω)) (Ket (w₀,(false,j₀)))
        2/5 ≤ MeasureProb out (Finset.univ.filter (fun p : VtReg W C=>p.2.2.1=vtGoodFlag)) ∧
        MeasureProb out (Finset.univ.filter (fun p : VtReg W C=>p.2.2.1=vtRunningFlag)) ≤ 3/5 ∧
        ∃ c : ℂ,Collapse out (Finset.univ.filter (fun p : VtReg W C=>p.2.2.1=vtGoodFlag))=
          c • embedState w₀ (Collapse Ψ (goodSet C)))
end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm
