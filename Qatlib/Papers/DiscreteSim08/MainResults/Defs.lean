/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.ConversionCore.WitnessCompile.ContinuousProgram
import Qatlib.Concepts.ConversionCore.WitnessCompile.ConversionBridges
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiscreteSim08.MainResults

def SourceDriverL1 {S : Type} [Fintype S] [DecidableEq S]
    (C : List (SourceContinuousStep S)) : Prop :=
  ∀ s ∈ C, ∀ (K : ℝ → Matrix S S ℂ) (T : ℝ) (adj : Bool),
    s = SourceContinuousStep.evolve K T adj →
      ∃ g : ℝ → ℝ, MeasureTheory.IntegrableOn g (Set.Icc 0 T) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), ‖K t‖ ≤ g t

def sourceContinuousCoherentQL1 {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r))),
    b = ENNReal.ofReal (sourceContinuousTime C) ∧ sourceContinuousLegal C ∧
    SourceDriverL1 C ∧
    ∀ x, (∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1 - ε)}

theorem sourceContinuousCoherentQ_le_coherentQL1 {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) (ε : ℝ) :
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceContinuousCoherentQ
        input ρ σ ε ≤
      sourceContinuousCoherentQL1 input ρ σ ε := by
  unfold Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceContinuousCoherentQ
    sourceContinuousCoherentQL1
  apply sInf_le_sInf
  rintro b ⟨r, hr, C, rfl, hlegal, hL1, hfid⟩
  exact ⟨r, hr, C, rfl, hlegal, hfid⟩

theorem sourceCoherentQ_antitone {X H : Type}
    [Fintype X] [DecidableEq X] [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) {ε ε' : ℝ}
    (hεε : ε ≤ ε') :
    Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceCoherentQ input ρ σ ε' ≤
      Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceCoherentQ input ρ σ ε := by
  unfold Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceCoherentQ
  apply sInf_le_sInf
  rintro b ⟨r, hr, C, rfl, hlegal, hfid⟩
  refine ⟨r, hr, C, rfl, hlegal, fun x => ?_⟩
  have hsqrt : Real.sqrt (1 - ε') ≤ Real.sqrt (1 - ε) := Real.sqrt_le_sqrt (by linarith)
  exact le_trans hsqrt (hfid x)

def sourceKnownUnitaryCount {S : Type} (C : SourceWord S) : ℕ :=
  C.countP (fun s => match s with | Sum.inl _ => true | Sum.inr _ => false)

theorem sourceKnownUnitaryCount_add_call {S : Type} (C : SourceWord S) (U : Matrix S S ℂ) :
    sourceKnownUnitaryCount (Sum.inl U :: C) = sourceKnownUnitaryCount C + 1 := by
  simp [sourceKnownUnitaryCount]

theorem sourceKnownUnitaryCount_add_query {S : Type} (C : SourceWord S) (adj : Bool) :
    sourceKnownUnitaryCount (Sum.inr adj :: C) = sourceKnownUnitaryCount C := by
  simp [sourceKnownUnitaryCount]

end Qatlib.Papers.DiscreteSim08.MainResults
