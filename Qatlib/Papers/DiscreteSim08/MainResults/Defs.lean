/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels
import Qatlib.Concepts.ConversionCore.WitnessCompile.ContinuousProgram
import Qatlib.Concepts.ConversionCore.WitnessCompile.ConversionBridges
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Source program regularity and operation counts

`SourceDriverL1` requires an integrable scalar majorant for the norm of each continuous driver,
and `sourceContinuousCoherentQL1` restricts the continuous coherent-query infimum to such
programs. The module also proves error monotonicity for discrete coherent complexity and defines
the known-unitary operation count.

This development follows [CleveEtAl2009].

## Main statements

* `sourceContinuousCoherentQ_le_coherentQL1`: imposing driver regularity can only increase the
  infimum.
* `sourceCoherentQ_antitone`: larger error tolerance gives no larger coherent query complexity.
* `sourceKnownUnitaryCount`: the number of known-unitary entries in a source word.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- The condition that each continuous evolution driver has an integrable scalar majorant for
its operator norm almost everywhere on its time interval. -/
def SourceDriverL1 {S : Type} [Fintype S] [DecidableEq S]
    (C : List (SourceContinuousStep S)) : Prop :=
  ∀ s ∈ C, ∀ (K : ℝ → Matrix S S ℂ) (T : ℝ) (adj : Bool),
    s = SourceContinuousStep.evolve K T adj →
      ∃ g : ℝ → ℝ, MeasureTheory.IntegrableOn g (Set.Icc 0 T) ∧
        ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc 0 T)), ‖K t‖ ≤ g t

/-- The infimum of continuous query times over legal source programs with `SourceDriverL1` and
real clean-state overlap at least `sqrt (1 - ε)` on every input. -/
def sourceContinuousCoherentQL1 {X H : Type} [Fintype X] [DecidableEq X]
    [Fintype H] [DecidableEq H] {n q : ℕ}
    (input : X → Fin n → Fin (q + 1)) (ρ σ : X → QState H) (ε : ℝ) : ℝ≥0∞ :=
  sInf {b | ∃ (r : ℕ) (hr : 0 < r) (C : List (SourceContinuousStep (SourceSpace n q H r))),
    b = ENNReal.ofReal (sourceContinuousTime C) ∧ sourceContinuousLegal C ∧
    SourceDriverL1 C ∧
    ∀ x, (∑ p, star ((sourceContinuousMatrix (sourceLogOracle input x) C *ᵥ
        sourceClean n q r hr false (ρ x)) p) * sourceClean n q r hr true (σ x) p).re ≥
      Real.sqrt (1 - ε)}

/-- The unrestricted continuous coherent-query infimum is at most the infimum restricted by
`SourceDriverL1`. See [CleveEtAl2009]. -/
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

/-- Increasing the error parameter cannot increase discrete coherent query complexity. -/
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

/-- The number of known-unitary entries in a source word. -/
def sourceKnownUnitaryCount {S : Type} (C : SourceWord S) : ℕ :=
  C.countP (fun s => match s with | Sum.inl _ => true | Sum.inr _ => false)

/-- Prepending a known-unitary entry increases the known-unitary count by one. See
[CleveEtAl2009]. -/
theorem sourceKnownUnitaryCount_add_call {S : Type} (C : SourceWord S) (U : Matrix S S ℂ) :
    sourceKnownUnitaryCount (Sum.inl U :: C) = sourceKnownUnitaryCount C + 1 := by
  simp [sourceKnownUnitaryCount]

/-- Prepending an oracle query leaves the known-unitary count unchanged. See [CleveEtAl2009]. -/
theorem sourceKnownUnitaryCount_add_query {S : Type} (C : SourceWord S) (adj : Bool) :
    sourceKnownUnitaryCount (Sum.inr adj :: C) = sourceKnownUnitaryCount C := by
  simp [sourceKnownUnitaryCount]

end Qatlib.Papers.DiscreteSim08.MainResults
