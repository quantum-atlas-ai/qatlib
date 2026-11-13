/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationDual
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationError
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.MatrixOptimizationSemantics

/-!
# Stopped sampling laws for dual vectors

`frontier1` relates the dual vector of a matrix family to the actual output distribution of a
stopped rejection sampler. It combines positive normalization, exact capped success and failure
probabilities, legality, and finite expected costs. The surrounding sampling-based
matrix-arithmetic setting is represented by [ChiaEtAl2022].

## Main statements

* `frontier1`: scaled dual-vector semantics and cost guarantees for stopped and capped samplers.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdversaryBounds.AdvDuality.HybridProgram
open Qatlib.Concepts.MpsAdaptation.MpsTransfer
open Qatlib.Concepts.MpsAdaptation.MpsTransfer.Family
open Qatlib.Concepts.LinearLearning.ConcisePipeline

namespace Qatlib.Concepts.DyadicOverlap.ArithLedger

open Qatlib
open scoped ENNReal Classical

/-- For positive `a` and nonnegative selector weights, the stopped output law represents the
dual vector up to a positive scale. Every capped program is legal with the stated exact
success and failure masses, and the stopped read cost and every natural-valued function of
its leaf counts have finite expectation. -/
theorem frontier1 {T D m : ℕ} (F : Family T D m) (j₀ : Fin m) (hT : 0 < T)
    (a : ℚ) (μ : Fin T → ℚ) (ha : 0 < a) (hμ : ∀ t, 0 ≤ μ t) :
    let w := intWeights (selectorMasses T a μ)
    let b := blockWidth w
    let F' := F.withOffset j₀
    let L := dualScale T (a : ℝ) (fun t => (μ t : ℝ))
    ∃ hW : 0 < weightTotal w,
      let p := (F'.stopped w b hW (blockWidth_capacity w)).map F'.value
      0 < L ∧ (∑ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i) = L ∧
      (∀ i, dualVector F j₀ (a : ℝ) (fun t => (μ t : ℝ)) i = L*(p i).toReal) ∧
      (∀ fuel, (F'.cappedProgram w b fuel).Legal ∧
        (∀ i, ((F'.capped w b fuel).map F'.cappedValue) (some i) =
          (1-rationalRejectMass w b ^ fuel)*p i) ∧
        ((F'.capped w b fuel).map F'.cappedValue) none = rationalRejectMass w b ^ fuel) ∧
      CostedLaw.expectation (F'.stopped w b hW (blockWidth_capacity w))
        (fun z => ((F'.counts b z).reads : ℝ≥0∞)) < ⊤ ∧
      (∀ g : HybridCounts → ℕ,
        CostedLaw.expectation (F'.stopped w b hW (blockWidth_capacity w))
          (fun z => (g ((F'.program z.1).leaf F'.oracle z.2.2).counts : ℝ≥0∞)) < ⊤) := by
  (try dsimp only)
  let w := intWeights (selectorMasses T a μ)
  have hW : 0 < weightTotal w := (intWeights_normalization _
    (selectorMasses_nonneg a μ ha.le hμ) (selectorMasses_pos hT a μ ha hμ)).1
  refine ⟨hW, ?_⟩
  have hd := dual_actual_output F j₀ hT a μ ha hμ
  dsimp only at hd
  refine ⟨hd.1, hd.2.1, hd.2.2, ?_, ?_, ?_⟩
  · intro fuel
    exact ⟨(F.withOffset j₀).cappedProgram_legal w (blockWidth w) fuel,
      (fun i => (F.withOffset j₀).capped_success_exact w (blockWidth w) fuel hW
        (blockWidth_capacity w) i),
      (F.withOffset j₀).capped_none w (blockWidth w) fuel (blockWidth_capacity w)⟩
  · exact (F.withOffset j₀).stopped_reads_finite w (blockWidth w) hW (blockWidth_capacity w)
  · exact fun g => (F.withOffset j₀).stopped_cost_finite w (blockWidth w) hW
      (blockWidth_capacity w) g

end Qatlib.Concepts.DyadicOverlap.ArithLedger
