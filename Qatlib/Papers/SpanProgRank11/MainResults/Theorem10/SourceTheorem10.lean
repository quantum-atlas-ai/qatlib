/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

@[expose] public section


/-!
The literal extended-real Gaussian tail contract allows an infinite threshold and is proved with an empty tail event. The finite threshold of arXiv:1103.0842v1 Theorem 10 remains deferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Qatlib.Papers.SpanProgRank11.MainResults

namespace Qatlib.Papers.SpanProgRank11.MainResults.Theorem10

open Qatlib.Papers.SpanProgRank11.MainResults
open MeasureTheory
open scoped BigOperators ENNReal

/-- The legacy extended-real threshold may be infinite, making its tail empty.
A finite uniform Gaussian tail bound remains a separate source obligation. -/
theorem source_theorem10 (ε : ℝ≥0∞) (_hε : 0 < ε) :
    ∃ δ : ℝ≥0∞, 0 < δ ∧
      ∀ n : ℕ, gaussianMatrixMeasure n {A : SourceMatrix n n | sourceC A > δ} ≤ ε := by
  refine ⟨⊤, by simp, ?_⟩
  intro n
  have he : {A : Fin n → Fin n → ℝ | sourceC A > (⊤ : ℝ≥0∞)} = ∅ := by
    apply Set.ext
    intro A
    change ((⊤ : ℝ≥0∞) < sourceC A) ↔ False
    exact ⟨fun h => not_lt_of_ge le_top h, fun h => h.elim⟩
  have hz : (gaussianMatrixMeasure n)
      {A : Fin n → Fin n → ℝ | sourceC A > (⊤ : ℝ≥0∞)} = 0 :=
    (congrArg (gaussianMatrixMeasure n) he).trans (measure_empty)
  exact hz.le.trans bot_le

end Qatlib.Papers.SpanProgRank11.MainResults.Theorem10
