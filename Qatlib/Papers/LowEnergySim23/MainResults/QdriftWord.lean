/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.LowEnergySim23.MainResults.Framework.AlgorithmicModel

@[expose] public section

/-!
# Finite words for the sampled qDRIFT product

Algorithm 1 of arXiv:2312.08867v3 uses one exponential for each draw.
Expose the sampled word of the pinned qDRIFT product, with its length
and exact product semantics.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Papers.LowEnergySim23.MainResults.Framework

namespace Qatlib.Papers.LowEnergySim23.MainResults

/-- The factors of the pinned qDRIFT product in left-to-right product order. -/
def qdriftWord {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) (σ : Fin r → Fin Hd.L) :
    List (Op D) :=
  List.ofFn (fun j => qdriftFactor Hd t r (σ j))

/-- The emitted list contains exactly one factor per sample. -/
theorem qdriftWord_length {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) (σ : Fin r → Fin Hd.L) :
    (qdriftWord Hd t r σ).length = r :=
  List.length_ofFn

/-- Multiplying the emitted factors gives the pinned qDRIFT product. -/
theorem qdriftWord_prod {D : ℕ} (Hd : HamModel D) (t : ℝ) (r : ℕ) (σ : Fin r → Fin Hd.L) :
    (qdriftWord Hd t r σ).prod = qdriftProduct Hd t r σ := rfl

/-- The pinned term-norm weights sum to one whenever the total norm is positive. -/
theorem qdriftWeights_sum_one {D : ℕ} (Hd : HamModel D)
    (h : 0 < ∑ j, ‖Hd.terms j‖) :
    (∑ j, qdriftWeight Hd j) = 1 := by
  simp only [qdriftWeight, ← Finset.sum_div]
  exact div_self h.ne'

end Qatlib.Papers.LowEnergySim23.MainResults
