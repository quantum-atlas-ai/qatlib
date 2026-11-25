/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SparseMarkov16.MainResults.Model.SparseMarkovModel

@[expose] public section

/-!
# Diamond closeness as a finite diamond norm bound

Childs--Li, *Efficient simulation of sparse Markovian quantum dynamics*,
fixed arXiv:1611.05543v3 (9 Oct 2023), Definition 4, Eq. (26).

The paper states every simulation error as `‖Φ - Ψ‖_⋄ ≤ δ`, using the
reference-amplified trace norm of Definition 4. The model layer records the
same condition as `DiamondClose δ Φ Ψ`, a uniform bound over all finite
reference registers. The public library records the supremum form
`finiteDiamondNorm (F - G) ≤ ofReal δ`.

This module proves that the two are the same condition for complex-linear maps
`F G : Op N →ₗ[ℂ] Op N`. The only content is that the pointwise difference
`tensorImage F r X - tensorImage G r X` of the model layer is the amplified
image `tensorLeft (F - G) X` of the public definition, so the uniform bound
hypothesis of `finiteDiamondNorm_le_iff_uniform` applies verbatim. No second
diamond norm and no channel-theoretic estimate is introduced.
-/
set_option autoImplicit false

noncomputable section

open Matrix
open scoped ENNReal

namespace Qatlib.Papers.SparseMarkov16.MainResults.DiamondCloseness

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Papers.SparseMarkov16.MainResults.Model

/-- The reference-amplified image difference of the model layer is the amplified
image of the difference of the two linear maps. -/
theorem tensorImage_sub_eq_tensorLeft_sub {N : ℕ} (F G : Op N →ₗ[ℂ] Op N) (r : ℕ)
    (X : Matrix (Fin N × Fin r) (Fin N × Fin r) ℂ) :
    tensorImage (⇑F) r X - tensorImage (⇑G) r X = tensorLeft (F - G) X := by
  ext a b
  rfl

/-- The model-layer predicate `DiamondClose δ Φ Ψ` is equivalent to the public
finite diamond norm bound `finiteDiamondNorm (F - G) ≤ ofReal δ` for
complex-linear `F` and `G`, for every `δ ≥ 0`. -/
theorem diamondClose_iff_finiteDiamondNorm_le {N : ℕ} (F G : Op N →ₗ[ℂ] Op N) (δ : ℝ)
    (hδ : 0 ≤ δ) :
    DiamondClose δ (⇑F) (⇑G) ↔ finiteDiamondNorm (F - G) ≤ ENNReal.ofReal δ := by
  rw [finiteDiamondNorm_le_iff_uniform N N (F - G) δ hδ]
  simp only [DiamondClose]
  constructor
  · intro h r X
    simpa only [tensorImage_sub_eq_tensorLeft_sub] using h r X
  · intro h r X
    rw [tensorImage_sub_eq_tensorLeft_sub]
    exact h r X

end Qatlib.Papers.SparseMarkov16.MainResults.DiamondCloseness
